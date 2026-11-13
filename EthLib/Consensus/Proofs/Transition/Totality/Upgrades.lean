module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Containers.Requests
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
public import EthLib.Consensus.Proofs.Transition.Totality.ProposerLookahead
public import EthLib.Consensus.Proofs.Transition.Totality.PtcWindow
public import EthLib.Consensus.Proofs.Transition.Upgrade

/-!
# Proofs: the upgrades to Fulu and to Gloas succeed under bounds

The upgrade to Fulu computes the first lookahead of proposers, and fails only if that draw fails.

[EIP-7917] specifies that lookahead.

The upgrade to Gloas computes the first window of payload timeliness committees.

It then moves the pending deposits of builders to a new registry of builders.

[EIP-7732] specifies that onboarding at the fork, and [EIP-8282] keeps it.

The onboarding overflows no builder balance when the pending deposits hold under `2^64` Gwei.

The checks of the deposit signatures and the root of the empty requests never fail.

The bounds of each draw are stated on the state before the upgrade.

The upgrade keeps the registry, the mixes and the slot, so the draws read the same values.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#fork-transition
[EIP-7917]: https://eips.ethereum.org/EIPS/eip-7917#specification
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#fork-transition-onboarding
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The upgrade to Fulu succeeds when the first lookahead of proposers can be drawn.

It draws the proposers of the current epoch and of each epoch of the seed lookahead.

In each of these epochs one active validator is at the cap of the draw.

That is an assumption on the registry, not a bound.

The bounds are those of the first lookahead, read on the Electra state. -/
theorem upgradeToFulu_ok {pre : BeaconState preset .pectra}
    (fits : DrawFits preset .fusaka)
    (seedRoom : (getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : ((getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (drawable : ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
      ProposersDrawable pre (getCurrentEpoch pre + offset.toUInt64)) :
    ∃ post, upgradeToFulu config pre = .ok post := by
  have epoch : getCurrentEpoch (carryFields config .fusaka pre (by decide) (by decide)) =
      getCurrentEpoch pre := rfl
  have cap : drawCap preset .fusaka = drawCap preset .pectra := by
    simp only [drawCap, show Fork.pectra ≤ Fork.fusaka from by decide,
      show Fork.pectra ≤ Fork.pectra from by decide, ↓reduceIte]
  obtain ⟨proposers, drawn⟩ := initializeProposerLookahead_ok
    (state := carryFields config .fusaka pre (by decide) (by decide)) fits
    (by rw [epoch]; exact seedRoom) lookahead (by rw [epoch]; exact slotRoom)
    (fun offset le => by
      rw [epoch]
      exact ProposersDrawable.of_validators (state := pre) rfl cap (by decide)
        (drawable offset le))
  refine ⟨{ carryFields config .fusaka pre (by decide) (by decide) with
    proposerLookahead := fun _ => proposers }, ?_⟩
  simp only [upgradeToFulu, liftAccessor, drawn, Except.mapError, bind, Except.bind, pure,
    Except.pure]

/-- A short-circuit test over a list succeeds when the test of each element succeeds. -/
private theorem anyM_exists_ok {α ε : Type} {test : α → Except ε Bool}
    (total : ∀ x, ∃ b, test x = .ok b) : ∀ xs : List α, ∃ b, xs.anyM test = .ok b
  | [] => ⟨false, by rw [List.anyM_nil]; rfl⟩
  | x :: rest => by
    obtain ⟨b, tested⟩ := total x
    obtain ⟨c, restOk⟩ := anyM_exists_ok total rest
    cases b
    · exact ⟨c, by simp [List.anyM_cons, tested, restOk, bind, Except.bind]⟩
    · exact ⟨true, by simp [List.anyM_cons, tested, bind, Except.bind, pure, Except.pure]⟩

/-- The search of the queue for a pending validator with a key never fails. -/
private theorem isPendingValidator_total (pending : List PendingDeposit)
    (pubkey : Cryptography.Bls.BLSPubkey) :
    ∃ found, isPendingValidator config checks pending pubkey = .ok found := by
  unfold isPendingValidator
  refine anyM_exists_ok (fun deposit => ?_) pending
  split
  · exact isValidDepositSignature_exists_ok config checks _ _ _ _
  · exact ⟨false, rfl⟩

/-- The index for a new builder is at most the size of the registry. -/
private theorem getIndexForNewBuilder_le (state : BeaconState preset .glamsterdam) :
    getIndexForNewBuilder state (by decide) ≤ (state.builders (by decide)).data.size := by
  simp only [getIndexForNewBuilder, Option.getD]
  split
  · rename_i index found
    exact (Array.findIdx?_eq_some_iff_getElem.mp found).1.le
  · exact Nat.le_refl _

/-- Registering a builder succeeds while the registry holds fewer than `2^64` builders.

It adds at most one builder to the registry. -/
private theorem addBuilderToRegistry_ok {state : BeaconState preset .glamsterdam}
    {pubkey : Cryptography.Bls.BLSPubkey} {version : UInt8} {executionAddress : ExecutionAddress}
    {amount : Gwei} {slot : Slot} (few : (state.builders (by decide)).data.size < 2 ^ 64) :
    ∃ after, addBuilderToRegistry state (by decide) pubkey version executionAddress amount slot =
        .ok after ∧
      (after.builders (by decide)).data.size ≤ (state.builders (by decide)).data.size + 1 := by
  have converted :=
    Uint64.ofNatChecked_of_lt (Nat.lt_of_le_of_lt (getIndexForNewBuilder_le state) few)
  simp only [addBuilderToRegistry, liftAccessor, liftArith, converted, Except.mapError, bind,
    Except.bind]
  split
  · exact ⟨_, rfl, by simp [BeaconState.putBuilder]⟩
  · exact ⟨_, rfl, by simp⟩

/-- One pending deposit is onboarded without error under bounds.

The registry holds fewer than `2^64` builders, and the deposit fits beside the builder balances.

It adds at most one builder to the registry. -/
private theorem onboardDeposit_ok {validatorKeys : List Cryptography.Bls.BLSPubkey}
    {state : BeaconState preset .glamsterdam} {kept : Array PendingDeposit}
    {deposit : PendingDeposit} (few : (state.builders (by decide)).data.size < 2 ^ 64)
    (funded : builderBalanceSum state (by decide) + deposit.amount.toNat < 2 ^ 64) :
    ∃ after kept', onboardDeposit config checks validatorKeys (state, kept) deposit =
        .ok (after, kept') ∧
      (after.builders (by decide)).data.size ≤ (state.builders (by decide)).data.size + 1 := by
  dsimp only [onboardDeposit]
  split
  · exact ⟨_, _, rfl, by omega⟩
  split
  · rename_i index _
    have below : ((state.builders (by decide)).data[index]).balance.toNat ≤
        builderBalanceSum state (by decide) := by
      have := builderBalanceSum_putBuilder (state := state) (gloas := by decide)
        (builder := { (state.builders (by decide)).data[index] with balance := 0 }) index.isLt
      simp only [Fin.getElem_fin, UInt64.toNat_zero] at this ⊢
      omega
    rw [Uint64.ofNatChecked_of_lt (Nat.lt_trans index.isLt few),
      Uint64.addChecked_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right below _) funded)]
    simp only [liftAccessor, liftArith, Except.mapError, bind, Except.bind, pure, Except.pure]
    exact ⟨_, _, rfl, by simp [BeaconState.putBuilder]⟩
  split
  · exact ⟨_, _, rfl, by omega⟩
  obtain ⟨pending, pendingOk⟩ := isPendingValidator_total (config := config) (checks := checks)
    kept.toList deposit.pubkey
  obtain ⟨valid, validOk⟩ := isValidDepositSignature_exists_ok config checks
    deposit.pubkey deposit.withdrawalCredentials deposit.amount deposit.signature
  obtain ⟨added, addedOk, grown⟩ := addBuilderToRegistry_ok (pubkey := deposit.pubkey)
    (version := PAYLOAD_BUILDER_VERSION)
    (executionAddress := credentialAddress deposit.withdrawalCredentials)
    (amount := deposit.amount) (slot := deposit.slot) few
  cases pending <;> cases valid <;>
    simp only [pendingOk, validOk, addedOk, bind, Except.bind, pure, Except.pure,
      Bool.false_eq_true, ↓reduceIte] <;>
    exact ⟨_, _, rfl, by omega⟩

/-- A fold of the onboarding over some pending deposits succeeds under bounds.

The builders plus the deposits left number fewer than `2^64`.

The builder balances plus the amounts left stay below `2^64`. -/
private theorem foldlM_onboardDeposit_ok {validatorKeys : List Cryptography.Bls.BLSPubkey} :
    ∀ (deposits : List PendingDeposit) (state : BeaconState preset .glamsterdam)
      (kept : Array PendingDeposit),
      (state.builders (by decide)).data.size + deposits.length < 2 ^ 64 →
      builderBalanceSum state (by decide) + pendingAmount deposits < 2 ^ 64 →
      ∃ out, deposits.foldlM (onboardDeposit config checks validatorKeys) (state, kept) = .ok out
  | [], state, kept, _, _ => ⟨(state, kept), rfl⟩
  | deposit :: rest, state, kept, few, funded => by
    have amounts : pendingAmount (deposit :: rest) =
        deposit.amount.toNat + pendingAmount rest := by simp [pendingAmount]
    rw [List.length_cons] at few
    obtain ⟨after, kept', stepped, grown⟩ := onboardDeposit_ok (config := config)
      (checks := checks) (validatorKeys := validatorKeys) (state := state) (kept := kept)
      (deposit := deposit) (by omega) (by omega)
    have summed : builderBalanceSum after (by decide) ≤
        builderBalanceSum state (by decide) + deposit.amount.toNat := by
      rcases onboardDeposit_cases stepped with ⟨rfl, -⟩ | ⟨-, summed, -⟩ | ⟨rfl, -⟩ <;> omega
    obtain ⟨out, folded⟩ := foldlM_onboardDeposit_ok (validatorKeys := validatorKeys) rest after
      kept' (by omega) (by omega)
    exact ⟨out, by simp only [List.foldlM_cons, bind, Except.bind, stepped, folded]⟩

/-- The onboarding of the pending deposits at the fork to Gloas succeeds.

The registry of builders is empty before it.

The pending deposits number fewer than `2^64` and hold less than `2^64` Gwei.

So no builder balance overflows. -/
theorem onboardBuildersFromPendingDeposits_ok {state : BeaconState preset .glamsterdam}
    (empty : (state.builders (by decide)).data = #[])
    (fewDeposits : (state.pendingDeposits (by decide)).data.size < 2 ^ 64)
    (funded : pendingAmount (state.pendingDeposits (by decide)).data.toList < 2 ^ 64) :
    ∃ post, onboardBuildersFromPendingDeposits config checks state = .ok post := by
  obtain ⟨⟨folded, kept⟩, foldedOk⟩ := foldlM_onboardDeposit_ok (config := config)
    (checks := checks) (validatorKeys := (state.validators.data.map (·.pubkey)).toList)
    (state.pendingDeposits (by decide)).data.toList state #[]
    (by rw [empty, Array.size_empty, Array.length_toList, Nat.zero_add]; exact fewDeposits)
    (by
      simp only [builderBalanceSum, empty, Array.toList_empty, List.map_nil, List.sum_nil,
        Nat.zero_add]
      exact funded)
  rw [Array.foldlM_toList] at foldedOk
  dsimp only [onboardBuildersFromPendingDeposits]
  rw [foldedOk]
  exact ⟨_, rfl⟩

/-- The upgrade to Gloas succeeds when the first window of payload committees can be drawn.

It draws the committees of the current epoch and of each epoch of the seed lookahead.

In each slot of these epochs one member of the beacon committees is at the cap of the draw.

That is an assumption on the registry, not a bound.

An epoch must have at least one slot.

The pending deposits must also hold less than `2^64` Gwei.

The bounds of the draw are those of the first window, read on the Fulu state. -/
theorem upgradeToGloas_ok {pre : BeaconState preset .fusaka}
    (fits : DrawFits preset .glamsterdam)
    (seedRoom : (getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat +
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat < 2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (slotRoom : ((getCurrentEpoch pre).toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1) *
      preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    (perEpoch : preset.SLOTS_PER_EPOCH ≠ 0)
    (drawable : ∀ offset ≤ preset.MIN_SEED_LOOKAHEAD.toNat,
      PtcDrawable pre (getCurrentEpoch pre + offset.toUInt64))
    (funded : pendingAmount (pre.pendingDeposits (by decide)).data.toList < 2 ^ 64) :
    ∃ post, upgradeToGloas config checks pre = .ok post := by
  obtain ⟨root, rooted⟩ :=
    Serialization.Ssz.SszType.hashTreeRoot_total (ExecutionRequests.empty preset .glamsterdam)
  have epoch : getCurrentEpoch (upgradeFields config pre root) = getCurrentEpoch pre := rfl
  have cap : drawCap preset .glamsterdam = drawCap preset .fusaka := by
    simp only [drawCap, show Fork.pectra ≤ Fork.glamsterdam from by decide,
      show Fork.pectra ≤ Fork.fusaka from by decide, ↓reduceIte]
  obtain ⟨window, windowOk⟩ := initializePtcWindow_ok (state := upgradeFields config pre root)
    fits (by rw [epoch]; exact seedRoom) lookahead (by rw [epoch]; exact slotRoom) perEpoch
    (fun offset le => by
      rw [epoch]
      exact PtcDrawable.of_eq (state := pre) rfl rfl cap (drawable offset le))
  obtain ⟨post, onboarded⟩ := onboardBuildersFromPendingDeposits_ok (config := config)
    (checks := checks)
    (state := { upgradeFields config pre root with ptcWindow := fun _ => window }) rfl
    (Nat.lt_of_le_of_lt ((pre.pendingDeposits (by decide)).bound (by decide))
      preset.PENDING_DEPOSITS_LIMIT.toNat_lt)
    funded
  refine ⟨post, ?_⟩
  simp only [upgradeToGloas, liftSsz, liftAccessor, rooted, windowOk, Except.mapError, bind,
    Except.bind]
  exact onboarded

end EthLib.Consensus
