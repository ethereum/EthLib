module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Containers.Requests
public import EthLib.Consensus.Proofs.Signing
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits
public import EthLib.Consensus.Proofs.Transition.Totality.ProposerLookahead
public import EthLib.Consensus.Proofs.Transition.Totality.PtcWindow
public import EthLib.Consensus.Proofs.Transition.Upgrade

/-!
# Proofs: the upgrades of the beacon state succeed under bounds

The upgrade to Altair turns the pending attestations into flags and draws the sync committee.

It succeeds when those attestations read and the draw has its bounds and assumptions.

The upgrade to Electra starts the churns of exits and consolidations, and the queue of deposits.

It succeeds under bounds on the registry, the epoch and the deposit queue.

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

In each of these epochs the draws must end: an assumption, not a bound.

The bounds are those of the first lookahead, read on the Electra state. -/
theorem upgradeToFulu_ok {pre : BeaconState preset .pectra}
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
  obtain ⟨proposers, drawn⟩ := initializeProposerLookahead_ok
    (state := carryFields config .fusaka pre (by decide) (by decide))
    (by rw [epoch]; exact seedRoom) lookahead (by rw [epoch]; exact slotRoom)
    (fun offset le => by
      rw [epoch]
      exact ProposersDrawable.of_eq (state := pre) rfl rfl (by decide) (by decide)
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

In each of these epochs the draws must end: an assumption, not a bound.

An epoch must have at least one slot.

The pending deposits must also hold less than `2^64` Gwei.

The bounds of the draw are those of the first window, read on the Fulu state. -/
theorem upgradeToGloas_ok {pre : BeaconState preset .fusaka}
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
  obtain ⟨window, windowOk⟩ := initializePtcWindow_ok (state := upgradeFields config pre root)
    (by rw [epoch]; exact seedRoom) lookahead (by rw [epoch]; exact slotRoom) perEpoch
    (fun offset le => by
      rw [epoch]
      exact PtcDrawable.of_eq (state := pre) rfl rfl (by decide) (drawable offset le))
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

/-- Setting the earned flags of some attesters never fails when each attester is in range. -/
private theorem foldlM_addFlags_ok {fork : Fork} (flags : List UInt64) :
    ∀ (attesters : List ValidatorIndex) (participation : EpochParticipation preset fork),
      (∀ index ∈ attesters, index.toNat < participation.data.size) →
      ∃ out, attesters.foldlM (m := Except TransitionError) (init := participation)
        (fun participation index => do
          if inside : index.toNat < participation.data.size then
            let old := participation.data[index.toNat]
            return ⟨participation.data.set index.toNat (flags.foldl addFlag old) inside,
              fun before => by simpa using participation.bound before⟩
          else throw (.accessor (.indexOutOfRange index))) = .ok out
  | [], participation, _ => ⟨participation, rfl⟩
  | index :: rest, participation, inside => by
    have here := inside index List.mem_cons_self
    obtain ⟨out, folded⟩ := foldlM_addFlags_ok flags rest
      ⟨participation.data.set index.toNat (flags.foldl addFlag participation.data[index.toNat])
        here, fun before => by simpa using participation.bound before⟩
      (fun other member => by simpa using inside other (List.mem_cons_of_mem _ member))
    refine ⟨out, ?_⟩
    simp only [List.foldlM_cons, here, ↓reduceDIte, pure, Except.pure, bind, Except.bind]
    exact folded

/-- One pending attestation translates when its flags and attesters read, each attester in range. -/
private theorem translateAttestation_exists_ok {state : BeaconState preset .altair}
    {attestation : PendingAttestation preset} {flags : List UInt64}
    {attesters : List ValidatorIndex}
    (flagsOk : getAttestationParticipationFlagIndices state attestation.data
      attestation.inclusionDelay state.latestBlockHeader.slot = .ok flags)
    (attestersOk : getPendingAttestingIndices state attestation = .ok attesters)
    (inside : ∀ index ∈ attesters,
      index.toNat < (state.previousEpochParticipation (by decide)).data.size) :
    ∃ after, translateAttestation state (by decide) attestation = .ok after := by
  obtain ⟨out, folded⟩ := foldlM_addFlags_ok flags attesters _ inside
  rw [translateAttestation]
  simp only [liftAccessor, flagsOk, attestersOk, Except.mapError, bind, Except.bind]
  rw [folded]
  exact ⟨_, rfl⟩

/-- In Phase 0, each attester of a pending attestation is in the registry.

It is a member of a committee, so an active validator. -/
private theorem getPendingAttestingIndices_lt {pre : BeaconState preset .phase0}
    {attestation : PendingAttestation preset} {attesters : List ValidatorIndex}
    (ok : getPendingAttestingIndices pre attestation = .ok attesters) :
    ∀ index ∈ attesters, index.toNat < pre.validators.data.size := by
  intro index member
  simp only [getPendingAttestingIndices, bind, Except.bind] at ok
  split at ok
  · cases ok
  · rename_i committee committeeOk
    have inCommittee := mem_of_committeeAttesters ok member
    have active := mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk inCommittee
    obtain ⟨_, read, -⟩ :=
      (mem_getActiveValidatorIndices (pre.validators.bound (by decide))).mp active
    exact (Array.getElem?_eq_some_iff.mp read).1

/-- The upgrade to Altair succeeds when the pending attestations read and the draw has its bounds.

Each pending attestation of the previous epoch must give its flags and its attesters.

That is an assumption on the pending attestations, not a bound.

The sync committee is drawn under the bounds of the draw, read on the state before the upgrade.

The draw also needs valid keys, and it must end.

Those are assumptions too. -/
theorem upgradeToAltair_exists_ok {pre : BeaconState preset .phase0}
    (epochRoom : (getCurrentEpoch pre).toNat + 1 + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat <
      2 ^ 64)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (members : preset.SYNC_COMMITTEE_SIZE ≠ 0)
    (drawable : SyncDrawable pre)
    (translated : ∀ attestation ∈ (pre.previousEpochAttestations (by decide)).data.toList,
      (∃ flags, getAttestationParticipationFlagIndices pre attestation.data
          attestation.inclusionDelay pre.latestBlockHeader.slot = .ok flags) ∧
        ∃ attesters, getPendingAttestingIndices pre attestation = .ok attesters) :
    ∃ post, upgradeToAltair config pre = .ok post := by
  let carried := carryFields config .altair pre (by decide) (by decide)
  -- Each translation keeps the carried state, up to the flags of the previous epoch.
  have walk : ∀ list : List (PendingAttestation preset),
      (∀ attestation ∈ list,
        attestation ∈ (pre.previousEpochAttestations (by decide)).data.toList) →
      ∀ participation : EpochParticipation preset .altair,
        participation.data.size = pre.validators.data.size →
        ∃ participation' : EpochParticipation preset .altair,
          list.foldlM (fun state attestation => translateAttestation state (by decide) attestation)
            { carried with previousEpochParticipation := fun _ => participation } =
            .ok { carried with previousEpochParticipation := fun _ => participation' } := by
    intro list
    induction list with
    | nil => exact fun _ participation _ => ⟨participation, rfl⟩
    | cons first rest more =>
      intro listed participation sized
      obtain ⟨⟨flags, flagsOk⟩, attesters, attestersOk⟩ :=
        translated first (listed first List.mem_cons_self)
      have inside := getPendingAttestingIndices_lt attestersOk
      obtain ⟨after, stepped⟩ := translateAttestation_exists_ok
        (state := { carried with previousEpochParticipation := fun _ => participation })
        flagsOk attestersOk (fun index member => sized ▸ inside index member)
      obtain ⟨participation', rfl, same⟩ := translateAttestation_spec stepped
      rw [List.foldlM_cons, stepped]
      exact more (fun attestation member => listed attestation (List.mem_cons_of_mem _ member))
        participation' (same.trans sized)
  obtain ⟨previous, -, -⟩ := carryFields_of_lt_altair (config := config) (post := .altair) pre
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨participation, folded⟩ := walk _ (fun _ member => member)
    (carried.previousEpochParticipation (by decide)) (by rw [previous, Array.size_replicate])
  obtain ⟨keys, few, ends⟩ := drawable
  obtain ⟨committee, drawn⟩ := getNextSyncCommittee_ok
    (state := { carried with previousEpochParticipation := fun _ => participation })
    epochRoom lookahead keys few (SyncDrawEnds.of_eq (state := pre) rfl rfl (by decide) ends)
    members
  have start : (pre.previousEpochAttestations (by decide)).data.toList.foldlM
      (fun state attestation => translateAttestation state (by decide) attestation)
        (carryFields config .altair pre (by decide) (by decide)) =
      .ok { carried with previousEpochParticipation := fun _ => participation } := folded
  rw [Array.foldlM_toList] at start
  simp only [upgradeToAltair, start, liftAccessor, drawn, Except.mapError, bind, Except.bind,
    pure, Except.pure]
  exact ⟨_, rfl⟩

/-- An append to a list with room gives the list with the item at its end. -/
private theorem appendWithinLimit_of_fits {fork switch : Fork} {α : Type} {limit : Nat}
    {list : Serialization.Ssz.ForkList switch fork α limit}
    (fits : fork < switch → list.data.size + 1 ≤ limit)
    (item : α) :
    appendWithinLimit list item =
      .ok ⟨list.data.push item, fun before => by simpa using fits before⟩ :=
  dite_eq_left_of_eq_true (eq_true fits)

/-- A validator in the registry waits as a pending deposit when the queue has room.

The queue grows by at most one deposit. -/
private theorem queuePreActivation_exists_ok {state : BeaconState preset .pectra}
    {index : ValidatorIndex} (matched : BalancesMatch state)
    (inside : index.toNat < state.validators.data.size)
    (room : (state.pendingDeposits (by decide)).data.size + 1 ≤
      preset.PENDING_DEPOSITS_LIMIT.toNat) :
    ∃ after, queuePreActivation state (by decide) index = .ok after ∧
      (after.pendingDeposits (by decide)).data.size ≤
        (state.pendingDeposits (by decide)).data.size + 1 := by
  have balanceInside : index.toNat < state.balances.data.size := matched ▸ inside
  have fits : Fork.pectra < .glamsterdam → (state.pendingDeposits (by decide)).data.size + 1 ≤
      preset.PENDING_DEPOSITS_LIMIT.toNat := fun _ => room
  have stillInside :
      index.toNat < (state.putBalance index.toNat balanceInside 0).validators.data.size := inside
  simp only [queuePreActivation, getValidator, getBalance, Array.getElem?_eq_getElem inside,
    Array.getElem?_eq_getElem balanceInside, appendWithinLimit_of_fits fits,
    BeaconState.setBalance, balanceInside, stillInside, BeaconState.setValidator, ↓reduceDIte,
    liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl, by simp⟩

/-- One position of the registry queues its excess balance, if any, when the queue has room.

Only a validator with compounding credentials has an excess to queue.

The queue grows by at most one deposit. -/
private theorem queueCompoundingExcess_exists_ok {state : BeaconState preset .pectra}
    {index : Nat} (matched : BalancesMatch state)
    (room : (state.pendingDeposits (by decide)).data.size + 1 ≤
      preset.PENDING_DEPOSITS_LIMIT.toNat) :
    ∃ after, queueCompoundingExcess state (by decide) index = .ok after ∧
      (after.pendingDeposits (by decide)).data.size ≤
        (state.pendingDeposits (by decide)).data.size + 1 := by
  unfold queueCompoundingExcess
  split
  · rename_i validator found
    split
    · have inside := (Array.getElem?_eq_some_iff.mp found).1
      have small : index < 2 ^ 64 := Nat.lt_of_lt_of_le inside
        (Nat.le_trans (state.validators.bound (by decide))
          (Nat.le_of_lt preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt))
      have converted : index.toUInt64.toNat = index := by
        simpa using Nat.mod_eq_of_lt small
      have balanceInside : index.toUInt64.toNat < state.balances.data.size := by
        rw [converted, matched]
        exact inside
      have validatorInside : index.toUInt64.toNat < state.validators.data.size := by
        rw [converted]
        exact inside
      have fits : Fork.pectra < .glamsterdam →
          (state.pendingDeposits (by decide)).data.size + 1 ≤
            preset.PENDING_DEPOSITS_LIMIT.toNat := fun _ => room
      simp only [queueExcessActiveBalance, getBalance, getValidator,
        Array.getElem?_eq_getElem balanceInside, Array.getElem?_eq_getElem validatorInside,
        appendWithinLimit_of_fits fits, BeaconState.setBalance, balanceInside, ↓reduceDIte,
        liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure]
      by_cases above : preset.MIN_ACTIVATION_BALANCE < state.balances.data[index.toUInt64.toNat]
      · simp only [above, ↓reduceIte]
        exact ⟨_, rfl, by simp⟩
      · simp only [above, ↓reduceIte]
        exact ⟨_, rfl, Nat.le_succ _⟩
    · exact ⟨_, rfl, Nat.le_succ _⟩
  · exact ⟨_, rfl, Nat.le_succ _⟩

/-- The queueing of some validators of the registry succeeds when the queue has room for all.

It keeps the registry size and one balance for each validator.

It adds at most one pending deposit for each validator queued. -/
private theorem foldlM_queuePreActivation_exists_ok :
    ∀ (indices : List ValidatorIndex) (state : BeaconState preset .pectra),
      BalancesMatch state → (∀ index ∈ indices, index.toNat < state.validators.data.size) →
      (state.pendingDeposits (by decide)).data.size + indices.length ≤
        preset.PENDING_DEPOSITS_LIMIT.toNat →
      ∃ after, indices.foldlM (fun state index => queuePreActivation state (by decide) index)
          state = .ok after ∧
        BalancesMatch after ∧ after.validators.data.size = state.validators.data.size ∧
        (after.pendingDeposits (by decide)).data.size ≤
          (state.pendingDeposits (by decide)).data.size + indices.length
  | [], state, matched, _, _ => ⟨state, rfl, matched, rfl, Nat.le_refl _⟩
  | index :: rest, state, matched, inside, room => by
    rw [List.length_cons] at room
    obtain ⟨middle, stepped, grown⟩ :=
      queuePreActivation_exists_ok matched (inside index List.mem_cons_self) (by omega)
    have sizes := (electraKept_queuePreActivation stepped).1
    have matched' : BalancesMatch middle := by
      unfold BalancesMatch
      rw [sizes.1, sizes.2]
      exact matched
    obtain ⟨after, folded, matchedAfter, sized, bounded⟩ :=
      foldlM_queuePreActivation_exists_ok rest middle matched'
        (fun other member => sizes.1 ▸ inside other (List.mem_cons_of_mem _ member)) (by omega)
    refine ⟨after, ?_, matchedAfter, sized.trans sizes.1, ?_⟩
    · simp only [List.foldlM_cons, stepped, bind, Except.bind]
      exact folded
    · rw [List.length_cons]
      omega

/-- The validators not yet active are positions of the registry, and number at most its size. -/
private theorem preActivationIndices_bounds {fork : Fork} (state : BeaconState preset fork)
    (small : state.validators.data.size < 2 ^ 64) :
    (preActivationIndices state).length ≤ state.validators.data.size ∧
      ∀ index ∈ preActivationIndices state, index.toNat < state.validators.data.size := by
  unfold preActivationIndices
  dsimp only
  constructor
  · rw [List.length_map, List.length_mergeSort]
    exact (List.length_filter_le _ _).trans (by simp)
  · intro index member
    obtain ⟨entry, sorted, rfl⟩ := List.mem_map.mp member
    have inside := List.snd_lt_of_mem_zipIdx
      (List.mem_of_mem_filter ((List.mergeSort_perm _ _).subset sorted))
    simp only [Array.length_toList] at inside
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
    exact inside

/-- The queueing of the validators not yet active succeeds when the queue has room for the registry.

It keeps the registry size and one balance for each validator.

It adds at most one pending deposit for each validator. -/
private theorem queuePreActivations_exists_ok (state : BeaconState preset .pectra)
    (matched : BalancesMatch state) (small : state.validators.data.size < 2 ^ 64)
    (room : (state.pendingDeposits (by decide)).data.size + state.validators.data.size ≤
      preset.PENDING_DEPOSITS_LIMIT.toNat) :
    ∃ after, (preActivationIndices state).foldlM
        (fun state index => queuePreActivation state (by decide) index) state = .ok after ∧
      BalancesMatch after ∧ after.validators.data.size = state.validators.data.size ∧
      (after.pendingDeposits (by decide)).data.size ≤
        (state.pendingDeposits (by decide)).data.size + state.validators.data.size := by
  obtain ⟨count, inside⟩ := preActivationIndices_bounds state small
  obtain ⟨after, folded, matchedAfter, sized, bounded⟩ :=
    foldlM_queuePreActivation_exists_ok _ state matched inside (by omega)
  exact ⟨after, folded, matchedAfter, sized, by omega⟩

/-- The queueing of the excess balances succeeds when the queue has room for one per position. -/
private theorem foldlM_queueCompoundingExcess_exists_ok :
    ∀ (indices : List Nat) (state : BeaconState preset .pectra), BalancesMatch state →
      (state.pendingDeposits (by decide)).data.size + indices.length ≤
        preset.PENDING_DEPOSITS_LIMIT.toNat →
      ∃ after, indices.foldlM (fun state index => queueCompoundingExcess state (by decide) index)
          state = .ok after
  | [], state, _, _ => ⟨state, rfl⟩
  | index :: rest, state, matched, room => by
    rw [List.length_cons] at room
    obtain ⟨middle, stepped, grown⟩ :=
      queueCompoundingExcess_exists_ok (index := index) matched (by omega)
    have sizes := (electraKept_queueCompoundingExcess stepped).1
    have matched' : BalancesMatch middle := by
      unfold BalancesMatch
      rw [sizes.1, sizes.2]
      exact matched
    obtain ⟨after, folded⟩ := foldlM_queueCompoundingExcess_exists_ok rest middle matched'
      (by omega)
    refine ⟨after, ?_⟩
    simp only [List.foldlM_cons, stepped, bind, Except.bind]
    exact folded

/-- A step and its continuation succeed when the step succeeds and the continuation after it. -/
private theorem bind_exists_ok {ε α β : Type} {x : Except ε α} {g : α → Except ε β} {a : α}
    (first : x = .ok a) (rest : ∃ b, g a = .ok b) : ∃ b, x >>= g = .ok b := by
  rw [first]
  exact rest

/-- A step and its continuation succeed when the step succeeds with a property.

The continuation must succeed on each value with that property. -/
private theorem bind_exists_ok_of {ε α β : Type} {x : Except ε α} {g : α → Except ε β}
    {P : α → Prop} (first : ∃ a, x = .ok a ∧ P a) (rest : ∀ a, P a → ∃ b, g a = .ok b) :
    ∃ b, x >>= g = .ok b :=
  let ⟨_, ok, holds⟩ := first
  bind_exists_ok ok (rest _ holds)

/-- The latest finite exit epoch, from a finite start, stays below the far future epoch. -/
private theorem foldl_latestExit_lt (validators : List Validator) {start : Epoch}
    (finite : start.toNat < 2 ^ 64 - 1) :
    (validators.foldl (fun latest validator =>
      if validator.exitEpoch = FAR_FUTURE_EPOCH then latest else max latest validator.exitEpoch)
      start).toNat < 2 ^ 64 - 1 := by
  induction validators generalizing start with
  | nil => exact finite
  | cons validator rest more =>
    rw [List.foldl_cons]
    apply more
    split
    · exact finite
    · rename_i other
      have below : validator.exitEpoch.toNat < 2 ^ 64 - 1 := by
        have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        have ne : validator.exitEpoch.toNat ≠ FAR_FUTURE_EPOCH.toNat :=
          fun same => other (UInt64.toNat_inj.mp same)
        have := validator.exitEpoch.toNat_lt
        omega
      simp only [max]
      split <;> assumption

/-- The churns of exits and of consolidations are computed under bounds on the registry.

The registry is within its limit, and the effective balances sum below `2^64`. -/
private theorem churns_exists_ok {state : BeaconState preset .pectra}
    (within : state.RegistryWithinLimit) (summed : effectiveBalanceSum state < 2 ^ 64) :
    (∃ churn, getActivationExitChurnLimit config state = .ok churn) ∧
      ∃ churn, getConsolidationChurnLimit config state = .ok churn := by
  obtain ⟨total, totalOk, -⟩ := getTotalActiveBalance_exists_ok within summed
  refine ⟨?_, ?_⟩ <;>
    simp only [getActivationExitChurnLimit, getConsolidationChurnLimit, getBalanceChurnLimit,
      totalOk, show ¬Fork.glamsterdam ≤ Fork.pectra from by decide, ↓reduceIte, bind,
      Except.bind, pure, Except.pure] <;>
    exact ⟨_, rfl⟩

/-- The upgrade to Electra succeeds under bounds on the registry, the epoch and the deposit queue.

The registry must have one balance for each validator.

The effective balances must sum below `2^64`, for the churns.

The first epoch at which an exit can start, plus one, must be below `2^64`.

Each validator queues at most two pending deposits, so twice the registry must fit in that queue.

That bound is not tight, since a validator queued before activation has no excess left.

The end of the exit queue needs no bound: a finite exit epoch is below the far future epoch. -/
theorem upgradeToElectra_exists_ok {pre : BeaconState preset .dencun}
    (matched : BalancesMatch pre) (summed : effectiveBalanceSum pre < 2 ^ 64)
    (activationRoom : (getCurrentEpoch pre).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat + 1 <
      2 ^ 64)
    (queueRoom : 2 * pre.validators.data.size ≤ preset.PENDING_DEPOSITS_LIMIT.toNat) :
    ∃ post, upgradeToElectra config pre = .ok post := by
  have small : pre.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (pre.validators.bound (by decide)) (UInt64.toNat_lt _)
  have epochOne : (getCurrentEpoch pre).toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    change _ + 1 < _
    omega
  have epochLookahead : (getCurrentEpoch pre + 1).toNat + preset.MAX_SEED_LOOKAHEAD.toNat <
      2 ^ 64 := by
    rw [Uint64.toNat_add_of_lt epochOne]
    change _ + 1 + _ < _
    omega
  have activationOk : computeActivationExitEpoch preset (getCurrentEpoch pre) =
      .ok (getCurrentEpoch pre + 1 + preset.MAX_SEED_LOOKAHEAD) := by
    simp only [computeActivationExitEpoch, Uint64.addChecked_of_lt epochOne,
      Uint64.addChecked_of_lt epochLookahead, bind, Except.bind]
  have activationFinite :
      (getCurrentEpoch pre + 1 + preset.MAX_SEED_LOOKAHEAD).toNat < 2 ^ 64 - 1 := by
    rw [Uint64.toNat_add_of_lt epochLookahead, Uint64.toNat_add_of_lt epochOne]
    change _ + 1 + _ < _
    omega
  have latest := foldl_latestExit_lt pre.validators.data.toList activationFinite
  rw [Array.foldl_toList] at latest
  unfold upgradeToElectra
  refine bind_exists_ok (mapError_ok_iff.mpr (mapError_ok_iff.mpr activationOk)) ?_
  refine bind_exists_ok (mapError_ok_iff.mpr (mapError_ok_iff.mpr
    (Uint64.addChecked_of_lt (b := 1) (by change _ + 1 < _; omega)))) ?_
  dsimp only
  refine bind_exists_ok_of (P := fun _ => True) ?_ fun _ _ => ?_
  · refine ((churns_exists_ok (config := config) ?_ ?_).1).imp
      fun _ ok => ⟨mapError_ok_iff.mpr ok, trivial⟩
    · exact pre.validators.bound (by decide)
    · exact summed
  refine bind_exists_ok_of (P := fun _ => True) ?_ fun _ _ => ?_
  · refine ((churns_exists_ok (config := config) ?_ ?_).2).imp
      fun _ ok => ⟨mapError_ok_iff.mpr ok, trivial⟩
    · exact pre.validators.bound (by decide)
    · exact summed
  refine bind_exists_ok_of (queuePreActivations_exists_ok _ ?_ ?_ ?_)
    fun middle ⟨matchedMiddle, sized, pending⟩ => ?_
  · exact matched
  · exact small
  · show 0 + pre.validators.data.size ≤ _
    omega
  -- The carried queue is empty, so the first fold queues at most one deposit per validator.
  have queued : (middle.pendingDeposits (by decide)).data.size ≤
      0 + pre.validators.data.size := pending
  have kept : middle.validators.data.size = pre.validators.data.size := sized
  exact foldlM_queueCompoundingExcess_exists_ok _ middle matchedMiddle
    (by rw [List.length_range, kept]; omega)

end EthLib.Consensus
