module

public import EthLib.Consensus.Proofs.HonestBlockInput
public import EthLib.Consensus.Proofs.Transition.BlockLedger
public import EthLib.Consensus.Proofs.Transition.Totality.PendingDeposits

/-!
# Proofs: the deposit steps of a block accept the deposits that are due

Each deposit needs a Merkle proof to the deposit root, at the next deposit index.

It then adds a validator, raises a balance or waits in the pending deposits, with room for each.

The deposits keep the frame of a block and the flags of each validator already in the registry.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- The next deposit index plus the number of deposits that a block must carry fits in 64 bits.

The count is at most the deposits left in the deposit contract, and is zero from Fulu. -/
theorem expectedDepositCount_index_lt {state : BeaconState preset fork} {before : fork < .hegota}
    {count : Nat} (expected : expectedDepositCount state before = .ok count) :
    (state.eth1DepositIndex before).toNat + count < 2 ^ 64 := by
  have indexLt := (state.eth1DepositIndex before).toNat_lt
  have countLt := (state.eth1Data before).depositCount.toNat_lt
  unfold expectedDepositCount at expected
  split at expected
  · cases expected
    omega
  split at expected
  · rename_i electra
    cases expected
    split
    · -- The count is at most the deposits left below the limit, which is at most the count.
      rename_i below
      have belowNat := UInt64.lt_iff_toNat_lt.mp below
      have limitLe : (min (state.eth1Data before).depositCount
          (state.depositRequestsStartIndex ⟨electra, before⟩)).toNat ≤
            (state.eth1Data before).depositCount.toNat := by
        rw [Uint64.toNat_min]
        exact Nat.min_le_left _ _
      have takeLe : (min preset.MAX_DEPOSITS (min (state.eth1Data before).depositCount
          (state.depositRequestsStartIndex ⟨electra, before⟩) -
            state.eth1DepositIndex before)).toNat ≤
          (min (state.eth1Data before).depositCount
            (state.depositRequestsStartIndex ⟨electra, before⟩)).toNat -
              (state.eth1DepositIndex before).toNat := by
        rw [Uint64.toNat_min, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt below)]
        exact Nat.min_le_right _ _
      omega
    · omega
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, subChecked_ok_iff,
      pure, Except.pure, Except.ok.injEq] at expected
    obtain ⟨outstanding, ⟨le, taken⟩, rfl⟩ := expected
    rw [Uint64.toNat_min]
    have := Nat.min_le_right preset.MAX_DEPOSITS.toNat outstanding.toNat
    omega

/-- A sum of balances is at most the sum of each balance or effective balance, read in step.

The registry must be at least as long as the balances. -/
private theorem sum_le_sum_zipWith_max :
    ∀ (validators : List Validator) (balances : List UInt64),
      balances.length ≤ validators.length →
      (balances.map (·.toNat)).sum ≤ (validators.zipWith (fun validator balance =>
        max validator.effectiveBalance.toNat balance.toNat) balances).sum
  | _, [], _ => by simp
  | [], _ :: _, long => by simp at long
  | validator :: validators, balance :: balances, long => by
    have := sum_le_sum_zipWith_max validators balances (by simpa using long)
    have := Nat.le_max_right validator.effectiveBalance.toNat balance.toNat
    simp only [List.map_cons, List.sum_cons, List.zipWith_cons_cons]
    omega

/-- The balances sum to at most the stake sum, when there is one balance for each validator. -/
theorem balanceSum_le_stakeSum {state : BeaconState preset fork} (matched : BalancesMatch state) :
    balanceSum state ≤ stakeSum state := by
  unfold BalancesMatch at matched
  exact sum_le_sum_zipWith_max _ _ (by simp [matched])

/-! ## One deposit -/

/-- A deposit of a block passes, when its proof leads to the deposit root at the next index.

The next index plus one must fit in 64 bits.

The registry, and from Electra the pending deposits, must have room for one more entry.

Before Electra the sum of the balances plus the amount must be below `2^64`.

Each list of the registry must have one entry for each validator, and it keeps one.

The registry and the pending deposits grow by at most one.

Before Electra the balances grow by at most the amount. -/
theorem processDeposit_exists_ok (before : fork < .hegota) {state : BeaconState preset fork}
    {deposit : Deposit}
    (proven : ∃ leaf, hashTreeRoot deposit.data = .ok leaf ∧
      isValidMerkleBranch leaf deposit.proof.toList (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
        (state.eth1DepositIndex before).toNat (state.eth1Data before).depositRoot = true)
    (indexRoom : (state.eth1DepositIndex before).toNat + 1 < 2 ^ 64)
    (registryRoom : state.validators.data.size < preset.VALIDATOR_REGISTRY_LIMIT.toNat)
    (pendingRoom : ∀ electra : .pectra ≤ fork,
      (state.pendingDeposits electra).data.size < preset.PENDING_DEPOSITS_LIMIT.toNat)
    (funded : fork < .pectra → balanceSum state + deposit.data.amount.toNat < 2 ^ 64)
    (matched : BalancesMatch state) (sized : ParticipationMatches state)
    (scored : InactivityScoresMatch state) :
    ∃ after, processDeposit config checks before state deposit = .ok after ∧
      after.validators.data.size ≤ state.validators.data.size + 1 ∧
      (∀ electra : .pectra ≤ fork, (after.pendingDeposits electra).data.size ≤
        (state.pendingDeposits electra).data.size + 1) ∧
      (fork < .pectra → balanceSum after ≤ balanceSum state + deposit.data.amount.toNat) ∧
      ParticipationMatches after ∧ InactivityScoresMatch after := by
  obtain ⟨leaf, leafOk, valid⟩ := proven
  -- The next deposit index is one more, and fits in 64 bits.
  obtain ⟨next, named⟩ := Uint64.exists_toNat_eq indexRoom
  have nextOk : addChecked (state.eth1DepositIndex before) 1 = .ok next :=
    addChecked_ok_iff.mpr ⟨indexRoom, named⟩
  suffices applied : ∃ after, applyDeposit config checks
      { state with eth1DepositIndex := fun _ => next } deposit.data.pubkey
      deposit.data.withdrawalCredentials deposit.data.amount deposit.data.signature = .ok after ∧
      after.validators.data.size ≤ state.validators.data.size + 1 ∧
      (∀ electra : .pectra ≤ fork, (after.pendingDeposits electra).data.size ≤
        (state.pendingDeposits electra).data.size + 1) ∧
      (fork < .pectra → balanceSum after ≤ balanceSum state + deposit.data.amount.toNat) ∧
      ParticipationMatches after ∧ InactivityScoresMatch after by
    obtain ⟨after, appliedOk, facts⟩ := applied
    refine ⟨after, ?_, facts⟩
    simp only [processDeposit, liftSsz, leafOk, Except.mapError, valid, ensure, ↓reduceIte,
      liftAccessor, liftArith, nextOk, bind, Except.bind]
    exact appliedOk
  by_cases electra : .pectra ≤ fork
  · -- From Electra the deposit waits in the pending deposits, after a new key gets a validator.
    have notEarly : ¬ fork < .pectra := Nat.not_lt_of_le electra
    have appended : ∀ (middle : BeaconState preset fork),
        middle.pendingDeposits = state.pendingDeposits → ∀ deposit : PendingDeposit,
          ∃ after, addPendingDeposit middle electra deposit = .ok after ∧
            after.validators = middle.validators ∧
            (after.pendingDeposits electra).data.size =
              (state.pendingDeposits electra).data.size + 1 ∧
            (ParticipationMatches middle → ParticipationMatches after) ∧
            (InactivityScoresMatch middle → InactivityScoresMatch after) := by
      intro middle same deposit
      have room := pendingRoom electra
      rw [← same] at room
      obtain ⟨pending, pendingOk⟩ : ∃ pending,
          appendWithinLimit (middle.pendingDeposits electra) deposit = .ok pending := by
        unfold appendWithinLimit
        rw [dite_eq_left (fun _ => by omega)]
        exact ⟨_, rfl⟩
      refine ⟨{ middle with pendingDeposits := fun _ => pending }, ?_, rfl, ?_, id, id⟩
      · simp only [addPendingDeposit, pendingOk, bind, Except.bind, pure, Except.pure]
      · show pending.data.size = _
        rw [appendWithinLimit_data pendingOk, Array.size_push, same]
    obtain ⟨verdict, verdictOk⟩ := isValidDepositSignature_exists_ok config checks
      deposit.data.pubkey deposit.data.withdrawalCredentials deposit.data.amount
      deposit.data.signature
    rw [applyDeposit, dite_eq_left electra]
    unfold applyDepositElectra
    split
    · simp only [verdictOk, bind, Except.bind]
      cases verdict
      · -- A new key with an invalid signature changes nothing but the index.
        exact ⟨_, rfl, by simp, fun _ => by simp, fun early => absurd early notEarly, sized,
          scored⟩
      · -- A new key with a valid signature gets a validator with no balance.
        obtain ⟨added, addedOk⟩ := addValidatorToRegistry_exists_ok
          (state := { state with eth1DepositIndex := fun _ => next }) matched sized scored
          registryRoom deposit.data.pubkey deposit.data.withdrawalCredentials 0
        have pendingA : added.pendingDeposits = state.pendingDeposits := by
          unfold addValidatorToRegistry at addedOk
          split at addedOk
          · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure,
              Except.pure, Except.ok.injEq] at addedOk
            obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := addedOk
            rfl
          · split at addedOk
            · cases addedOk
              rfl
            · cases addedOk
        obtain ⟨after, pendingOk, validatorsA, pendingSize, sizedA, scoredA⟩ := appended added
          pendingA ⟨deposit.data.pubkey, deposit.data.withdrawalCredentials, deposit.data.amount,
            deposit.data.signature, GENESIS_SLOT⟩
        obtain ⟨sizedM, scoredM⟩ := addValidatorToRegistry_matches addedOk sized scored
        refine ⟨after, ?_, ?_, fun _ => by rw [pendingSize], fun early => absurd early notEarly,
          sizedA sizedM, scoredA scoredM⟩
        · simp only [↓reduceIte, addedOk, liftAccessor, pendingOk, Except.mapError]
        · rw [validatorsA, addValidatorToRegistry_validators_eq_push addedOk, Array.size_push]
    · -- A known key waits in the pending deposits.
      obtain ⟨after, pendingOk, validatorsA, pendingSize, sizedA, scoredA⟩ := appended
        { state with eth1DepositIndex := fun _ => next } rfl
        ⟨deposit.data.pubkey, deposit.data.withdrawalCredentials, deposit.data.amount,
          deposit.data.signature, GENESIS_SLOT⟩
      refine ⟨after, ?_, by rw [validatorsA]; exact Nat.le_succ _, fun _ => by rw [pendingSize],
        fun early => absurd early notEarly, sizedA sized, scoredA scored⟩
      simp only [liftAccessor, pendingOk, Except.mapError]
  · -- Before Electra the deposit applies at once.
    have early : fork < .pectra := Nat.lt_of_not_le electra
    obtain ⟨after, appliedOk⟩ := applyPendingDeposit_exists_ok config checks
      (state := { state with eth1DepositIndex := fun _ => next })
      ⟨deposit.data.pubkey, deposit.data.withdrawalCredentials, deposit.data.amount,
        deposit.data.signature, GENESIS_SLOT⟩ matched sized scored registryRoom (funded early)
    obtain ⟨sizedA, scoredA⟩ := applyPendingDeposit_matches appliedOk sized scored
    refine ⟨after, ?_, (applyPendingDeposit_validators_size_le_and_mem appliedOk).1,
      fun electra' => absurd electra' electra,
      fun _ => balanceSum_applyPendingDeposit_le appliedOk, sizedA, scoredA⟩
    simp only [applyDeposit, electra, ↓reduceDIte]
    exact appliedOk

/-! ## The deposits of a block -/

/-- The deposits of a block pass, when each has a proof to the deposit root at its index.

The index of a deposit is the next deposit index plus its position in the list.

The next deposit index plus the number of deposits must fit in 64 bits.

The registry, and from Electra the pending deposits, must have room for every deposit.

Before Electra the sum of the balances plus the amounts must be below `2^64`.

Each list of the registry must have one entry for each validator.

The registry grows by at most one entry for each deposit. -/
theorem foldlM_processDeposit_exists_ok (before : fork < .hegota) :
    ∀ {deposits : List Deposit} {state : BeaconState preset fork},
      (∀ (position : Nat) (inside : position < deposits.length), ∃ leaf,
        hashTreeRoot deposits[position].data = .ok leaf ∧
        isValidMerkleBranch leaf deposits[position].proof.toList
          (DEPOSIT_CONTRACT_TREE_DEPTH.toNat + 1)
          ((state.eth1DepositIndex before).toNat + position)
          (state.eth1Data before).depositRoot = true) →
      (state.eth1DepositIndex before).toNat + deposits.length < 2 ^ 64 →
      state.validators.data.size + deposits.length ≤ preset.VALIDATOR_REGISTRY_LIMIT.toNat →
      (∀ electra : .pectra ≤ fork, (state.pendingDeposits electra).data.size +
        deposits.length ≤ preset.PENDING_DEPOSITS_LIMIT.toNat) →
      (fork < .pectra →
        balanceSum state + (deposits.map (·.data.amount.toNat)).sum < 2 ^ 64) →
      BalancesMatch state → ParticipationMatches state → InactivityScoresMatch state →
      ∃ after, deposits.foldlM (processDeposit config checks before) state = .ok after ∧
        after.validators.data.size ≤ state.validators.data.size + deposits.length
  | [], state, _, _, _, _, _, _, _, _ => ⟨state, rfl, by simp⟩
  | deposit :: rest, state, proven, indexRoom, registryRoom, pendingRoom, funded, matched,
      sized, scored => by
    simp only [List.length_cons, List.map_cons, List.sum_cons] at *
    obtain ⟨middle, ok, grown, pended, raised, sizedM, scoredM⟩ :=
      processDeposit_exists_ok (config := config) (checks := checks) before
        (by simpa using proven 0 (by simp)) (by omega) (by omega)
        (fun electra => by have := pendingRoom electra; omega)
        (fun early => by have := funded early; omega) matched sized scored
    -- The next deposit index grows by one, and the deposit contract data stays.
    obtain ⟨-, indexM, _, _, applied⟩ := processDeposit_ok ok
    have dataM := (applyDeposit_eth1 applied).2
    obtain ⟨after, folded, size⟩ := foldlM_processDeposit_exists_ok before (deposits := rest)
      (state := middle)
      (fun position inside => by
        have := proven (position + 1) (by simp; omega)
        rw [indexM, dataM, Nat.add_assoc, Nat.add_comm 1 position]
        simpa using this)
      (by omega) (by omega) (fun electra => by
        have := pended electra
        have := pendingRoom electra
        omega)
      (fun early => by
        have := raised early
        have := funded early
        omega)
      (balancesMatch_processDeposit ok matched) sizedM scoredM
    refine ⟨after, ?_, by omega⟩
    rw [List.foldlM_cons, ok]
    exact folded

/-- The deposits of a block keep the frame of a block and the flags already in the registry. -/
theorem foldlM_processDeposit_kept {before : fork < .hegota} {deposits : List Deposit}
    {first after : BeaconState preset fork}
    (computed : deposits.foldlM (processDeposit config checks before) first = .ok after) :
    BlockFrame first after ∧ ParticipationKeptBelow first after :=
  foldlM_ok_invariant
    (fun now : BeaconState preset fork => BlockFrame first now ∧ ParticipationKeptBelow first now)
    (fun _ _ _ ⟨frame, below⟩ ok =>
      ⟨frame.trans (frame_processDeposit ok), below.trans (flagsBelow_deposit ok)
        frame.registryGrows⟩)
    ⟨BlockFrame.refl first, ParticipationKeptBelow.refl first⟩ computed

end EthLib.Consensus
