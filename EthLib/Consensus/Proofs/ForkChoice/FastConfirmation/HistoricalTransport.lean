module

import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.Basic
import EthLib.Consensus.Proofs.ForkChoice.HonestVotes
import EthLib.Consensus.Proofs.ForkChoice.HonestEquivocators
import EthLib.Consensus.Proofs.ForkChoice.BlockAgreement
import EthLib.Consensus.Proofs.ForkChoice.BlockRuns
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# Checked reads for historical-anchor transport

A receiver can read the weight of an older committee window in its own balance state.

The caller's successful read supplies the arithmetic at the first slot.

The receiver's longer committee window supplies the shorter window and its final-slot arithmetic.

Successful registry lookups and an active total then supply the checked balance read.
-/

namespace EthLib.Consensus

open Base Uint64 Models

variable {preset : Preset} {fork : Fork}

/-- Activity at any queried epoch requires a finite activation epoch. -/
private theorem finiteActivation {state : BeaconState preset fork} {epoch : Epoch}
    {position : Nat} (active : isActiveAt state epoch position = true) :
    ∃ validator, state.validators.data[position]? = some validator ∧
      validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨validator, found, active⟩ := isActiveAt_eq_true_iff.mp active
  refine ⟨validator, found, ?_⟩
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  intro far
  have below := UInt64.lt_iff_toNat_lt.mp active.2
  have above := UInt64.le_iff_toNat_le.mp active.1
  rw [far] at above
  have bound := validator.exitEpoch.toNat_lt
  change 18446744073709551615 ≤ epoch.toNat at above
  omega

/-- Entries beyond a historical registry boundary still await activation eligibility. -/
private def PendingTail (count : Nat) (epoch : Epoch) (state : BeaconState preset fork) : Prop :=
  ∀ index validator, count ≤ index → state.validators.data[index]? = some validator →
    epoch < validator.activationEligibilityEpoch ∧ validator.activationEpoch = FAR_FUTURE_EPOCH

/-- Equal registries preserve the pending suffix without any slot condition. -/
private theorem pendingTail_of_validators {state after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch} (same : after.validators.data = state.validators.data)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  intro index validator lower found
  exact tail index validator lower (same ▸ found)

/-- Replacing an entry preserves the suffix if it preserves the entry's pending condition. -/
private theorem pendingTail_setValidatorAt_of {state after : BeaconState preset fork}
    {position count : Nat} {epoch : Epoch} {old validator : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after)
    (kept : epoch < old.activationEligibilityEpoch → old.activationEpoch = FAR_FUTURE_EPOCH →
      epoch < validator.activationEligibilityEpoch ∧ validator.activationEpoch = FAR_FUTURE_EPOCH)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  intro index entry lower read
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set] at read
  split at read
  · rename_i same
    subst index
    cases read
    obtain ⟨eligible, pending⟩ := tail position old lower
      (by rw [Array.getElem?_eq_getElem inside, oldEq])
    exact kept eligible pending
  · exact tail index entry lower read

/-- Replacing an entry with unchanged activation fields preserves the suffix. -/
private theorem pendingTail_setValidatorAt {state after : BeaconState preset fork}
    {position count : Nat} {epoch : Epoch} {old validator : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after)
    (eligibility : validator.activationEligibilityEpoch = old.activationEligibilityEpoch)
    (activation : validator.activationEpoch = old.activationEpoch)
    (tail : PendingTail count epoch state) : PendingTail count epoch after :=
  pendingTail_setValidatorAt_of found set
    (fun eligible pending => ⟨eligibility ▸ eligible, activation.trans pending⟩) tail

/-- Effective-balance updates cannot change pending activation eligibility or activation. -/
private theorem pendingTail_processEffectiveBalanceUpdates {state after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch}
    (run : processEffectiveBalanceUpdates state = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  apply foldlM_ok_invariant (PendingTail count epoch) (fun s i t before ok => ?_) tail run
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact pendingTail_setValidatorAt found set rfl rfl before

/-- Scheduling an exit preserves both activation fields of the pending suffix. -/
private theorem pendingTail_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    {count : Nat} {epoch : Epoch}
    (run : initiateValidatorExit config state index = .ok after)
    (tail : PendingTail count epoch state) : PendingTail count epoch after := by
  obtain ⟨validator, found, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok run
  · rw [unchanged.2]; exact tail
  · have same := (exitQueue_validators queue).1
    rw [setValidator_eq_setValidatorAt] at set
    have queuedFound : getValidatorAt queued index.toNat = .ok validator := by
      rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]
      exact found
    exact pendingTail_setValidatorAt queuedFound set rfl rfl
      (pendingTail_of_validators (congrArg (·.data) same) tail)

/-- Electra registry updates cannot activate entries beyond the finalized boundary. -/
private theorem pendingTail_updateRegistryEntryElectra {config : Config}
    {state after : BeaconState preset fork} {index count : Nat} {epoch activation : Epoch}
    (run : updateRegistryEntryElectra config activation state index = .ok after)
    (boundary : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at run
  obtain ⟨old, found, rest⟩ := run
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at rest
    obtain ⟨next, nextOk, set⟩ := rest
    apply pendingTail_setValidatorAt_of found set (fun _ pending => ?_) tail
    have sum := (addChecked_ok_iff.mp nextOk).2
    have bound := UInt64.le_iff_toNat_le.mp boundary
    change epoch < next ∧ old.activationEpoch = FAR_FUTURE_EPOCH
    norm_num only [UInt64.toNat_ofNat] at sum
    exact ⟨UInt64.lt_iff_toNat_lt.mpr (by omega), pending⟩
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok] at rest
    obtain ⟨_, _, exited⟩ := rest
    exact pendingTail_initiateValidatorExit exited tail
  split at rest
  · rename_i eligible
    apply pendingTail_setValidatorAt_of found (liftAccessor_ok.mp rest) (fun beyond _ => ?_) tail
    have lower : old.activationEligibilityEpoch ≤ state.finalizedCheckpoint.epoch := by
      simp only [isEligibleForActivation, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at eligible
      exact eligible.1
    exact False.elim (UInt64.not_lt.mpr (UInt64.le_trans lower finalized) beyond)
  · cases rest; exact tail

/-- The actual Electra registry fold preserves a tail beyond the finalized boundary. -/
private theorem pendingTail_processRegistryUpdatesElectra {config : Config}
    {state after : BeaconState preset fork} {count : Nat} {epoch : Epoch}
    (electra : .pectra ≤ fork) (run : processRegistryUpdates config state = .ok after)
    (boundary : epoch ≤ getCurrentEpoch state)
    (finalized : state.finalizedCheckpoint.epoch ≤ epoch) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  simp only [processRegistryUpdates, electra, ↓reduceIte, bind_ok_iff, liftAccessor_ok] at run
  obtain ⟨activation, _, folded⟩ := run
  have result := foldlM_ok_invariant
    (fun s => PendingTail count epoch s ∧ s.slot = state.slot ∧
      s.finalizedCheckpoint = state.finalizedCheckpoint)
    (fun s i t before ok => by
      have frame := frame_updateRegistryEntryElectra ok
      refine ⟨pendingTail_updateRegistryEntryElectra ok ?_ ?_ before.1,
        frame.slot.trans before.2.1, frame.finalized.trans before.2.2⟩
      · simpa only [getCurrentEpoch, before.2.1] using boundary
      · simpa only [before.2.2] using finalized)
    ⟨tail, rfl, rfl⟩ folded
  exact result.1

/-- A newly deposited validator is pending beyond every finite boundary epoch. -/
private theorem pendingTail_addValidator {state after : BeaconState preset fork}
    {count : Nat} {epoch : Epoch} {pubkey : Cryptography.Bls.BLSPubkey}
    {credentials : Bytes32} {amount : Gwei}
    (run : addValidatorToRegistry state pubkey credentials amount = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  have added := addValidatorToRegistry_validators_eq_push run
  intro index validator lower found
  rw [added, Array.getElem?_push] at found
  split at found
  · cases found
    exact ⟨finite, rfl⟩
  · exact tail index validator lower found

/-- A pending deposit cannot assign either activation epoch. -/
private theorem pendingTail_applyPendingDeposit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    {count : Nat} {epoch : Epoch}
    (run : applyPendingDeposit config checks state deposit = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  unfold applyPendingDeposit at run
  split at run
  · split at run
    · cases run; exact tail
    simp only [bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    split at run
    · exact pendingTail_addValidator run finite tail
    · cases run; exact tail
  · simp only [liftAccessor_ok, bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    exact pendingTail_of_validators (congrArg (·.data) (increaseBalance_validators run)) tail

/-- The existing pending-deposit pass transports the suffix through all applied deposits. -/
private theorem pendingTail_passPendingDeposits {config : Config} {checks : SignatureChecks}
    {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei}
    {deposits : List PendingDeposit} {state : BeaconState preset fork}
    {processed : Gwei} {count : Nat} {postponed : Array PendingDeposit} {pass}
    {boundary : Nat} {epoch : Epoch}
    (run : passPendingDeposits config checks stop nextEpoch available state processed count
      postponed deposits = .ok pass) (finite : epoch < FAR_FUTURE_EPOCH)
    (tail : PendingTail boundary epoch state) : PendingTail boundary epoch pass.1.state :=
  passPendingDeposits_of (fun s t => PendingTail boundary epoch s → PendingTail boundary epoch t)
    (fun _ holds => holds) (fun one two holds => two (one holds))
    (fun ok holds => pendingTail_applyPendingDeposit ok finite holds) run tail

/-- Processing an epoch's pending deposits preserves the pending suffix. -/
private theorem pendingTail_processPendingDeposits {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork}
    {count : Nat} {epoch : Epoch}
    (run : processPendingDeposits config checks state electra = .ok after)
    (finite : epoch < FAR_FUTURE_EPOCH) (tail : PendingTail count epoch state) :
    PendingTail count epoch after := by
  unfold processPendingDeposits at run
  simp only [bind, Except.bind, pure, Except.pure] at run
  repeat' (split at run <;> try cases run)
  all_goals
    exact pendingTail_of_validators rfl (pendingTail_passPendingDeposits ‹_› finite tail)

/-- An active entry cannot belong to the unassigned suffix, even for a future query epoch. -/
private theorem active_before_pendingTail {state : BeaconState preset fork}
    {epoch boundary : Epoch} {count position : Nat}
    (tail : PendingTail count boundary state)
    (active : isActiveAt state epoch position = true) : position < count := by
  obtain ⟨validator, found, finite⟩ := finiteActivation active
  by_contra outside
  exact finite (tail position validator (Nat.le_of_not_gt outside) found).2

/-- A registry containing the historical prefix contains every active queried position.

The prefix inclusion remains a separate input; default-false slashing flags do not supply it. -/
private theorem active_registry_of_pendingTail {state cached : BeaconState preset fork}
    {epoch boundary : Epoch} {count : Nat}
    (tail : PendingTail count boundary state) (contains : count ≤ cached.validators.data.size)
    {position : Nat} (active : isActiveAt state epoch position = true) :
    ∃ validator, cached.validators.data[position]? = some validator := by
  have inside := Nat.lt_of_lt_of_le (active_before_pendingTail tail active) contains
  exact ⟨cached.validators.data[position], Array.getElem?_eq_getElem inside⟩

/-- A successful total also bounds a subset, without bounding inactive balances. -/
private theorem totalBalance_exists_of_subset {state : BeaconState preset fork}
    {indices all : List ValidatorIndex} {total : Gwei}
    (read : getTotalBalance state all = .ok total)
    (subset : ∀ v ∈ indices, v ∈ all) :
    ∃ result, getTotalBalance state indices = .ok result := by
  obtain ⟨inside, bounded, -⟩ := getTotalBalance_ok_iff_stake.mp read
  have small : stake (fun v => balanceAt state v.toNat) indices.toFinset < 2 ^ 64 :=
    lt_of_le_of_lt (stake_mono fun v member =>
      List.mem_toFinset.mpr (subset v (List.mem_toFinset.mp member))) bounded
  let value := max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (stake (fun v => balanceAt state v.toNat) indices.toFinset)
  have fits : value < 2 ^ 64 := max_lt preset.EFFECTIVE_BALANCE_INCREMENT.toNat_lt small
  refine ⟨value.toUInt64, getTotalBalance_ok_iff_stake.mpr
    ⟨fun v member => inside v (subset v member), small, ?_⟩⟩
  exact UInt64.toNat_ofNat_of_lt' fits

/-- Registry lookups and a checked active total supply a checked filtered total. -/
private theorem filteredTotal_exists {state : BeaconState preset fork}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (read : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ active result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok active ∧ getTotalBalance state active = .ok result := by
  obtain ⟨active, filtered⟩ := filterM_exists_ok (test := fun index => do
    return isActiveValidator (← validatorAt state index) (getCurrentEpoch state))
    (list := participants.toList) (fun v member => by
      obtain ⟨validator, found⟩ := inside v (Std.TreeSet.mem_toList.mp member)
      exact ⟨isActiveValidator validator (getCurrentEpoch state), by simp [found]⟩)
  obtain ⟨result, resultOk⟩ := totalBalance_exists_of_subset
    (indices := active) (getTotalActiveBalance_ok read) (fun v member => by
      have passed := passes_of_mem_filterM_ok filtered member
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at passed
      obtain ⟨validator, found, isActive⟩ := passed
      exact mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨validator, validatorAt_ok_iff.mp found, isActive⟩))
  exact ⟨active, result, filtered, resultOk⟩

/-- Historical activity supplies checked receiver lookups through a pending-tail boundary.

The receiver filters at its own epoch; the epoch proving membership is unrestricted. -/
private theorem filteredTotal_of_pendingTail {source state : BeaconState preset fork}
    {epoch boundary : Epoch} {count : Nat} {participants : Std.TreeSet ValidatorIndex}
    {total : Gwei} (tail : PendingTail count boundary source)
    (contains : count ≤ state.validators.data.size)
    (active : ∀ v ∈ participants, isActiveAt source epoch v.toNat = true)
    (read : getTotalActiveBalance state = .ok total) :
    ∃ selected result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt state index) (getCurrentEpoch state)) =
        .ok selected ∧ getTotalBalance state selected = .ok result := by
  apply filteredTotal_exists read
  intro v member
  obtain ⟨validator, found⟩ := active_registry_of_pendingTail tail contains (active v member)
  exact ⟨validator, validatorAt_ok_iff.mpr found⟩

/-- A deposit pass followed by balance updates still gives checked historical reads. -/
private theorem filteredTotal_of_pendingDeposits_balances
    {config : Config} {checks : SignatureChecks}
    {source deposited after cached : BeaconState preset fork} {electra : .pectra ≤ fork}
    {epoch boundEpoch : Epoch} {count : Nat} {participants : Std.TreeSet ValidatorIndex}
    {total : Gwei} (deposits : processPendingDeposits config checks source electra = .ok deposited)
    (balances : processEffectiveBalanceUpdates deposited = .ok after)
    (finite : boundEpoch < FAR_FUTURE_EPOCH) (tail : PendingTail count boundEpoch source)
    (contains : count ≤ cached.validators.data.size)
    (active : ∀ v ∈ participants, isActiveAt after epoch v.toNat = true)
    (read : getTotalActiveBalance cached = .ok total) :
    ∃ selected result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt cached index) (getCurrentEpoch cached)) =
        .ok selected ∧ getTotalBalance cached selected = .ok result :=
  filteredTotal_of_pendingTail
    (pendingTail_processEffectiveBalanceUpdates balances
      (pendingTail_processPendingDeposits deposits finite tail)) contains active read

/-- The Electra registry stage retains the historical checked-read boundary. -/
private theorem filteredTotal_of_registryUpdates
    {config : Config}
    {source after cached : BeaconState preset fork} (electra : .pectra ≤ fork)
    {epoch boundEpoch : Epoch} {count : Nat}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (registry : processRegistryUpdates config source = .ok after)
    (boundary : boundEpoch ≤ getCurrentEpoch source)
    (finalized : source.finalizedCheckpoint.epoch ≤ boundEpoch)
    (tail : PendingTail count boundEpoch source)
    (contains : count ≤ cached.validators.data.size)
    (active : ∀ v ∈ participants, isActiveAt after epoch v.toNat = true)
    (read : getTotalActiveBalance cached = .ok total) :
    ∃ selected result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt cached index) (getCurrentEpoch cached)) =
        .ok selected ∧ getTotalBalance cached selected = .ok result :=
  filteredTotal_of_pendingTail
    (pendingTail_processRegistryUpdatesElectra electra registry boundary finalized tail)
    contains active read

/-- Lookahead extends a run without assuming a registry-size bound. -/
private theorem runKept_lookahead {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) : RunKept state after := by
  unfold lookaheadState at run
  split at run
  · exact runKept_processSlots (mapError_ok_iff.mp run)
  · cases run; exact .refl _

/-- An ancestor's registry prefix remains present in a descendant's cached state. -/
private theorem ancestor_registrySize_le_cached {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {node ancestor : ForkChoiceNode} {query target : Slot}
    {boundary base cached : BeaconState preset fork}
    (walk : store.getAncestor node query = .ok ancestor)
    (baseFound : store.blockStates[node.root]? = some base)
    (boundaryFound : store.blockStates[ancestor.root]? = some boundary)
    (advanced : lookaheadState config checks base target = .ok cached) :
    boundary.validators.data.size ≤ cached.validators.data.size :=
  Nat.le_trans (reachable.runKept_of_getAncestor anchorSlot walk baseFound boundaryFound).grows
    (runKept_lookahead advanced).grows

/-- A held ancestor supplies the prefix size for checked historical participant reads.

The pending-tail provenance is still required separately; no validator identity is inferred. -/
private theorem filteredTotal_of_ancestor_pendingTail {config : Config} {checks : SignatureChecks}
    {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
    {store : Store preset fork} (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (reachable : Store.Reachable config anchorState anchorBlock store)
    {node ancestor : ForkChoiceNode} {query target : Slot}
    {source boundary base cached : BeaconState preset fork} {epoch boundEpoch : Epoch}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei}
    (walk : store.getAncestor node query = .ok ancestor)
    (baseFound : store.blockStates[node.root]? = some base)
    (boundaryFound : store.blockStates[ancestor.root]? = some boundary)
    (advanced : lookaheadState config checks base target = .ok cached)
    (tail : PendingTail boundary.validators.data.size boundEpoch source)
    (active : ∀ v ∈ participants, isActiveAt source epoch v.toNat = true)
    (read : getTotalActiveBalance cached = .ok total) :
    ∃ selected result,
      participants.toList.filterM (fun index => do
        return isActiveValidator (← validatorAt cached index) (getCurrentEpoch cached)) =
        .ok selected ∧ getTotalBalance cached selected = .ok result :=
  filteredTotal_of_pendingTail tail
    (ancestor_registrySize_le_cached anchorSlot reachable walk baseFound boundaryFound advanced)
    active read

/-- The maximum succeeds when its arithmetic, committee, registry and total reads succeed. -/
private theorem maximum_exists_of_total {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last : Slot}
    {participants : Std.TreeSet ValidatorIndex} {total : Gwei} {covered : Bool}
    (coverage : isFullValidatorSetCovered preset first last = .ok covered)
    (windowOk : store.getCommitteesBetweenSlots head first last = .ok participants)
    (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ participants, ∃ validator, validatorAt state v = .ok validator) :
    ∃ maximum, store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum := by
  by_cases empty : last < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  cases covered
  · obtain ⟨active, result, filtered, resultOk⟩ := filteredTotal_exists totalOk inside
    simp only [bind, Except.bind, pure, Except.pure] at filtered
    exact ⟨result, by
      simp only [Store.computeCommitteeWeightBetweenSlots, Store.computeCommitteeWeightAndMembers,
        empty, ↓reduceIte, coverage, bind, Except.bind, Bool.false_eq_true, windowOk,
        filtered, resultOk, Except.mapError, pure, Except.pure]⟩
  · exact ⟨total, by
      rw [Store.computeCommitteeWeightBetweenSlots_of_covered coverage]
      rw [totalOk]; rfl⟩

/-- A successful committee window supplies every shorter window with the same first slot. -/
private theorem committeeWindow_prefix {store : Store preset fork} {head : Root}
    {first last shortLast : Slot} {members : Std.TreeSet ValidatorIndex}
    (read : store.getCommitteesBetweenSlots head first last = .ok members)
    (before : shortLast ≤ last) :
    ∃ short, store.getCommitteesBetweenSlots head first shortLast = .ok short ∧
      ∀ v ∈ short, v ∈ members := by
  have original := read
  unfold Store.getCommitteesBetweenSlots at read
  obtain ⟨afterLast, afterOk, folded⟩ := bind_ok_iff.mp read
  have afterNat := addChecked_ok_iff.mp (mapError_ok_iff.mp afterOk)
  have shorter : shortLast.toNat + (1 : UInt64).toNat < 2 ^ 64 := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have shortOk := addChecked_of_lt shorter
  have shortNat := (addChecked_ok_iff.mp shortOk).2
  have counts : (shortLast + 1).toNat - first.toNat ≤ afterLast.toNat - first.toNat := by
    have le := UInt64.le_iff_toNat_le.mp before
    omega
  have split : List.range (afterLast.toNat - first.toNat) =
      List.range ((shortLast + 1).toNat - first.toNat) ++
        (List.range (afterLast.toNat - first.toNat)).drop
          ((shortLast + 1).toNat - first.toNat) := by
    simpa only [List.take_range, Nat.min_eq_left counts] using
      (List.take_append_drop ((shortLast + 1).toNat - first.toNat)
        (List.range (afterLast.toNat - first.toNat))).symm
  rw [split, List.foldlM_append] at folded
  obtain ⟨short, prefixOk, _⟩ := bind_ok_iff.mp folded
  have shortRead : store.getCommitteesBetweenSlots head first shortLast = .ok short := by
    simpa only [Store.getCommitteesBetweenSlots, shortOk, Except.mapError,
      bind, Except.bind] using prefixOk
  exact ⟨short, shortRead, fun _ member =>
    Store.mem_getCommitteesBetweenSlots_of_le shortRead original before member⟩

/-- A nonempty maximum supplies first-slot arithmetic for another range with the same start. -/
private theorem coverage_exists_of_maximum {store : Store preset fork} {head : Root}
    {state : BeaconState preset fork} {first last otherLast afterOther : Slot} {maximum : Gwei}
    (nonempty : first ≤ last)
    (read : store.computeCommitteeWeightBetweenSlots head state first last = .ok maximum)
    (afterOk : addChecked otherLast 1 = .ok afterOther) :
    ∃ covered, isFullValidatorSetCovered preset first otherLast = .ok covered := by
  have notEmpty : ¬last < first := UInt64.not_lt.mpr nonempty
  simp only [Store.computeCommitteeWeightBetweenSlots, bind_ok_iff] at read
  obtain ⟨result, read, -⟩ := read
  simp only [Store.computeCommitteeWeightAndMembers, notEmpty, ↓reduceIte,
    bind_ok_iff] at read
  obtain ⟨covered, coverage, -⟩ := read
  simp only [isFullValidatorSetCovered, bind_ok_iff, mapError_ok_iff] at coverage
  obtain ⟨afterFirst, firstOk, lastFirst, lastFirstOk, _, _, -⟩ := coverage
  refine ⟨decide (computeEpochAtSlot preset lastFirst < computeEpochAtSlot preset afterOther), ?_⟩
  simp only [isFullValidatorSetCovered, firstOk, lastFirstOk, afterOk, Except.mapError,
    bind, Except.bind, pure, Except.pure]

/-- The receiver reads the old maximum from its own balance state.

The caller supplies range arithmetic, not balances or registry containment. -/
private theorem receiver_oldMaximum {caller receiver : Store preset fork}
    {head receiverHead : Root} {source state : BeaconState preset fork}
    {first oldLast last : Slot} {maximum total : Gwei}
    {window : Std.TreeSet ValidatorIndex}
    (read : caller.computeCommitteeWeightBetweenSlots head source first oldLast = .ok maximum)
    (windowOk : receiver.getCommitteesBetweenSlots receiverHead first last = .ok window)
    (before : oldLast ≤ last) (totalOk : getTotalActiveBalance state = .ok total)
    (inside : ∀ v ∈ window, ∃ validator, validatorAt state v = .ok validator) :
    ∃ result, receiver.computeCommitteeWeightBetweenSlots receiverHead state first oldLast =
      .ok result := by
  by_cases empty : oldLast < first
  · exact ⟨0, Store.computeCommitteeWeightBetweenSlots_of_gt empty⟩
  obtain ⟨members, membersOk, subset⟩ := committeeWindow_prefix windowOk before
  have afterRead := membersOk
  unfold Store.getCommitteesBetweenSlots at afterRead
  obtain ⟨afterOld, afterOk, _⟩ := bind_ok_iff.mp afterRead
  obtain ⟨covered, coverage⟩ := coverage_exists_of_maximum (UInt64.not_lt.mp empty) read
    (mapError_ok_iff.mp afterOk)
  exact maximum_exists_of_total coverage membersOk totalOk
    (fun v member => inside v (subset v member))

/-- Slot processing keeps slashing flags, including the default at an absent position. -/
private def SlashFlagsKept (state after : BeaconState preset fork) : Prop :=
  ∀ i : Nat, (after.validators.data[i]?.map (·.slashed)).getD false =
    (state.validators.data[i]?.map (·.slashed)).getD false

private theorem SlashFlagsKept.refl (state : BeaconState preset fork) :
    SlashFlagsKept state state := fun _ => rfl

private theorem SlashFlagsKept.trans {first second third : BeaconState preset fork}
    (one : SlashFlagsKept first second) (two : SlashFlagsKept second third) :
    SlashFlagsKept first third := fun i => (two i).trans (one i)

private theorem slashFlags_of_validators {state after : BeaconState preset fork}
    (same : after.validators.data = state.validators.data := by rfl) :
    SlashFlagsKept state after := by intro i; simp only [same]

private theorem slashFlags_of_map {state after : BeaconState preset fork}
    (same : after.validators.data.toList.map (·.slashed) =
      state.validators.data.toList.map (·.slashed)) : SlashFlagsKept state after := by
  intro i
  have atIndex := congrArg (fun xs => (xs[i]?).getD false) same
  simpa only [List.getElem?_map, Array.getElem?_toList] using atIndex

private theorem slashFlags_fold {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    {xs : List α} {state after : BeaconState preset fork}
    (keeps : ∀ s x t, step s x = .ok t → SlashFlagsKept s t)
    (ok : xs.foldlM step state = .ok after) : SlashFlagsKept state after :=
  foldlM_ok_invariant (SlashFlagsKept state)
    (fun _ _ _ before ok => before.trans (keeps _ _ _ ok)) (.refl state) ok

/-- Replacing one validator with the same flag keeps the flag map. -/
private theorem slashFlags_setValidatorAt {state after : BeaconState preset fork}
    {position : Nat} {validator old : Validator}
    (found : getValidatorAt state position = .ok old)
    (set : state.setValidatorAt position validator = .ok after) (same : validator.slashed =
      old.slashed) : SlashFlagsKept state after := by
  apply slashFlags_of_map
  obtain ⟨inside, rfl⟩ := setValidatorAt_ok set
  have oldEq : state.validators.data[position] = old := by
    simpa [getValidatorAt, inside] using found
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.toList_set, List.map_set]
  rw [same, ← oldEq]
  have atValue : (state.validators.data.toList.map (·.slashed))[position]'(by
      simpa using inside) = state.validators.data[position].slashed := by simp
  rw [← atValue]
  exact List.set_getElem_self _

/-- Exit scheduling changes neither existing slashing flags nor registry length. -/
private theorem slashFlags_initiateValidatorExit {config : Config}
    {state after : BeaconState preset fork} {index : ValidatorIndex}
    (run : initiateValidatorExit config state index = .ok after) :
    SlashFlagsKept state after := by
  obtain ⟨validator, found, unchanged | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok run
  · rw [unchanged.2]; exact .refl _
  · have same := (exitQueue_validators queue).1
    have kept := slashFlags_setValidatorAt
      (by rw [← getValidator_eq_getValidatorAt, getValidator_of_validators_eq same]; exact found)
      (by rwa [← setValidator_eq_setValidatorAt]) (by rfl)
    exact (slashFlags_of_validators (congrArg (·.data) same)).trans kept

/-- Registry updates schedule activity without changing slashing flags. -/
private theorem slashFlags_processRegistryUpdates {config : Config}
    {state after : BeaconState preset fork}
    (run : processRegistryUpdates config state = .ok after) : SlashFlagsKept state after := by
  have update {s t : BeaconState preset fork} {i : Nat}
      (ok : updateRegistryEntry config s i = .ok t) : SlashFlagsKept s t := by
    simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, queued, queue, marked, set, ok⟩ := ok
    have flag : queued.slashed = validator.slashed := by
      unfold queueForActivation at queue
      split at queue
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queue
        obtain ⟨_, _, rfl⟩ := queue
        rfl
      · cases queue; rfl
    have first := slashFlags_setValidatorAt found set flag
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact first.trans (slashFlags_initiateValidatorExit exited)
    · cases ok; exact first
  have activate {s t : BeaconState preset fork} {i : ValidatorIndex}
      (ok : activateValidator s i = .ok t) : SlashFlagsKept s t := by
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, _, _, set⟩ := ok
    rw [setValidator_eq_setValidatorAt] at set
    rw [getValidator_eq_getValidatorAt] at found
    exact slashFlags_setValidatorAt found set rfl
  have updateElectra {s t : BeaconState preset fork} {epoch : Epoch} {i : Nat}
      (ok : updateRegistryEntryElectra config epoch s i = .ok t) : SlashFlagsKept s t := by
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact slashFlags_setValidatorAt found set rfl
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, exited⟩ := ok
      exact slashFlags_initiateValidatorExit exited
    split at ok
    · exact slashFlags_setValidatorAt found (liftAccessor_ok.mp ok) rfl
    · cases ok; exact .refl _
  unfold processRegistryUpdates at run
  split at run
  · simp only [bind_ok_iff, liftAccessor_ok] at run
    obtain ⟨_, _, run⟩ := run
    exact slashFlags_fold (fun _ _ _ ok => updateElectra ok) run
  · simp only [bind_ok_iff] at run
    obtain ⟨_, updated, activated⟩ := run
    exact (slashFlags_fold (fun _ _ _ ok => update ok) updated).trans
      (slashFlags_fold (fun _ _ _ ok => activate ok) activated)

/-- A new validator has the same false flag as an absent registry position. -/
private theorem slashFlags_addValidator {state after : BeaconState preset fork}
    {pubkey : Cryptography.Bls.BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (run : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    SlashFlagsKept state after := by
  have added := addValidatorToRegistry_validators_eq_push run
  intro i
  rw [added]
  by_cases before : i < state.validators.data.size
  · simp [Array.getElem?_push, before, Nat.ne_of_lt before]
  · by_cases atEnd : i = state.validators.data.size
    · subst i
      simp [getValidatorFromDeposit]
    · simp [Array.getElem?_push, before, atEnd]

/-- A pending deposit credits a balance or appends an unslashed validator. -/
private theorem slashFlags_applyPendingDeposit {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {deposit : PendingDeposit}
    (run : applyPendingDeposit config checks state deposit = .ok after) :
    SlashFlagsKept state after := by
  unfold applyPendingDeposit at run
  split at run
  · split at run
    · cases run; exact .refl _
    simp only [bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    split at run
    · exact slashFlags_addValidator run
    · cases run; exact .refl _
  · simp only [liftAccessor_ok, bind_ok_iff] at run
    obtain ⟨_, _, run⟩ := run
    exact slashFlags_of_validators (congrArg (·.data) (increaseBalance_validators run))

/-- Passing pending deposits preserves flags even when the registry grows. -/
private theorem slashFlags_passPendingDeposits {config : Config} {checks : SignatureChecks}
    {stop : PendingDeposit → Bool} {nextEpoch : Epoch} {available : Gwei}
    {deposits : List PendingDeposit} {state : BeaconState preset fork}
    {processed : Gwei} {count : Nat} {postponed : Array PendingDeposit} {pass}
    (run : passPendingDeposits config checks stop nextEpoch available state processed count
      postponed deposits = .ok pass) : SlashFlagsKept state pass.1.state :=
  passPendingDeposits_of SlashFlagsKept .refl (fun one two => one.trans two)
    (fun ok => slashFlags_applyPendingDeposit ok) run

/-- Effective-balance updates preserve each slashing flag. -/
private theorem slashFlags_processEffectiveBalanceUpdates {state after : BeaconState preset fork}
    (run : processEffectiveBalanceUpdates state = .ok after) : SlashFlagsKept state after := by
  apply slashFlags_fold (fun _ _ _ ok => ?_) run
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact slashFlags_setValidatorAt found set rfl

/-- Every stage in the shared epoch schedule preserves the default-false slashing flag. -/
private theorem slashFlags_processEpoch {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    (run : processEpoch config checks state = .ok after) : SlashFlagsKept state after := by
  apply (processEpoch_trace run).transport SlashFlagsKept .refl (fun a b => a.trans b)
  intro stage _ s t ok
  have edge := EpochStage.action_cases.mp ok
  cases stage
  case registry => exact slashFlags_processRegistryUpdates edge
  case pendingDeposits =>
    simp only [EpochStage.Edge] at edge
    split at edge
    · unfold processPendingDeposits at edge
      simp only [bind, Except.bind, pure, Except.pure] at edge
      repeat' (split at edge <;> try cases edge)
      all_goals exact (slashFlags_passPendingDeposits ‹_›).trans slashFlags_of_validators
    · exact edge ▸ .refl _
  case effectiveBalances => exact slashFlags_processEffectiveBalanceUpdates edge
  all_goals
    exact slashFlags_of_validators
      (congrArg (·.data) (edge.validators_eq ⟨nofun, nofun, nofun⟩))

/-- Successful lookahead preserves flags across any number of epochs, at every position. -/
private theorem slashFlags_lookahead {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) : SlashFlagsKept state after := by
  have step {s t : BeaconState preset fork}
      (ok : advanceSlot config checks s = .ok t) : SlashFlagsKept s t := by
    obtain ⟨_, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok ok
    obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
    have first : SlashFlagsKept s cached := slashFlags_of_validators (by rw [cachedEq])
    have middle : SlashFlagsKept cached epoched := by
      unfold epochIfLast at epochedOk
      split at epochedOk
      · exact slashFlags_processEpoch epochedOk
      · cases epochedOk; exact .refl _
    exact (first.trans middle).trans slashFlags_of_validators
  have steps {count : Nat} {s t : BeaconState preset fork}
      (ok : advanceSlots config checks count s = .ok t) : SlashFlagsKept s t := by
    induction count generalizing s with
    | zero => cases ok; exact .refl _
    | succ count ih =>
      obtain ⟨_, first, rest⟩ := bind_ok_iff.mp ok
      exact (step first).trans (ih rest)
  unfold lookaheadState at run
  split at run
  · have slotsOk := mapError_ok_iff.mp run
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advanced⟩ := slotsOk
    exact steps advanced
  · cases run; exact .refl _

private def NotSlashed (state : BeaconState preset fork) (v : ValidatorIndex) : Prop :=
  (state.validators.data[v.toNat]?.map (·.slashed)).getD false = false

/-- Lookahead preserves unslashedness without a committee, chain or honest-set premise. -/
private theorem notSlashed_lookahead {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slot : Slot}
    (run : lookaheadState config checks state slot = .ok after) :
    ∀ v, NotSlashed after v ↔ NotSlashed state v := by
  intro v
  unfold NotSlashed
  rw [slashFlags_lookahead run v.toNat]

namespace Models.Network

variable {config : Config} {checks : SignatureChecks} {sources : BlockSources preset fork}
  {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {assignment : Assignment preset} {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config checks sources anchorState anchorBlock assignment
    genesisTimeMs) J}

/-- Held-state flags suffice for a cached checkpoint through its fixed-check lookahead origin. -/
private theorem notSlashed_checkpointState {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u : ValidatorIndex} (honest : u ∈ J) {n : ℕ}
    (flags : ∀ (root : Root) (base : BeaconState preset fork),
      ((e.world n).state u).blockStates[root]? = some base →
      ∀ v ∈ J, NotSlashed base v)
    {checkpoint : Checkpoint} {state : BeaconState preset fork}
    (read : ((e.world n).state u).checkpointState checkpoint = .ok state) :
    ∀ v ∈ J, NotSlashed state v := by
  obtain ⟨base, slot, stored, _, advanced⟩ :=
    e.checkpointStates_fixedChecks anchorStore anchored honest
      (Store.checkpointState_ok_iff.mp read)
  intro v member
  exact (notSlashed_lookahead advanced v).mpr (flags checkpoint.root base stored v member)

/-- Honest signatures for one target epoch carry the same attestation data. -/
private theorem data_eq_of_signed_of_target_epoch (slots : 0 < config.SLOT_DURATION_MS)
    {n k : ℕ} {first second : Message preset fork} (sentFirst : first ∈ (e.world n).sent)
    (sentSecond : second ∈ (e.world k).sent) {v : ValidatorIndex} {data other : AttestationData}
    (signedFirst : (v, data) ∈ statements config checks anchorState anchorBlock first)
    (signedSecond : (v, other) ∈ statements config checks anchorState anchorBlock second)
    (honest : v ∈ J) (epoch : data.target.epoch = other.target.epoch) : data = other := by
  have nonslashable := e.isSlashableAttestationData_honest slots (max n k) honest
    (e.monotone_sent (Nat.le_max_left n k) sentFirst)
    (e.monotone_sent (Nat.le_max_right n k) sentSecond) signedFirst signedSecond
  by_contra different
  simp [isSlashableAttestationData, different, epoch] at nonslashable

/-- Equal-rank honest latest votes agree before Gloas, even across different stores. -/
private theorem latest_eq_of_rank_eq (slots : 0 < config.SLOT_DURATION_MS)
    (preGloas : fork < .glamsterdam) {anchor : Store preset fork}
    (anchorStore : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchored : ∀ w ∈ J, e.start w = anchor)
    {u w v : ValidatorIndex} (caller : u ∈ J) (receiver : w ∈ J) (honest : v ∈ J)
    {n k : ℕ} {first second : LatestMessage fork}
    (firstOk : ((e.world n).state u).latestMessages[v]? = some first)
    (secondOk : ((e.world k).state w).latestMessages[v]? = some second)
    (rank : first.rank = second.rank) : first = second := by
  obtain ⟨a, firstMessage, seenFirst, rfl, signedFirst, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored caller firstOk
  obtain ⟨b, secondMessage, seenSecond, rfl, signedSecond, _⟩ :=
    e.exists_signed_origin_of_latestMessages anchorStore anchored receiver secondOk
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have epoch : a.data.target.epoch = b.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  have same := data_eq_of_signed_of_target_epoch slots
    (e.view_subset_sent n u seenFirst) (e.view_subset_sent k w seenSecond)
    signedFirst signedSecond honest epoch
  simp only [LatestMessage.ofAttestation, same]

/-- A latest vote at or above a signed vote's rank cannot come from an older slot. -/
private theorem latest_slot_floor_of_signed_rank
    (slots : 0 < config.SLOT_DURATION_MS) (preGloas : fork < .glamsterdam)
    {v : ValidatorIndex} (honest : v ∈ J) {n k : ℕ}
    {message other : Message preset fork}
    (sent : message ∈ (e.world n).sent) (sentOther : other ∈ (e.world k).sent)
    {data : AttestationData} {attestation : Attestation preset fork}
    (signed : (v, data) ∈ statements config checks anchorState anchorBlock message)
    (signedOther : (v, attestation.data) ∈
      statements config checks anchorState anchorBlock other)
    {store : Store preset fork} (origin : store.VoteOrigin config v attestation)
    (epoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    (rank : (LatestMessage.ofAttestation (fork := fork) attestation).rank ≥ data.target.epoch)
    {slot : Slot} (floor : slot ≤ data.slot) : slot ≤ attestation.data.slot := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt preGloas
  have targetLe : data.target.epoch ≤ attestation.data.target.epoch := by
    simpa [LatestMessage.rank, LatestMessage.ofAttestation, notGloas] using rank
  by_cases same : data.target.epoch = attestation.data.target.epoch
  · have dataEq := data_eq_of_signed_of_target_epoch slots sent sentOther
      signed signedOther honest same
    exact dataEq ▸ floor
  · have targetLt := UInt64.lt_of_le_of_ne targetLe same
    have slotLe : data.slot ≤ attestation.data.slot := by
      by_contra h
      have reversed := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt (UInt64.not_le.mp h)))
      rw [epoch, origin.targetEpoch] at targetLt
      have strict := UInt64.lt_iff_toNat_lt.mp targetLt
      simp only [computeEpochAtSlot, UInt64.toNat_div] at strict
      omega
    exact UInt64.le_trans floor slotLe

end Models.Network

end EthLib.Consensus
