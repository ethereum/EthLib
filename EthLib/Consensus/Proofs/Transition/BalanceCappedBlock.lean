module

public import EthLib.Consensus.Proofs.Transition.BalanceNotRaisedBlock
public import EthLib.Consensus.Proofs.Transition.InactivityLeakBetween
import EthLib.Consensus.Proofs.PayloadTimeliness
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.BalanceDrift
import EthLib.Consensus.Proofs.Transition.BuilderRequests
import EthLib.Consensus.Proofs.Transition.Execution
import EthLib.Consensus.Proofs.Transition.Payload
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: a block keeps the capped balance of a validator that does not act against it

The capped balance of a validator is the lesser of its balance and its largest effective balance.

A block lowers a balance in a few ways.

A proposer or attester slashing charges the validator it slashes.

From Altair the sync aggregate charges each member of the committee whose bit is not set.

From Capella a withdrawal lowers the balance that it names.

From Electra a withdrawal request queues a partial withdrawal.

From Electra a request to switch to compounding moves the balance above the activation balance.

Every other step of a block raises a balance or keeps it.

The withdrawal sweep takes only the part of a balance above the largest effective balance.

So it keeps the capped balance, unless the validator may withdraw all of it.

A queued partial withdrawal can take more.

The conditions exclude it and the other ways, each an act of the validator or a fault of it.

A slot that ends no epoch keeps every balance and the registry.

The module follows a validator through any sequence of such slots and blocks.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}

/-- The lesser of the balance at a position and a cap does not fall from one state to another.

A position with no balance in the first state counts as not lowered. -/
def CappedNotLowered (index : Nat) (cap : Gwei) (state after : BeaconState preset fork) :
    Prop :=
  ∀ earlier, state.balances.data[index]? = some earlier →
    ∃ later, after.balances.data[index]? = some later ∧ min earlier cap ≤ min later cap

/-- A state lowers no capped balance under itself. -/
theorem CappedNotLowered.refl (index : Nat) (cap : Gwei) (state : BeaconState preset fork) :
    CappedNotLowered index cap state state :=
  fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩

/-- Two steps that lower no capped balance at a position lower none there. -/
theorem CappedNotLowered.trans {index : Nat} {cap : Gwei}
    {first second third : BeaconState preset fork}
    (one : CappedNotLowered index cap first second)
    (two : CappedNotLowered index cap second third) :
    CappedNotLowered index cap first third := by
  intro earlier found
  obtain ⟨middle, atMiddle, low⟩ := one earlier found
  obtain ⟨later, atThird, lower⟩ := two middle atMiddle
  exact ⟨later, atThird, UInt64.le_trans low lower⟩

/-- A step that keeps the balances lowers no capped balance. -/
theorem CappedNotLowered.of_balances (same : after.balances = state.balances) (index : Nat)
    (cap : Gwei) : CappedNotLowered index cap state after := by
  intro earlier found
  exact ⟨earlier, by rw [same]; exact found, UInt64.le_refl _⟩

/-- No withdrawal or consolidation request among the execution requests comes from a key.

A consolidation request comes from the key of its source.

This excludes more than a block needs: only a switch to compounding lowers a balance at once.

A withdrawal request only queues a partial withdrawal or starts an exit. -/
def ExecutionRequests.NoneFrom (key : Cryptography.Bls.BLSPubkey)
    (requests : ExecutionRequests preset fork) : Prop :=
  (∀ request ∈ requests.withdrawals.data, request.validatorPubkey ≠ key) ∧
    ∀ request ∈ requests.consolidations.data, request.sourcePubkey ≠ key

/-! ## Balances that do not fall -/

/-- A step keeps the balance at a position from falling.

The validator there keeps its key and its largest effective balance. -/
private def Rise (index : Nat) (state after : BeaconState preset fork) : Prop :=
  (∀ earlier, state.balances.data[index]? = some earlier →
    ∃ later, after.balances.data[index]? = some later ∧ earlier ≤ later) ∧
  ∀ validator, state.validators.data[index]? = some validator →
    ∃ now, after.validators.data[index]? = some now ∧ now.pubkey = validator.pubkey ∧
      withdrawalMaxEffectiveBalance preset fork now =
        withdrawalMaxEffectiveBalance preset fork validator

/-- A state keeps its own balances and validators. -/
private theorem Rise.refl (index : Nat) (state : BeaconState preset fork) :
    Rise index state state :=
  ⟨fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩,
    fun validator found => ⟨validator, found, rfl, rfl⟩⟩

/-- Two steps that keep a balance from falling keep it from falling. -/
private theorem Rise.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Rise index first second) (two : Rise index second third) : Rise index first third := by
  refine ⟨fun earlier found => ?_, fun validator found => ?_⟩
  · obtain ⟨middle, atMiddle, low⟩ := one.1 earlier found
    obtain ⟨later, atLater, lower⟩ := two.1 middle atMiddle
    exact ⟨later, atLater, UInt64.le_trans low lower⟩
  · obtain ⟨middle, atMiddle, key, cap⟩ := one.2 validator found
    obtain ⟨now, atNow, key', cap'⟩ := two.2 middle atMiddle
    exact ⟨now, atNow, key'.trans key, cap'.trans cap⟩

/-- A step that keeps the balance and the validator at a position keeps them. -/
private theorem Rise.of_get {index : Nat}
    (balance : after.balances.data[index]? = state.balances.data[index]?)
    (validator : after.validators.data[index]? = state.validators.data[index]?) :
    Rise index state after :=
  ⟨fun earlier found => ⟨earlier, balance.trans found, UInt64.le_refl _⟩,
    fun old found => ⟨old, validator.trans found, rfl, rfl⟩⟩

/-- A step that keeps the balances and the registry keeps them at each position. -/
private theorem Rise.of_eq (balances : after.balances = state.balances)
    (validators : after.validators = state.validators) (index : Nat) : Rise index state after :=
  Rise.of_get (by rw [balances]) (by rw [validators])

/-- A fold keeps a balance from falling when each step does, given the steps so far. -/
private theorem Rise.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {start : BeaconState preset fork} {items : List α}
    (each : ∀ u x v, x ∈ items → Rise index start u → step u x = .ok v → Rise index u v)
    {first last : BeaconState preset fork} (held : Rise index start first)
    (computed : items.foldlM step first = .ok last) : Rise index start last :=
  foldlM_ok_invariant_of_mem (Rise index start)
    (fun u x v member held ok => held.trans (each u x v member held ok)) held computed

/-- A balance that does not fall keeps its lesser value with any cap. -/
private theorem Rise.capped {index : Nat} (rise : Rise index state after) (cap : Gwei) :
    CappedNotLowered index cap state after := by
  intro earlier found
  obtain ⟨later, atLater, low⟩ := rise.1 earlier found
  refine ⟨later, atLater, ?_⟩
  rw [UInt64.le_iff_toNat_le] at low ⊢
  rw [Uint64.toNat_min, Uint64.toNat_min]
  omega

/-- The validator at a position has the key it had, when the registry grows. -/
private theorem Rise.keyed {index : Nat} (rise : Rise index state after) {validator : Validator}
    (found : state.validators.data[index]? = some validator) :
    ∃ now, after.validators.data[index]? = some now ∧ now.pubkey = validator.pubkey := by
  obtain ⟨now, atNow, key, -⟩ := rise.2 validator found
  exact ⟨now, atNow, key⟩

/-- Raising a balance keeps every balance from falling. -/
private theorem rise_increaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state position delta = .ok after) (index : Nat) :
    Rise index state after := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  refine ⟨fun earlier found => ?_, fun validator found => ⟨validator, found, rfl, rfl⟩⟩
  simp only [BeaconState.putBalance, Array.getElem?_set]
  split
  · rename_i same
    subst same
    rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
    subst found
    refine ⟨_, rfl, ?_⟩
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    omega
  · exact ⟨earlier, found, UInt64.le_refl _⟩

/-- Writing a balance at another position keeps the balance at this one. -/
private theorem rise_setBalance {position : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance position balance = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : Rise index state after := by
  obtain ⟨inside, rfl⟩ := setBalance_ok set
  exact Rise.of_get (by simp only [BeaconState.putBalance, Array.getElem?_set, other,
    ↓reduceIte]) rfl

/-- Lowering the balance at another position keeps the balance at this one. -/
private theorem rise_decreaseBalance {position : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state position delta = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : Rise index state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  exact rise_setBalance set other

/-- A write of a validator keeps the balances.

At the position it must keep the key and the largest effective balance. -/
private theorem rise_setValidator {position : ValidatorIndex} {validator : Validator}
    (set : state.setValidator position validator = .ok after) {index : Nat}
    (same : position.toNat = index → ∀ old, state.validators.data[index]? = some old →
      validator.pubkey = old.pubkey ∧ withdrawalMaxEffectiveBalance preset fork validator =
        withdrawalMaxEffectiveBalance preset fork old) :
    Rise index state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨fun earlier found => ⟨earlier, found, UInt64.le_refl _⟩, fun old found => ?_⟩
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set]
  split
  · rename_i here
    exact ⟨validator, rfl, same here old found⟩
  · exact ⟨old, found, rfl, rfl⟩

/-- A write of a validator that keeps its credentials and key keeps a balance from falling. -/
private theorem rise_setValidator_of_get {position : ValidatorIndex} {validator old : Validator}
    (found : getValidator state position = .ok old)
    (set : state.setValidator position validator = .ok after)
    (key : validator.pubkey = old.pubkey)
    (credentials : validator.withdrawalCredentials = old.withdrawalCredentials) (index : Nat) :
    Rise index state after := by
  refine rise_setValidator set fun here current atCurrent => ?_
  have read := getValidator_eq_ok_iff.mp found
  rw [here, atCurrent, Option.some.injEq] at read
  subst read
  refine ⟨key, ?_⟩
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance hasCompoundingWithdrawalCredential
  rw [credentials]

/-- An exit keeps a balance from falling.

It keeps the key and the largest effective balance of each validator. -/
private theorem rise_initiateValidatorExit {position : ValidatorIndex}
    (computed : initiateValidatorExit config state position = .ok after) (index : Nat) :
    Rise index state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Rise.refl _ _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    exact rise_setValidator_of_get (old := validator) (by exact found) set rfl rfl index

/-- A slashing of another validator keeps the balance of this one from falling. -/
private theorem rise_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after)
    {index : Nat} (other : slashedIndex.toNat ≠ index) : Rise index state after := by
  obtain ⟨exited, validator, _, marked, _, _, _, lowered, _, _, raised, last, exitedOk, found, -,
    markedOk, -, -, -, loweredOk, -, -, raisedOk, lastOk, done⟩ := slashValidator_ok computed
  have cancelled : Rise index last after := by
    subst done
    split
    · exact Rise.of_eq rfl rfl index
    · exact Rise.refl _ _
  exact (rise_initiateValidatorExit exitedOk index).trans <|
    ((rise_setValidator_of_get found markedOk rfl rfl index).trans
      (Rise.of_eq rfl rfl index)).trans <|
    (rise_decreaseBalance loweredOk other).trans <|
    (rise_increaseBalance raisedOk index).trans <|
    (rise_increaseBalance lastOk index).trans cancelled

/-- A proposer slashing of another validator keeps the balance of this one from falling. -/
private theorem rise_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) {index : Nat}
    (other : slashing.signedHeader1.message.proposerIndex.toNat ≠ index) :
    Rise index state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact rise_slashValidator slashed other

/-- An attester slashing of other validators keeps the balance of this one from falling. -/
private theorem rise_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) {index : Nat}
    (other : ∀ slashed ∈ slashingIndices slashing, slashed.toNat ≠ index) :
    Rise index state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  refine foldlM_ok_invariant_of_mem (fun step => Rise index state step.1)
    (fun step slashed next member held ok => ?_)
    (show Rise index state (state, false).1 from Rise.refl index state) folded
  obtain ⟨middle, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashedOk, rfl⟩ := ok
    exact held.trans (rise_slashValidator slashedOk (other slashed member))
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ held

/-- An attestation keeps every balance from falling, and the registry. -/
private theorem rise_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (index : Nat) : Rise index state after := by
  have registry := processAttestation_registry computed
  refine ⟨?_, fun validator found => ⟨validator, by rw [registry.1]; exact found, rfl, rfl⟩⟩
  by_cases altair : Fork.altair ≤ fork
  · rw [processAttestation_of_altair altair] at computed
    obtain ⟨_, _, _, _, -, -, -, -, _, -, -, balances⟩ :=
      processAttestationAltair_balance computed
    intro earlier found
    obtain ⟨final, atFinal, value⟩ := balances index earlier found
    exact ⟨final, atFinal, UInt64.le_iff_toNat_le.mpr (by omega)⟩
  · unfold processAttestation at computed
    simp only [altair, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure,
      Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
    have kept := recordPendingAttestation_ok recorded
    intro earlier found
    refine ⟨earlier, ?_, UInt64.le_refl _⟩
    split at kept <;>
    · obtain ⟨_, rest⟩ := kept
      rw [← rest] at found
      exact found

/-- A new validator lands after the registry, so it keeps a position of it. -/
private theorem rise_addValidatorToRegistry {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after)
    {index : Nat} (inside : index < state.validators.data.size) : Rise index state after := by
  have pushed := addValidatorToRegistry_validators_eq_push computed
  refine ⟨fun earlier found =>
    ⟨earlier, addValidatorToRegistry_balance computed inside found, UInt64.le_refl _⟩,
    fun validator found => ⟨validator, ?_, rfl, rfl⟩⟩
  rw [pushed, Array.getElem?_push, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  exact found

/-- A deposit keeps a balance of the registry from falling. -/
private theorem rise_applyDeposit {pubkey : Cryptography.Bls.BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : Cryptography.Bls.BLSSignature}
    (computed : applyDeposit config checks state pubkey withdrawalCredentials amount signature =
      .ok after)
    {index : Nat} (inside : index < state.validators.data.size) : Rise index state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (rise_addValidatorToRegistry added inside).trans (Rise.of_eq rfl rfl index)
      · cases computed
        exact Rise.refl _ _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact Rise.of_eq rfl rfl index
  · rcases applyPendingDeposit_cases computed with rfl | ⟨_, raised⟩ | ⟨_, added⟩
    · exact Rise.refl _ _
    · exact rise_increaseBalance raised index
    · exact rise_addValidatorToRegistry added inside

/-- A deposit of a block keeps a balance of the registry from falling. -/
private theorem rise_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) {index : Nat}
    (inside : index < state.validators.data.size) : Rise index state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (Rise.of_eq (after := { state with eth1DepositIndex := fun _ => next }) rfl rfl
    index).trans (rise_applyDeposit applied inside)

/-- The BLS prefix is not the compounding prefix. -/
private theorem bls_ne_compounding :
    (BLS_WITHDRAWAL_PREFIX[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = false := by
  decide

/-- The execution address prefix is not the compounding prefix. -/
private theorem eth1_ne_compounding :
    (ETH1_ADDRESS_WITHDRAWAL_PREFIX[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = false := by
  decide

/-- A change of BLS credentials keeps every balance and each largest effective balance.

Neither BLS credentials nor credentials with an address are compounding. -/
private theorem rise_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after)
    (index : Nat) : Rise index state after := by
  obtain ⟨validator, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok computed
  refine rise_setValidator set fun here current atCurrent => ?_
  have read := getValidator_eq_ok_iff.mp found
  rw [here, atCurrent, Option.some.injEq] at read
  subst read
  refine ⟨rfl, ?_⟩
  simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
    hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential,
    executionCredentials_prefix, bls, bls_ne_compounding, eth1_ne_compounding]

/-! ## Steps that keep the validator and its balance -/

/-- A step keeps the balance and the validator at a position.

When no queued partial withdrawal names the position before it, none names it after it. -/
private def Still (index : Nat) (state after : BeaconState preset fork) : Prop :=
  after.balances.data[index]? = state.balances.data[index]? ∧
    after.validators.data[index]? = state.validators.data[index]? ∧
    ((∀ electra : .pectra ≤ fork, ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
        pending.validatorIndex.toNat ≠ index) →
      ∀ electra : .pectra ≤ fork, ∀ pending ∈ (after.pendingPartialWithdrawals electra).data,
        pending.validatorIndex.toNat ≠ index)

/-- A state keeps its own balance and validator. -/
private theorem Still.refl (index : Nat) (state : BeaconState preset fork) :
    Still index state state :=
  ⟨rfl, rfl, id⟩

/-- Two steps that keep the balance and the validator keep them. -/
private theorem Still.trans {index : Nat} {first second third : BeaconState preset fork}
    (one : Still index first second) (two : Still index second third) :
    Still index first third :=
  ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2 ∘ one.2.2⟩

/-- A step that keeps the balances, the registry and the queued partial withdrawals keeps them. -/
private theorem Still.of_eq (balances : after.balances = state.balances)
    (validators : after.validators = state.validators)
    (pending : after.pendingPartialWithdrawals = state.pendingPartialWithdrawals) (index : Nat) :
    Still index state after :=
  ⟨by rw [balances], by rw [validators], by rw [pending]; exact id⟩

/-- A step that keeps the balance and the validator at a position keeps a balance from falling. -/
private theorem Still.rise {index : Nat} (still : Still index state after) :
    Rise index state after :=
  Rise.of_get still.1 still.2.1

/-- A fold keeps the balance and the validator when each step does, given the steps so far. -/
private theorem Still.foldlM {index : Nat} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    {start : BeaconState preset fork} {items : List α}
    (each : ∀ u x v, x ∈ items → Still index start u → step u x = .ok v → Still index u v)
    {first last : BeaconState preset fork} (held : Still index start first)
    (computed : items.foldlM step first = .ok last) : Still index start last :=
  foldlM_ok_invariant_of_mem (Still index start)
    (fun u x v member held ok => held.trans (each u x v member held ok)) held computed

/-- The first position with a key is not that of a validator with another key. -/
private theorem findValidatorByPubkey_ne {key : Cryptography.Bls.BLSPubkey}
    {position : Fin state.validators.data.size}
    (located : findValidatorByPubkey state key = some position)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (other : key ≠ validator.pubkey) : position.val ≠ index := by
  intro same
  unfold findValidatorByPubkey at located
  have keyed := (Array.findFinIdx?_eq_some_iff.mp located).1
  rw [Array.getElem?_eq_some_iff] at found
  obtain ⟨inside, atIndex⟩ := found
  subst same
  rw [show state.validators.data[position] = validator from atIndex] at keyed
  exact other (beq_iff_eq.mp keyed).symm

/-- The position of a request from another key is not that of a validator with this key. -/
private theorem position_ne {key : Cryptography.Bls.BLSPubkey}
    {position : Fin state.validators.data.size}
    (located : findValidatorByPubkey state key = some position) {converted : UInt64}
    (conv : liftAccessor (liftArith (Uint64.ofNatChecked position.val)) =
      (Except.ok converted : Except TransitionError UInt64))
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (other : key ≠ validator.pubkey) : converted.toNat ≠ index := by
  simp only [liftAccessor_ok, liftArith, mapError_ok_iff] at conv
  rw [(Uint64.ofNatChecked_ok_iff.mp conv).2]
  exact findValidatorByPubkey_ne located found other

/-- A write of a validator at another position keeps the balance and validator at this one. -/
private theorem still_setValidator {position : ValidatorIndex} {validator : Validator}
    (set : state.setValidator position validator = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : Still index state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine ⟨rfl, ?_, id⟩
  simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
    Array.getElem?_set, other, ↓reduceIte]

/-- An exit of another validator keeps the balance and validator at this position. -/
private theorem still_initiateValidatorExit {position : ValidatorIndex}
    (computed : initiateValidatorExit config state position = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : Still index state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact Still.refl _ _
  · obtain ⟨_, _, rfl⟩ := exitQueue_eq queue
    exact (Still.of_eq rfl rfl rfl index).trans (still_setValidator set other)

/-- A partial withdrawal request of another validator keeps the balance at this position.

It queues no partial withdrawal that names this position. -/
private theorem still_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {position : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra position validator amount owed =
      .ok after) {index : Nat} (other : position.toNat ≠ index) : Still index state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨churnedState, _⟩, churned, _, _, pending, pendingOk, rfl⟩ := computed
    have kept := computeExitEpochAndUpdateChurn_earliest churned
    refine ⟨by rw [kept.2.2], by rw [kept.2.1], fun quiet electra' member inside => ?_⟩
    have pushed := appendWithinLimit_data pendingOk
    simp only at inside
    rw [pushed, Array.mem_push] at inside
    rcases inside with old | rfl
    · -- The churn keeps the queue of partial withdrawals.
      have queue : churnedState.pendingPartialWithdrawals = state.pendingPartialWithdrawals := by
        simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at churned
        obtain ⟨_, _, _, _, _, _, churned⟩ := churned
        cases churned
        rfl
      rw [queue] at old
      exact quiet electra member old
    · exact other
  · cases computed
    exact Still.refl _ _

/-- A withdrawal request from another key keeps the balance and the validator of this one.

No queued partial withdrawal that it adds names this position. -/
private theorem still_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (other : request.validatorPubkey ≠ validator.pubkey) : Still index state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Still.refl _ _)
    | (with_reducible refine still_initiateValidatorExit (liftAccessor_ok.mp computed) ?_
       with_reducible exact position_ne ‹_› ‹_› found other)
    | (with_reducible refine still_requestPartialWithdrawal computed ?_
       with_reducible exact position_ne ‹_› ‹_› found other)

/-- A switch of another validator to compounding keeps the balance and validator at this one. -/
private theorem still_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {position : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra position = .ok after) {index : Nat}
    (other : position.toNat ≠ index) : Still index state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, mid, set, queued⟩ := computed
  refine (still_setValidator set other).trans ?_
  simp only [queueExcessActiveBalance, bind_ok_iff] at queued
  obtain ⟨_, _, queued⟩ := queued
  split at queued
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
    obtain ⟨_, _, _, _, _, lowered, rfl⟩ := queued
    obtain ⟨inside, rfl⟩ := setBalance_ok lowered
    refine ⟨?_, rfl, id⟩
    simp only [BeaconState.putBalance, Array.getElem?_set, other, ↓reduceIte]
  · cases queued
    exact Still.refl _ _

/-- A queued consolidation from another validator keeps the balance and validator at this one. -/
private theorem still_queueConsolidation {electra : .pectra ≤ fork}
    {sourceIndex : ValidatorIndex} {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourceIndex source targetIndex = .ok after)
    {index : Nat} (other : sourceIndex.toNat ≠ index) : Still index state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at churned
  obtain ⟨_, _, _, _, _, _, churned⟩ := churned
  cases churned
  exact ((Still.of_eq rfl rfl rfl index).trans (still_setValidator set other)).trans
    (Still.of_eq rfl rfl rfl index)

/-- A consolidation request from another key keeps the balance and validator of this one. -/
private theorem still_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (other : request.sourcePubkey ≠ validator.pubkey) : Still index state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Still.refl _ _)
    | (with_reducible refine still_switchToCompoundingValidator (liftAccessor_ok.mp computed) ?_
       with_reducible exact position_ne ‹_› ‹_› found other)
    | (with_reducible refine still_queueConsolidation computed ?_
       with_reducible exact position_ne ‹_› ‹_› found other)

/-- A deposit request keeps the balances, the registry and the queued partial withdrawals. -/
private theorem still_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) (index : Nat) :
    Still index state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact Still.of_eq rfl rfl rfl index

/-! ## The balance alone -/

/-- A proposer slashing of another validator keeps the balance of this one from falling. -/
theorem balanceRises_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) {index : Nat}
    (other : slashing.signedHeader1.message.proposerIndex.toNat ≠ index) :
    BalanceRises index state after :=
  (rise_processProposerSlashing computed other).1

/-- An attester slashing of other validators keeps the balance of this one from falling. -/
theorem balanceRises_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) {index : Nat}
    (other : ∀ slashed ∈ slashingIndices slashing, slashed.toNat ≠ index) :
    BalanceRises index state after :=
  (rise_processAttesterSlashing computed other).1

/-- An attestation keeps every balance from falling. -/
theorem balanceRises_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after)
    (index : Nat) : BalanceRises index state after :=
  (rise_processAttestation computed index).1

/-- A deposit of a block keeps a balance of the registry from falling. -/
theorem balanceRises_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) {index : Nat}
    (inside : index < state.validators.data.size) : BalanceRises index state after :=
  (rise_processDeposit computed inside).1

/-- A consolidation request from another key keeps the balance of this validator. -/
theorem balanceStays_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (other : request.sourcePubkey ≠ validator.pubkey) : BalanceStays index state after := by
  intro earlier atIndex
  rw [(still_processConsolidationRequest computed found other).1]
  exact atIndex

/-! ## The steps of a block -/

/-- From Gloas, the payload of the parent keeps the balance and validator of a voter.

No withdrawal or consolidation request of it comes from the key of the voter. -/
private theorem still_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unrequested : (body.parentExecutionRequests gloas).NoneFrom validator.pubkey) :
    Still index state after := by
  rcases processParentExecutionPayload_ok computed with ⟨-, -, rfl⟩ |
    ⟨-, settledState, _, _, _, _, _, _, settledOk, depositsOk, withdrawalsOk, consolidationsOk,
      buildersOk, exitsOk, -, rfl⟩
  · exact Still.refl _ _
  have settled := settleParentPayment_eq settledOk
  have one : Still index state settledState := by
    rw [settled]
    exact Still.of_eq rfl rfl rfl index
  have two := Still.foldlM (fun _ _ _ _ _ ok => still_processDepositRequest ok index) one depositsOk
  -- Each request names another key, so it lands at another position.
  have three := Still.foldlM (fun _ request _ member held ok =>
    still_processWithdrawalRequest ok (held.2.1.trans found)
      (unrequested.1 request (Array.mem_toList_iff.mp member))) two withdrawalsOk
  have four := Still.foldlM (fun _ request _ member held ok =>
    still_processConsolidationRequest ok (held.2.1.trans found)
      (unrequested.2 request (Array.mem_toList_iff.mp member))) three consolidationsOk
  have five := Still.foldlM (fun _ _ _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderDepositRequest_builders ok
    exact Still.of_eq rfl rfl rfl index) four buildersOk
  have six := Still.foldlM (fun _ _ _ _ _ ok => by
    obtain ⟨_, rfl⟩ := processBuilderExitRequest_builders ok
    exact Still.of_eq rfl rfl rfl index) five exitsOk
  exact six.trans (Still.of_eq rfl rfl rfl index)

/-- The execution part of a block keeps the capped balance of a validator that may not yet withdraw.

No queued partial withdrawal may name it. -/
private theorem capped_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unwithdrawable : getCurrentEpoch state < validator.withdrawableEpoch)
    (unqueued : ∀ electra : .pectra ≤ fork,
      ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
        pending.validatorIndex.toNat ≠ index) :
    CappedNotLowered index (withdrawalMaxEffectiveBalance preset fork validator) state after := by
  have withdrawals {t : BeaconState preset fork} {capella : .shapella ≤ fork}
      {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
      (ok : processWithdrawals state capella payload = .ok t) :
      CappedNotLowered index (withdrawalMaxEffectiveBalance preset fork validator) state t :=
    processWithdrawals_capped ok found unwithdrawable unqueued
  have payload {s t : BeaconState preset fork}
      {execution : .bellatrix ≤ fork ∧ fork < .glamsterdam}
      (ok : processExecutionPayload config engine s body execution = .ok t) :
      CappedNotLowered index (withdrawalMaxEffectiveBalance preset fork validator) s t := by
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok ok
    exact CappedNotLowered.of_balances rfl _ _
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    obtain ⟨_, rfl⟩ := processExecutionPayloadBid_eq bid
    exact (withdrawals withdrawnOk).trans (CappedNotLowered.of_balances rfl _ _)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (withdrawals withdrawnOk).trans (payload paid)
  · dsimp only at computed
    split at computed
    · exact payload computed
    · cases computed
      exact CappedNotLowered.refl _ _ _

/-- The operations keep the balance of a validator from falling, and its key and cap.

No slashing names it, and no request that they apply comes from its key. -/
private theorem rise_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unproposed : ∀ slashing ∈ body.proposerSlashings.data,
      slashing.signedHeader1.message.proposerIndex.toNat ≠ index)
    (unattested : ∀ slashing ∈ body.attesterSlashings.data,
      ∀ slashed ∈ slashingIndices slashing, slashed.toNat ≠ index)
    (unrequested : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      (body.executionRequests electra).NoneFrom validator.pubkey) :
    Rise index state after := by
  have proposers {u v : BeaconState preset fork} (held : Rise index state u)
      (ok : body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) u =
        .ok v) : Rise index state v :=
    Rise.foldlM (fun _ slashing _ member _ ok => rise_processProposerSlashing ok
      (unproposed slashing (Array.mem_toList_iff.mp member))) held ok
  have attesters {u v : BeaconState preset fork} (held : Rise index state u)
      (ok : body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks) u =
        .ok v) : Rise index state v :=
    Rise.foldlM (fun _ slashing _ member _ ok => rise_processAttesterSlashing ok
      (unattested slashing (Array.mem_toList_iff.mp member))) held ok
  have attestations {u v : BeaconState preset fork} {votes : List (Attestation preset fork)}
      (held : Rise index state u)
      (ok : votes.foldlM (processAttestation config checks · parentSlot ·) u = .ok v) :
      Rise index state v :=
    Rise.foldlM (fun _ _ _ _ _ ok => rise_processAttestation ok index) held ok
  have exits {u v : BeaconState preset fork} {signed : List SignedVoluntaryExit}
      (held : Rise index state u)
      (ok : signed.foldlM (processVoluntaryExit config checks) u = .ok v) :
      Rise index state v :=
    Rise.foldlM (fun _ _ _ _ _ ok =>
      rise_initiateValidatorExit (processVoluntaryExit_initiates ok) index) held ok
  have changes {u v : BeaconState preset fork} {signed : List SignedBLSToExecutionChange}
      (held : Rise index state u)
      (ok : signed.foldlM (processBlsToExecutionChange config checks) u = .ok v) :
      Rise index state v :=
    Rise.foldlM (fun _ _ _ _ _ ok => rise_processBlsToExecutionChange ok index) held ok
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    refine Rise.foldlM (fun _ _ _ _ _ ok => ?_) (changes (exits (attestations (attesters
      (proposers (Rise.refl index state) proposersOk) attestersOk) attestedOk) exitsOk) changesOk)
      paid
    rw [processPayloadAttestation_eq ok]
    exact Rise.refl _ _
  rename_i notGloas
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have attested := attestations (attesters (proposers (Rise.refl index state) proposersOk)
    attestersOk) attestedOk
  -- A deposit keeps each position of the registry, which keeps the validator.
  have deposited := Rise.foldlM (fun _ _ _ _ held ok => by
    obtain ⟨_, atNow, -⟩ := held.keyed found
    exact rise_processDeposit ok (Array.getElem?_eq_some_iff.mp atNow).1) attested depositedOk
  have changed : Rise index state changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact changes (exits deposited exitsOk) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ exits deposited exitsOk
  split at requestsOk
  · rename_i electra
    simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requestsOk
    obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := requestsOk
    -- Each request names another key, so it lands at another position.
    have requests := unrequested ⟨electra, Nat.lt_of_not_le notGloas⟩
    have one := Rise.foldlM (fun _ _ _ _ _ ok => (still_processDepositRequest ok index).rise)
      changed depositsOk
    have two := Rise.foldlM (fun _ request _ member held ok => by
      obtain ⟨now, atNow, key⟩ := held.keyed found
      refine (still_processWithdrawalRequest ok atNow ?_).rise
      rw [key]
      exact requests.1 request (Array.mem_toList_iff.mp member)) one withdrawalsOk
    exact Rise.foldlM (fun _ request _ member held ok => by
      obtain ⟨now, atNow, key⟩ := held.keyed found
      refine (still_processConsolidationRequest ok atNow ?_).rise
      rw [key]
      exact requests.2 request (Array.mem_toList_iff.mp member)) two consolidationsOk
  · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
    exact requestsOk ▸ changed

/-- The sync rewards do not lower a balance when every member at it has its bit set. -/
private theorem syncRewards_ge {reward proposerReward index : Nat} {chosen : ValidatorIndex} :
    ∀ (members : List (ValidatorIndex × Bool)) (balance : Nat),
      (∀ member ∈ members, member.2 = false → member.1.toNat ≠ index) →
      balance ≤ members.foldl (fun balance member =>
        if member.2 then balance + (if member.1.toNat = index then reward else 0) +
          (if chosen.toNat = index then proposerReward else 0)
        else if member.1.toNat = index then balance - reward else balance) balance
  | [], _, _ => Nat.le_refl _
  | member :: members, balance, apart => by
    rw [List.foldl_cons]
    refine Nat.le_trans ?_ (syncRewards_ge members _
      fun other inside => apart other (List.mem_cons_of_mem _ inside))
    have head := apart member List.mem_cons_self
    split
    · exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)
    · rename_i unset
      simp [head (by simpa using unset)]

/-- The sync aggregate keeps a balance from falling.

Each member with the key of the validator must have its bit set. -/
private theorem rise_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after)
    {index : Nat} {validator : Validator} (found : state.validators.data[index]? = some validator)
    (signed : ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
      aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1 = validator.pubkey → member.2 = true) :
    Rise index state after := by
  obtain ⟨_, _, members, chosen, -, -, membersOk, -, balances⟩ :=
    processSyncAggregate_balance computed
  have elsewhere := signers_elsewhere (bit := false) membersOk found
    fun member inside unset same => by
      rw [signed member inside same] at unset
      cases unset
  refine ⟨fun earlier atIndex => ?_, fun old atOld => ?_⟩
  · obtain ⟨final, atFinal, value⟩ := balances index earlier atIndex
    refine ⟨final, atFinal, UInt64.le_iff_toNat_le.mpr ?_⟩
    rw [value]
    exact syncRewards_ge _ _ elsewhere
  · obtain ⟨_, rfl⟩ := processSyncAggregate_eq computed
    exact ⟨old, atOld, rfl, rfl⟩

/-- A block keeps the capped balance of a validator that does not act against it.

This holds when the block succeeds, at every fork.

The cap is the largest effective balance of the validator before the block.

No proposer or attester slashing of the block names the validator.

From Altair, each member of the sync committee with its key has its bit set.

From Electra, no withdrawal or consolidation request that the block applies comes from its key.

The validator may not yet withdraw in the epoch of the state.

From Electra, no queued partial withdrawal names it.

After the block it keeps its key, its effective balance and its largest effective balance. -/
theorem cappedNotLowered_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (unproposed : ∀ slashing ∈ block.body.proposerSlashings.data,
      slashing.signedHeader1.message.proposerIndex.toNat ≠ index)
    (unattested : ∀ slashing ∈ block.body.attesterSlashings.data,
      ∀ slashed ∈ slashingIndices slashing, slashed.toNat ≠ index)
    (signed : ∀ altair : .altair ≤ fork,
      ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
        (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList,
        member.1 = validator.pubkey → member.2 = true)
    (unrequested : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      (block.body.executionRequests electra).NoneFrom validator.pubkey)
    (unrequestedParent : ∀ gloas : .glamsterdam ≤ fork,
      (block.body.parentExecutionRequests gloas).NoneFrom validator.pubkey)
    (unwithdrawable : getCurrentEpoch state < validator.withdrawableEpoch)
    (unqueued : ∀ electra : .pectra ≤ fork,
      ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
        pending.validatorIndex.toNat ≠ index) :
    CappedNotLowered index (withdrawalMaxEffectiveBalance preset fork validator) state after ∧
      ∃ now, after.validators.data[index]? = some now ∧ now.pubkey = validator.pubkey ∧
        now.effectiveBalance = validator.effectiveBalance ∧
        withdrawalMaxEffectiveBalance preset fork now =
          withdrawalMaxEffectiveBalance preset fork validator := by
  obtain ⟨input, last, started, operated, -, synced⟩ := processBlock_operationsInput computed
  obtain ⟨parented, headed, executed, revealed, paidOk, headerOk, executionOk, randaoOk,
    eth1Ok⟩ := started
  -- From Gloas the payload of the parent runs first, and keeps the validator and its balance.
  have paid : Still index state parented ∧ BlockFixed state parented := by
    split at paidOk
    · rename_i gloas
      exact ⟨still_processParentExecutionPayload paidOk found (unrequestedParent gloas),
        (down_processParentExecutionPayload (index := index) paidOk).2⟩
    · cases paidOk
      exact ⟨Still.refl _ _, BlockFixed.refl _⟩
  -- The header keeps everything that the withdrawals read of the validator.
  have header : Still index parented headed ∧ headed.slot = parented.slot ∧
      headed.currentSyncCommittee = parented.currentSyncCommittee := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact ⟨Still.of_eq rfl rfl rfl index, rfl, rfl⟩
  have early := paid.1.trans header.1
  have atHeaded : headed.validators.data[index]? = some validator := early.2.1.trans found
  have epoch : getCurrentEpoch headed = getCurrentEpoch state := by
    simp only [getCurrentEpoch, header.2.1, paid.2.1]
  -- From Bellatrix the execution part runs, with the withdrawals from Capella.
  have execution : CappedNotLowered index (withdrawalMaxEffectiveBalance preset fork validator)
      headed executed ∧ executed.validators = headed.validators ∧
      executed.currentSyncCommittee = headed.currentSyncCommittee := by
    split at executionOk
    · exact ⟨capped_processBlockExecution executionOk atHeaded (by rw [epoch]; exact unwithdrawable)
        (early.2.2 unqueued), processBlockExecution_validators executionOk,
        (down_processBlockExecution (index := index) executionOk).2.2.2.1⟩
    · cases executionOk
      exact ⟨CappedNotLowered.refl _ _ _, rfl, rfl⟩
  -- The RANDAO reveal and the vote on the deposit contract keep the balances and the registry.
  have late : input.balances = executed.balances ∧ input.validators = executed.validators ∧
      input.currentSyncCommittee = executed.currentSyncCommittee := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    split at eth1Ok
    · obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
      exact ⟨congrArg (·.balances) rest, congrArg (·.validators) rest,
        congrArg (·.currentSyncCommittee) rest⟩
    · cases eth1Ok
      exact ⟨rfl, rfl, rfl⟩
  have atExecuted : executed.validators.data[index]? = some validator := by
    rw [execution.2.1]
    exact atHeaded
  have atInput : input.validators.data[index]? = some validator := by
    rw [late.2.1]
    exact atExecuted
  have operations := rise_processOperations operated atInput unproposed unattested unrequested
  -- From Altair the sync aggregate reads the committee of the state before the block.
  have sync : Rise index last after := by
    split at synced
    · rename_i altair
      obtain ⟨now, atNow, key⟩ := operations.keyed atInput
      have committee : last.currentSyncCommittee = state.currentSyncCommittee :=
        (fixed_processOperations operated).2.2.1.trans <| late.2.2.trans <|
          execution.2.2.trans <| header.2.2.trans paid.2.2.2.1
      refine rise_processSyncAggregate synced atNow ?_
      rw [committee, key]
      exact signed altair
    · cases synced
      exact Rise.refl _ _
  have whole : Rise index executed after :=
    (Rise.of_eq late.1 late.2.1 index).trans (operations.trans sync)
  refine ⟨(early.rise.capped _).trans (execution.1.trans (whole.capped _)), ?_⟩
  obtain ⟨now, atNow, key, cap⟩ := whole.2 validator atExecuted
  have effective := effectiveKept_processBlock computed index
    (Array.getElem?_eq_some_iff.mp found).1
  simp only [effectiveAt, found, atNow, Option.map_some, Option.getD_some] at effective
  exact ⟨now, atNow, key, UInt64.toNat_inj.mp effective, cap⟩

/-- One step between two epoch transitions, under which a validator keeps its capped balance.

The validator is named by its position and by its key, given separately.

A slot step is one slot that does not end an epoch, so it runs no epoch transition.

A block step is a successful block whose slashings name another validator.

From Altair each member of the current sync committee with the key has its bit set.

From Electra no withdrawal or consolidation request that it applies comes from the key.

The validator at the position may not yet withdraw in the epoch of the state before.

From Electra no queued partial withdrawal of that state names the position. -/
inductive VoterStep (config : Config) (checks : SignatureChecks) (index : Nat)
    (key : Cryptography.Bls.BLSPubkey) :
    BeaconState preset fork → BeaconState preset fork → Prop where
  | slot {state after : BeaconState preset fork}
      (ok : advanceSlot config checks state = .ok after)
      (inside : (state.slot + 1) % preset.SLOTS_PER_EPOCH ≠ 0) :
      VoterStep config checks index key state after
  | block {state after : BeaconState preset fork} (engine : ExecutionEngine preset fork)
      (block : BeaconBlock preset fork)
      (ok : processBlock config checks engine state block = .ok after)
      (unproposed : ∀ slashing ∈ block.body.proposerSlashings.data,
        slashing.signedHeader1.message.proposerIndex.toNat ≠ index)
      (unattested : ∀ slashing ∈ block.body.attesterSlashings.data,
        ∀ slashed ∈ slashingIndices slashing, slashed.toNat ≠ index)
      (signed : ∀ altair : .altair ≤ fork,
        ∀ member ∈ ((state.currentSyncCommittee altair).value.pubkeys.toArray.zip
          (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList,
          member.1 = key → member.2 = true)
      (unrequested : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
        (block.body.executionRequests electra).NoneFrom key)
      (unrequestedParent : ∀ gloas : .glamsterdam ≤ fork,
        (block.body.parentExecutionRequests gloas).NoneFrom key)
      (unwithdrawable : ∀ validator, state.validators.data[index]? = some validator →
        getCurrentEpoch state < validator.withdrawableEpoch)
      (unqueued : ∀ electra : .pectra ≤ fork,
        ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
          pending.validatorIndex.toNat ≠ index) :
      VoterStep config checks index key state after

/-- A plain block is a step of a validator.

It has no slashing, no withdrawal or consolidation request, and every sync bit set.

The validator may not yet withdraw, and no queued partial withdrawal names it.

So the conditions on the content of a block reduce to these simpler ones. -/
theorem VoterStep.of_plain {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine state block = .ok after) {index : Nat}
    {key : Cryptography.Bls.BLSPubkey}
    (noProposerSlashing : block.body.proposerSlashings.data = #[])
    (noAttesterSlashing : block.body.attesterSlashings.data = #[])
    (full : ∀ altair : .altair ≤ fork,
      ∀ bit ∈ (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray, bit = true)
    (noRequest : ∀ electra : .pectra ≤ fork ∧ fork < .glamsterdam,
      (block.body.executionRequests electra).withdrawals.data = #[] ∧
        (block.body.executionRequests electra).consolidations.data = #[])
    (noParentRequest : ∀ gloas : .glamsterdam ≤ fork,
      (block.body.parentExecutionRequests gloas).withdrawals.data = #[] ∧
        (block.body.parentExecutionRequests gloas).consolidations.data = #[])
    (unwithdrawable : ∀ validator, state.validators.data[index]? = some validator →
      getCurrentEpoch state < validator.withdrawableEpoch)
    (unqueued : ∀ electra : .pectra ≤ fork,
      ∀ pending ∈ (state.pendingPartialWithdrawals electra).data,
        pending.validatorIndex.toNat ≠ index) :
    VoterStep config checks index key state after := by
  refine .block engine block ok (fun slashing member => ?_) (fun slashing member => ?_)
    (fun altair member inside _ => ?_) (fun electra => ?_) (fun gloas => ?_) unwithdrawable unqueued
  · rw [noProposerSlashing] at member
    simp at member
  · rw [noAttesterSlashing] at member
    simp at member
  · obtain ⟨_, bit⟩ := member
    rw [Array.toList_zip] at inside
    exact full altair bit (Array.mem_toList_iff.mp (List.of_mem_zip inside).2)
  · obtain ⟨withdrawals, consolidations⟩ := noRequest electra
    exact ⟨fun _ member => by simp [withdrawals] at member,
      fun _ member => by simp [consolidations] at member⟩
  · obtain ⟨withdrawals, consolidations⟩ := noParentRequest gloas
    exact ⟨fun _ member => by simp [withdrawals] at member,
      fun _ member => by simp [consolidations] at member⟩

/-- A run of such steps keeps what the inactivity leak reads of the validator.

The validator has the given key before the steps.

After them it keeps its position, its key, its effective balance and its largest effective balance.

The lesser of its balance and that largest effective balance does not fall. -/
theorem voterSteps_kept {index : Nat} {key : Cryptography.Bls.BLSPubkey}
    (steps : Relation.ReflTransGen (VoterStep config checks index key) state after)
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (keyed : validator.pubkey = key) :
    ∃ now, after.validators.data[index]? = some now ∧ now.pubkey = key ∧
      now.effectiveBalance = validator.effectiveBalance ∧
      withdrawalMaxEffectiveBalance preset fork now =
        withdrawalMaxEffectiveBalance preset fork validator ∧
      CappedNotLowered index (withdrawalMaxEffectiveBalance preset fork validator) state after := by
  induction steps with
  | refl => exact ⟨validator, found, keyed, rfl, rfl, .refl _ _ _⟩
  | tail _ step kept => ?_
  obtain ⟨now, atNow, nowKey, nowBalance, nowCap, capped⟩ := kept
  cases step with
  | slot ok inside =>
    obtain ⟨validators, balances, -⟩ := advanceSlot_quiet ok inside
    exact ⟨now, by rw [validators]; exact atNow, nowKey, nowBalance, nowCap,
      capped.trans (.of_balances balances _ _)⟩
  | block engine block ok unproposed unattested signed unrequested unrequestedParent
      unwithdrawable unqueued =>
    rw [← nowKey] at signed unrequested unrequestedParent
    obtain ⟨blocked, later, atLater, laterKey, laterBalance, laterCap⟩ :=
      cappedNotLowered_processBlock ok atNow unproposed unattested signed unrequested
        unrequestedParent (unwithdrawable now atNow) unqueued
    rw [nowCap] at blocked
    exact ⟨later, atLater, laterKey.trans nowKey, laterBalance.trans nowBalance,
      laterCap.trans nowCap, capped.trans blocked⟩

end EthLib.Consensus
