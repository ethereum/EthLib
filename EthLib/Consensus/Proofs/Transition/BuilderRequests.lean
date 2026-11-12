module

public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.BuilderRequests

/-!
# Proofs: the deposits and exits of builders

A deposit without the builder prefix changes nothing.

A new builder takes the index of a builder only if that builder is withdrawable with no balance.

A deposit adds its amount to the sum of the builder balances, or changes nothing.

It adds the amount when its key is known, or when its key is new and its signature is valid.

An exit request either changes nothing, or starts the exit of one builder.

It starts the exit only when that builder is active, the address is its own and it owes nothing.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}

/-- The sum of the balances of the builders, on natural numbers. -/
def builderBalanceSum (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) : Nat :=
  ((state.builders gloas).data.toList.map (·.balance.toNat)).sum

/-- A deposit without the builder prefix changes nothing. -/
theorem processBuilderDepositRequest_of_not_builder {request : BuilderDepositRequest}
    (other : isBuilderWithdrawalCredential request.withdrawalCredentials = false) :
    processBuilderDepositRequest config checks state gloas request = .ok state := by
  simp [processBuilderDepositRequest, other, pure, Except.pure]

/-- A new builder takes the index of a builder only if that builder may give it up.

That builder is withdrawable in the current epoch, with no balance left. -/
theorem isReusableBuilder_of_getIndexForNewBuilder_lt
    (inside : getIndexForNewBuilder state gloas < (state.builders gloas).data.size) :
    isReusableBuilder (getCurrentEpoch state)
      (state.builders gloas).data[getIndexForNewBuilder state gloas] = true := by
  unfold getIndexForNewBuilder at inside ⊢
  cases found : (state.builders gloas).data.findIdx? (isReusableBuilder (getCurrentEpoch state))
    with
  | none => simp [found] at inside
  | some index =>
    simp only [found, Option.getD_some]
    exact (Array.findIdx?_eq_some_iff_getElem.mp found).2.1

/-- Replacing an element of a list of natural numbers changes the sum by the difference. -/
theorem sum_set_add {l : List Nat} {i : Nat} (inside : i < l.length) (x : Nat) :
    (l.set i x).sum + l[i] = l.sum + x := by
  induction l generalizing i with
  | nil => simp at inside
  | cons head tail ih =>
    cases i with
    | zero => simp; omega
    | succ i =>
      simp only [List.set_cons_succ, List.sum_cons, List.getElem_cons_succ]
      have := ih (i := i) (by simpa using inside)
      omega

/-- Setting a builder changes the sum of balances by the difference of the two balances. -/
theorem builderBalanceSum_putBuilder {index : Nat} {builder : Builder}
    (inside : index < (state.builders gloas).data.size) :
    builderBalanceSum (state.putBuilder gloas index inside builder) gloas +
        ((state.builders gloas).data[index]).balance.toNat =
      builderBalanceSum state gloas + builder.balance.toNat := by
  unfold builderBalanceSum BeaconState.putBuilder
  simp only [Array.toList_set, List.map_set]
  have := sum_set_add (l := (state.builders gloas).data.toList.map (·.balance.toNat))
    (i := index) (by simpa using inside) builder.balance.toNat
  simpa using this

/-- A deposit to a known key adds its amount to the sum of the builder balances. -/
theorem builderBalanceSum_processBuilderDepositRequest_known {request : BuilderDepositRequest}
    {index : Fin (state.builders gloas).data.size}
    (credential : isBuilderWithdrawalCredential request.withdrawalCredentials = true)
    (found : findBuilderByPubkey state gloas request.pubkey = some index)
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    builderBalanceSum after gloas = builderBalanceSum state gloas + request.amount.toNat := by
  simp only [processBuilderDepositRequest, credential, found, Bool.true_eq_false,
    ↓reduceIte] at computed
  obtain ⟨_, _, computed⟩ := bind_ok_iff.mp computed
  -- Both branches end by adding the amount to the balance of the builder at the position.
  have added : ∃ balance : Gwei, balance.toNat =
      ((state.builders gloas).data[index]).balance.toNat + request.amount.toNat ∧
      ∃ builder : Builder, builder.balance = balance ∧
        after = state.putBuilder gloas index index.isLt builder := by
    split at computed
    all_goals
      obtain ⟨withdrawableEpoch, -, rest⟩ := bind_ok_iff.mp computed
      obtain ⟨balance, summed, kept⟩ := bind_ok_iff.mp rest
      rw [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at summed
      exact ⟨balance, summed.2, _, rfl, (Except.ok.inj kept).symm⟩
  obtain ⟨balance, summed, builder, rfl, rfl⟩ := added
  have := builderBalanceSum_putBuilder (state := state) (gloas := gloas) (builder := builder)
    index.isLt
  rw [Fin.getElem_fin] at summed
  omega

/-- Registering a builder adds its amount to the sum of the builder balances.

A reused index held a builder with no balance, so nothing else changes the sum. -/
theorem builderBalanceSum_addBuilderToRegistry {pubkey : BLSPubkey} {version : UInt8}
    {executionAddress : ExecutionAddress} {amount : Gwei} {slot : Slot}
    (computed : addBuilderToRegistry state gloas pubkey version executionAddress amount slot =
      .ok after) :
    builderBalanceSum after gloas = builderBalanceSum state gloas + amount.toNat := by
  simp only [addBuilderToRegistry, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · rename_i inside
    cases computed
    have reusable := isReusableBuilder_of_getIndexForNewBuilder_lt inside
    have empty : ((state.builders gloas).data[getIndexForNewBuilder state gloas]).balance = 0 := by
      simp only [isReusableBuilder, Bool.and_eq_true, beq_iff_eq] at reusable
      exact reusable.2
    have := builderBalanceSum_putBuilder (state := state) (gloas := gloas)
      (builder := ⟨pubkey, version, executionAddress, amount, computeEpochAtSlot preset slot,
        FAR_FUTURE_EPOCH⟩) inside
    rw [empty] at this
    simpa using this
  · cases computed
    simp [builderBalanceSum]

/-- A deposit to a new key with a valid signature adds its amount to the sum of the balances. -/
theorem builderBalanceSum_processBuilderDepositRequest_new {request : BuilderDepositRequest}
    (credential : isBuilderWithdrawalCredential request.withdrawalCredentials = true)
    (unknown : findBuilderByPubkey state gloas request.pubkey = none)
    (valid : isValidBuilderDepositSignature config checks request = .ok true)
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    builderBalanceSum after gloas = builderBalanceSum state gloas + request.amount.toNat := by
  simp only [processBuilderDepositRequest, credential, unknown, valid, Bool.true_eq_false,
    ↓reduceIte, bind, Except.bind] at computed
  exact builderBalanceSum_addBuilderToRegistry computed

/-- A deposit to a new key with an invalid signature changes nothing. -/
theorem processBuilderDepositRequest_of_invalid {request : BuilderDepositRequest}
    (unknown : findBuilderByPubkey state gloas request.pubkey = none)
    (invalid : isValidBuilderDepositSignature config checks request = .ok false) :
    processBuilderDepositRequest config checks state gloas request = .ok state := by
  simp only [processBuilderDepositRequest, unknown, invalid]
  split <;> rfl

/-- An exit request changes nothing, or starts the exit of the builder with its key.

That builder is active, its address sent the request, and it owes nothing. -/
theorem processBuilderExitRequest_cases {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    after = state ∨ ∃ index, findBuilderByPubkey state gloas request.pubkey = some index ∧
      isActiveBuilder state gloas index.val.toUInt64 = .ok true ∧
      ((state.builders gloas).data[index]).executionAddress = request.sourceAddress ∧
      getPendingBalanceToWithdrawForBuilder state gloas index.val.toUInt64 = .ok 0 ∧
      initiateBuilderExit config state gloas index.val.toUInt64 = .ok after := by
  unfold processBuilderExitRequest at computed
  cases found : findBuilderByPubkey state gloas request.pubkey with
  | none =>
    simp only [found] at computed
    exact .inl (Except.ok.inj computed).symm
  | some index =>
    simp only [found] at computed
    obtain ⟨builderIndex, checked, computed⟩ := bind_ok_iff.mp computed
    rw [liftAccessor_ok, liftArith, mapError_ok_iff] at checked
    have small := (ofNatChecked_ok_iff.mp checked).1
    rw [ofNatChecked_of_lt small, Except.ok.injEq] at checked
    subst builderIndex
    obtain ⟨active, isActive, rest⟩ := bind_ok_iff.mp computed
    rw [liftAccessor_ok] at isActive
    split at rest
    · split at rest
      · rename_i activeTrue address
        obtain ⟨pending, isPending, rest⟩ := bind_ok_iff.mp rest
        rw [liftAccessor_ok] at isPending
        split at rest
        · rename_i zero
          subst activeTrue zero
          exact .inr ⟨index, rfl, isActive, address, isPending, liftAccessor_ok.mp rest⟩
        · exact .inl (Except.ok.inj rest).symm
      · exact .inl (Except.ok.inj rest).symm
    · exact .inl (Except.ok.inj rest).symm

/-- A builder deposit changes only the registry of builders. -/
theorem processBuilderDepositRequest_builders {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    ∃ builders, after = { state with builders } := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first | (cases computed; done) | (cases computed; exact ⟨_, rfl⟩)

/-- A builder exit request changes only the registry of builders. -/
theorem processBuilderExitRequest_builders {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    ∃ builders, after = { state with builders } := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact ⟨_, rfl⟩
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨_, rfl⟩

/-- Registering a builder rejects its chosen position when it is at least `2^64`. -/
theorem addBuilderToRegistry_error_of_le {pubkey : BLSPubkey} {version : UInt8}
    {executionAddress : ExecutionAddress} {amount : Gwei} {slot : Slot}
    (large : 2 ^ 64 ≤ getIndexForNewBuilder state gloas) :
    addBuilderToRegistry state gloas pubkey version executionAddress amount slot =
      .error (.accessor (.arith .overflow)) := by
  simp [addBuilderToRegistry, liftAccessor, liftArith, ofNatChecked, Nat.not_lt.mpr large,
    Except.mapError, bind, Except.bind]

/-- A builder deposit with the builder prefix rejects a matching position of `2^64` or more. -/
theorem processBuilderDepositRequest_error_of_le {request : BuilderDepositRequest}
    {position : Fin (state.builders gloas).data.size}
    (credential : isBuilderWithdrawalCredential request.withdrawalCredentials = true)
    (found : findBuilderByPubkey state gloas request.pubkey = some position)
    (large : 2 ^ 64 ≤ position.val) :
    processBuilderDepositRequest config checks state gloas request =
      .error (.accessor (.arith .overflow)) := by
  simp [processBuilderDepositRequest, credential, found, liftAccessor, liftArith, ofNatChecked,
    Nat.not_lt.mpr large, Except.mapError, bind, Except.bind]

/-- A builder exit rejects a matching position of `2^64` or more before testing its activity. -/
theorem processBuilderExitRequest_error_of_le {request : BuilderExitRequest}
    {position : Fin (state.builders gloas).data.size}
    (found : findBuilderByPubkey state gloas request.pubkey = some position)
    (large : 2 ^ 64 ≤ position.val) :
    processBuilderExitRequest config state gloas request =
      .error (.accessor (.arith .overflow)) := by
  simp [processBuilderExitRequest, found, liftAccessor, liftArith, ofNatChecked,
    Nat.not_lt.mpr large, Except.mapError, bind, Except.bind]

/-- A builder deposit changes only the registry of builders. -/
theorem processBuilderDepositRequest_eq {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    ∃ builders, after = { state with builders := builders } := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact ⟨_, rfl⟩)

/-- A builder exit request changes only the registry of builders. -/
theorem processBuilderExitRequest_eq {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    ∃ builders, after = { state with builders := builders } := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact ⟨_, rfl⟩
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact ⟨_, rfl⟩

end EthLib.Consensus
