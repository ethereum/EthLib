module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Blocks.SystemCall
public import EthLib.Execution.Blocks.Transition
public import EthLib.Execution.Proofs.Evm.Logic.Callee
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: the system calls of a block

A checked system call succeeds exactly when its contract has code and the call stops with no error.

It fails as an empty contract exactly when the contract has no code.

It fails with the error of its call exactly when the contract has code and the call stops with it.

The requests of a block come in the order of their types, withdrawals before consolidations.

From Glamsterdam, the builder deposits and exits follow, by EIP-8282.

Each list holds its type byte and at least one byte of data.

Before Pectra a block reads no request.

The calls at the start of a block, and the requests of a block, are stated call by call.

A system call has 30,000,000 gas at every fork.

Up to BPO5 it has no reservoir and runs with one counter of the gas left.

From Glamsterdam it has a reservoir of 1,566,720 state gas, and runs with the meter of EIP-8037.

From Paris, an unchecked call to empty code outside the precompiles only records its target.

Joining that call keeps the block state and adds the address to the block access list builder.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)
open EthLib.Execution.Transactions (processMessageCall)

variable {fork : Fork} {env : BlockEnvironment fork} {block : BlockState} {target : Address}
  {data : ByteArray}

/-! ## The call -/

/-- A system call has 30,000,000 gas at every fork. -/
theorem gas_systemMessage : (systemMessage env target data).gas = 30000000 := rfl

/-- Up to BPO5, a system call has no reservoir of state gas. -/
theorem systemReservoir_of_lt_glamsterdam (h : fork < .glamsterdam) : systemReservoir fork = 0 := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [systemReservoir, hpre, ↓reduceIte]

/-- From Glamsterdam, a system call has the state gas of 16 new slots: 1,566,720. -/
theorem systemReservoir_of_glamsterdam (h : .glamsterdam ≤ fork) :
    systemReservoir fork = 1566720 := by
  simp only [systemReservoir, h, ↓reduceIte]
  rfl

/-- Up to BPO5, a system call runs its message with one counter of the gas left. -/
theorem systemCall_of_lt_glamsterdam (h : fork < .glamsterdam) :
    systemCall env block target data =
      (processMessageCall (Meter := Nat) env.chainId.toNat (systemMessage env target data)
        (.ofBlock block) Substate.empty).map fun out => ⟨out.state, out.output, out.error⟩ := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [systemCall, hpre, ↓reduceIte]
  cases processMessageCall (Meter := Nat) env.chainId.toNat (systemMessage env target data)
    (.ofBlock block) Substate.empty <;> rfl

/-- From Glamsterdam, a system call runs its message with the meter of EIP-8037. -/
theorem systemCall_of_glamsterdam (h : .glamsterdam ≤ fork) :
    systemCall env block target data =
      (processMessageCall (Meter := StateGasMeter) env.chainId.toNat (systemMessage env target data)
        (.ofBlock block) Substate.empty).map fun out => ⟨out.state, out.output, out.error⟩ := by
  simp only [systemCall, h, ↓reduceIte]
  cases processMessageCall (Meter := StateGasMeter) env.chainId.toNat
    (systemMessage env target data) (.ofBlock block) Substate.empty <;> rfl

private theorem processSystemMessage_empty (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (hfork : .paris ≤ fork) (hcode : codeAt block target = .ok .empty)
    (hpre : Precompiles.addedAt target.toU256.toNat = none) :
    (processMessageCall (Meter := Meter) env.chainId.toNat (systemMessage env target data)
      (.ofBlock block) Substate.empty).map (fun out =>
        SystemCallOutput.mk out.state out.output out.error) =
      .ok ⟨(State.TransactionState.ofBlock block).recordAccountRead target, .empty, none⟩ := by
  have hfirst := Transactions.prepareFirstFrame_of_value_eq_zero (Meter := Meter)
    (chainId := env.chainId.toNat) (message := systemMessage env target data)
    (state := .ofBlock block) (substate := Substate.empty) (paid := ∅) rfl rfl
    (EthLib.Base.mapError_ok_iff.mp hcode) (fun _ => Evm.delegatedAddress_empty)
  generalize hF : Transactions.FirstFrame.ofMeter (Meter := Meter) _ _ _ _ _ = first at hfirst
  have hstart : startState fork first.message first.state = first.state := by
    have hnot : ¬fork < .paris := Nat.not_lt.mpr hfork
    simp only [startState, hnot, ↓reduceIte]
  have hpre' : precompileAddress fork first.message = none := by
    subst hF
    simp [Transactions.FirstFrame.ofMeter, precompileAddress, systemMessage,
      Precompiles.isPrecompile, hpre]
  have hs : step fork (startFrame first.message first.state first.substate first.meter) =
      .ok (.next (advance { startFrame first.message first.state first.substate first.meter
        with running := false })) := by
    apply step_of_size_le
    subst hF
    exact Nat.le_refl 0
  have ran := runFrame_of_step_eq_next (runChild := Evm.Logic.processRunner fork first.message.gas)
    (decreases := step_decreases fork) (within := first.held) rfl hs
  rw [runFrame_of_running_eq_false rfl] at ran
  have hp := Evm.Logic.processMessage_map_val
    (state := first.state) (substate := first.substate) (meter := first.meter) (held := first.held)
    (result := .ok (advance { startFrame first.message first.state first.substate first.meter
      with running := false }))
    (by subst hF; simp [Transactions.FirstFrame.ofMeter, systemMessage]) hpre'
    (by simpa only [hstart] using ran)
  cases hc : processMessage fork first.message first.state first.substate first.meter
      first.held with
  | error e => rw [hc] at hp; cases hp
  | ok ended =>
    rw [hc] at hp
    have he := Except.ok.inj hp
    have ht : (systemMessage env target data).target = some target := rfl
    simp only [processMessageCall, hfirst, ht, hc, bind, Except.bind, pure,
      Except.pure, Except.map]
    rw [he]
    subst hF
    rfl

/-- From Paris, an unchecked call to empty code outside the precompiles succeeds without writes.

It returns no output and records only the read of its target, with either gas meter.

The code lookup must succeed: unavailable code is not empty code. -/
theorem systemCall_of_empty (hfork : .paris ≤ fork)
    (hcode : codeAt block target = .ok .empty)
    (hpre : Precompiles.addedAt target.toU256.toNat = none) :
    systemCall env block target data =
      .ok ⟨(State.TransactionState.ofBlock block).recordAccountRead target, .empty, none⟩ := by
  by_cases hglam : .glamsterdam ≤ fork
  · rw [systemCall_of_glamsterdam hglam]
    exact processSystemMessage_empty StateGasMeter hfork hcode hpre
  · rw [systemCall_of_lt_glamsterdam (Nat.lt_of_not_le hglam)]
    exact processSystemMessage_empty Nat hfork hcode hpre

/-- A checked system call to a contract with no code makes the block invalid. -/
theorem checkedSystemCall_of_size_eq_zero {code : ByteArray}
    (hCode : codeAt block target = .ok code) (hEmpty : code.size = 0) :
    checkedSystemCall env block target data = .error (.systemContractEmpty target) := by
  simp [checkedSystemCall, hCode, hEmpty, Except.mapError, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- A checked system call that succeeds calls a contract with code, and stops with no error. -/
theorem checkedSystemCall_ok {out : SystemCallOutput}
    (h : checkedSystemCall env block target data = .ok out) :
    (∃ code, codeAt block target = .ok code ∧ code.size ≠ 0) ∧
      systemCall env block target data = .ok out ∧ out.error = none := by
  unfold checkedSystemCall at h
  obtain ⟨code, hCode, h⟩ := bind_ok_iff.mp h
  by_cases hEmpty : code.size = 0
  · simp [hEmpty, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · simp only [hEmpty, ↓reduceIte] at h
    obtain ⟨call, hCall, h⟩ := bind_ok_iff.mp h
    cases hError : call.error with
    | some e => simp [hError, throw, throwThe, MonadExceptOf.throw] at h
    | none =>
      simp only [hError] at h
      cases h
      exact ⟨⟨code, mapError_ok_iff.mp hCode, hEmpty⟩, mapError_ok_iff.mp hCall, hError⟩

/-- A checked system call succeeds exactly when its contract has code and the call stops cleanly.

It then returns the output of the call. -/
theorem checkedSystemCall_eq_ok_iff {out : SystemCallOutput} :
    checkedSystemCall env block target data = .ok out ↔
      (∃ code, codeAt block target = .ok code ∧ code.size ≠ 0) ∧
        systemCall env block target data = .ok out ∧ out.error = none := by
  refine ⟨checkedSystemCall_ok, fun ⟨⟨code, hCode, hSize⟩, hCall, hError⟩ => ?_⟩
  simp [checkedSystemCall, hCode, hSize, hCall, hError, Except.mapError, bind, Except.bind, pure,
    Except.pure]

/-- A checked system call fails as an empty contract exactly when its contract has no code. -/
theorem checkedSystemCall_eq_systemContractEmpty_iff {address : Address} :
    checkedSystemCall env block target data = .error (.systemContractEmpty address) ↔
      address = target ∧ ∃ code, codeAt block target = .ok code ∧ code.size = 0 := by
  unfold checkedSystemCall
  cases hCode : codeAt block target with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok code =>
    by_cases hSize : code.size = 0
    · have hEmpty := ByteArray.size_eq_zero_iff.mp hSize
      simp [hEmpty, Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        eq_comm]
    · simp only [Except.mapError, bind, Except.bind, hSize, ↓reduceIte, Except.ok.injEq,
        exists_eq_left', and_false, iff_false]
      cases systemCall env block target data with
      | error e => simp
      | ok call =>
        simp only
        cases call.error <;> simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure]

/-- A checked system call fails with the error of its call exactly in one case.

Its contract has code, and the call stops with that error. -/
theorem checkedSystemCall_eq_systemCallFailed_iff {address : Address} {error : EvmError} :
    checkedSystemCall env block target data = .error (.systemCallFailed address error) ↔
      address = target ∧ (∃ code, codeAt block target = .ok code ∧ code.size ≠ 0) ∧
        ∃ out, systemCall env block target data = .ok out ∧ out.error = some error := by
  unfold checkedSystemCall
  cases hCode : codeAt block target with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok code =>
    by_cases hSize : code.size = 0
    · have hEmpty := ByteArray.size_eq_zero_iff.mp hSize
      simp [hEmpty, Except.mapError, bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw]
    · have hNe : code ≠ ByteArray.empty := fun h => hSize (ByteArray.size_eq_zero_iff.mpr h)
      simp only [Except.mapError, bind, Except.bind, hSize, ↓reduceIte, Except.ok.injEq,
        exists_eq_left']
      cases systemCall env block target data with
      | error e => simp
      | ok call =>
        simp only [Except.ok.injEq, exists_eq_left']
        cases call.error <;>
          simp [throw, throwThe, MonadExceptOf.throw, pure, Except.pure, eq_comm, hNe]

/-! ## A call that joins the body -/

/-- A call that joins the body is recorded by its builder.

Its writes join the block state, and the builder after the record is the new builder. -/
theorem BodyState.join_eq_ok {body body' : BodyState} {tx : State.TransactionState}
    (h : body.join tx = .ok body') :
    ∃ builder, body.builder.recordTransaction tx = .ok builder ∧
      body' = ⟨tx.incorporateTxIntoBlock.parent, builder⟩ := by
  unfold BodyState.join at h
  obtain ⟨b, hb, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨b, hb, rfl⟩

/-- Joining a call that only read its target keeps the block and records that address. -/
theorem BodyState.join_recordAccountRead (body : BodyState) (target : Address) :
    body.join ((State.TransactionState.ofBlock body.block).recordAccountRead target) =
      .ok { body with builder := body.builder.record target id } := by
  have hlist : ((∅ : Std.ExtTreeSet Address).insert target).toList = [target] := rfl
  simp [BodyState.join, AccessListBuilder.recordTransaction, State.TransactionState.ofBlock,
    State.TransactionState.recordAccountRead, State.TransactionState.incorporateTxIntoBlock,
    Std.ExtTreeMap.foldl_eq_foldl_toList, Std.ExtTreeMap.foldlM_eq_foldlM_toList,
    Std.ExtTreeSet.foldl_eq_foldl_toList, Std.ExtTreeMap.toList_eq_nil_iff.mpr,
    Std.ExtTreeSet.toList_eq_nil_iff.mpr, hlist,
    bind, Except.bind, pure, Except.pure]

/-! ## The calls at the start of a block -/

/-- The system calls at the start of a block pass through one body between the two calls.

From Dencun, the beacon roots contract runs on the body, and its call joins it to give that body.

Before Dencun, that body is the body at the start.

From Pectra, the history storage contract runs on that body, and its call joins it to give the end.

Before Pectra, the body at the end is that body. -/
theorem startSystemCalls_eq_ok {parentHash : Hash32} {body body' : BodyState}
    (h : startSystemCalls env parentHash body = .ok body') :
    ∃ mid : BodyState,
      (∀ hDencun : .dencun ≤ fork, ∃ out,
        systemCall env body.block BEACON_ROOTS_ADDRESS
          ⟨(env.parentBeaconBlockRoot hDencun).toArray⟩ = .ok out ∧
        body.join out.state = .ok mid) ∧
      (¬.dencun ≤ fork → mid = body) ∧
      (.pectra ≤ fork → ∃ out,
        systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩ = .ok out ∧
        mid.join out.state = .ok body') ∧
      (¬.pectra ≤ fork → body' = mid) := by
  -- The second call, from the body after the first.
  have second : ∀ mid : BodyState,
      (if Fork.pectra ≤ fork then do
          let out ← systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩
          (mid.join out.state).mapError EvmError.state
        else pure mid) = .ok body' →
      (.pectra ≤ fork → ∃ out,
        systemCall env mid.block HISTORY_STORAGE_ADDRESS ⟨parentHash.toArray⟩ = .ok out ∧
        mid.join out.state = .ok body') ∧
      (¬.pectra ≤ fork → body' = mid) := by
    intro mid h
    split at h
    · rename_i hPectra
      obtain ⟨out, hOut, hJoin⟩ := bind_ok_iff.mp h
      exact ⟨fun _ => ⟨out, hOut, mapError_ok_iff.mp hJoin⟩, fun h => absurd hPectra h⟩
    · rename_i hPectra
      exact ⟨fun h => absurd h hPectra, fun _ => (Except.ok.inj h).symm⟩
  unfold startSystemCalls at h
  dsimp only at h
  split at h
  · rename_i hDencun
    obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    exact ⟨mid, fun _ => ⟨out, hOut, mapError_ok_iff.mp hMid⟩, fun h => absurd hDencun h,
      second mid h⟩
  · rename_i hDencun
    obtain ⟨mid, hMid, h⟩ := bind_ok_iff.mp h
    cases hMid
    exact ⟨body, fun h => absurd h hDencun, fun _ => rfl, second _ h⟩

/-! ## The requests -/

/-- Reading a request contract with empty code rejects the block before joining any state. -/
theorem readRequest_of_empty {state : BodyState × List ByteArray} {contract : UInt8 × Address}
    (hcode : codeAt state.1.block contract.2 = .ok .empty) :
    readRequest env state contract = .error (.systemContractEmpty contract.2) := by
  simp [readRequest, checkedSystemCall_of_size_eq_zero hcode rfl, bind, Except.bind]

/-- The call to one request contract must succeed on the body so far, and then joins it.

Its requests follow those read so far. -/
theorem readRequest_eq_ok {state state' : BodyState × List ByteArray}
    {contract : UInt8 × Address} (h : readRequest env state contract = .ok state') :
    ∃ out, checkedSystemCall env state.1.block contract.2 .empty = .ok out ∧
      state.1.join out.state = .ok state'.1 ∧
      state'.2 = state.2 ++ requestList contract.1 out.output := by
  unfold readRequest at h
  obtain ⟨out, hOut, h⟩ := bind_ok_iff.mp h
  obtain ⟨body, hBody, h⟩ := bind_ok_iff.mp h
  cases h
  exact ⟨out, hOut, mapError_ok_iff.mp hBody, rfl⟩

/-- A list made by `requestList` holds its type byte first, then at least one byte. -/
theorem mem_requestList {type : UInt8} {r : ByteArray} (h : r ∈ requestList type data) :
    1 < r.size ∧ r.data[0]? = some type := by
  unfold requestList at h
  split at h
  · simp at h
  · rename_i hSize
    simp only [List.mem_singleton] at h
    subst h
    refine ⟨?_, ?_⟩
    · simp only [ByteArray.size_append]
      have : (⟨#[type]⟩ : ByteArray).size = 1 := rfl
      omega
    · rfl

/-- The requests that a fold over request contracts adds come in the order of the contracts. -/
theorem foldlM_requests {contracts : List (UInt8 × Address)} {start : BodyState × List ByteArray}
    {result : BodyState × List ByteArray}
    (h : contracts.foldlM (readRequest env) start = .ok result) :
    ∃ added, result.2 = start.2 ++ added ∧ (∀ r ∈ added, 1 < r.size) ∧
      (added.map (·.data[0]?)).Sublist ((contracts.map Prod.fst).map some) := by
  induction contracts generalizing start with
  | nil =>
    simp only [List.foldlM_nil] at h
    cases h
    exact ⟨[], by simp, by simp, by simp⟩
  | cons contract rest ih =>
    simp only [List.foldlM_cons] at h
    obtain ⟨next, hNext, hRest⟩ := bind_ok_iff.mp h
    obtain ⟨out, -, -, hNext⟩ := readRequest_eq_ok hNext
    obtain ⟨added, hAdded, hSize, hSub⟩ := ih hRest
    refine ⟨requestList contract.1 out.output ++ added, by simp [hAdded, hNext], ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · exact (mem_requestList hr).1
      · exact hSize r hr
    · simp only [List.map_append, List.map_cons]
      unfold requestList
      split
      · exact hSub.cons _
      · simp only [List.map_cons, List.map_nil, List.singleton_append]
        have : (⟨#[contract.1]⟩ ++ out.output : ByteArray).data[0]? = some contract.1 := rfl
        rw [this]
        exact hSub.cons_cons _

/-- Before Pectra, a block reads no request and its body is unchanged. -/
theorem readRequests_of_lt_pectra {body : BodyState} (h : fork < .pectra) :
    readRequests env body = .ok (body, []) := by
  unfold readRequests
  split
  · exact absurd ‹_› (Nat.not_le_of_lt h)
  · rfl

/-- From Pectra, a block calls each of its request contracts in turn, from no request. -/
theorem readRequests_of_pectra {body : BodyState} (h : .pectra ≤ fork) :
    readRequests env body = (requestContracts fork).foldlM (readRequest env) (body, []) := by
  simp only [readRequests, h, ↓reduceIte]

/-- The requests of a block have data, and come in the order of their types.

Withdrawals, of type 1, come before consolidations, of type 2.

From Glamsterdam, builder deposits, of type 3, then builder exits, of type 4, follow.

Each type comes at most once, and before Glamsterdam no builder type comes.
-/
theorem readRequests_requests {body : BodyState} {result : BodyState × List ByteArray}
    (h : readRequests env body = .ok result) :
    (∀ r ∈ result.2, 1 < r.size) ∧
      (result.2.map (·.data[0]?)).Sublist (((requestContracts fork).map Prod.fst).map some) := by
  by_cases hPectra : .pectra ≤ fork
  · rw [readRequests_of_pectra hPectra] at h
    obtain ⟨added, hAdded, hSize, hSub⟩ := foldlM_requests h
    simp only [List.nil_append] at hAdded
    rw [hAdded]
    exact ⟨hSize, hSub⟩
  · rw [readRequests_of_lt_pectra (Nat.lt_of_not_le hPectra)] at h
    cases h
    simp

/-- Up to BPO5, a block reads the withdrawal and consolidation requests only. -/
theorem requestContracts_types_of_lt_glamsterdam (h : fork < .glamsterdam) :
    (requestContracts fork).map Prod.fst =
      [WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE] := by
  have hpre : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [requestContracts, hpre, ↓reduceIte]
  rfl

/-- From Glamsterdam, a block reads the request types 1 to 4, in ascending order. -/
theorem requestContracts_types_of_glamsterdam (h : .glamsterdam ≤ fork) :
    (requestContracts fork).map Prod.fst = [1, 2, 3, 4] := by
  simp only [requestContracts, h, ↓reduceIte]
  rfl

/-- The requests of a block, after its transactions and withdrawals.

Before Pectra, the body stays as it was and there is no request.

From Pectra, the deposits come from the logs, and each request contract is called in turn.

The deposits come first, then the requests of the contracts. -/
theorem blockRequests_eq_ok {depositContract : Address} {body : BodyState} {logs : List Log}
    {result : BodyState × List ByteArray}
    (h : blockRequests depositContract env body logs = .ok result) :
    (¬.pectra ≤ fork → result = (body, [])) ∧
      (.pectra ≤ fork → ∃ deposits read,
        depositRequests depositContract logs = .ok deposits ∧
        (requestContracts fork).foldlM (readRequest env) (body, []) = .ok read ∧
        result = (read.1, requestList DEPOSIT_REQUEST_TYPE deposits ++ read.2)) := by
  unfold blockRequests at h
  refine ⟨fun hPectra => ?_, fun hPectra => ?_⟩
  · simp only [hPectra, ↓reduceIte] at h
    exact (Except.ok.inj h).symm
  · simp only [hPectra, ↓reduceIte] at h
    obtain ⟨deposits, hDeposits, h⟩ := bind_ok_iff.mp h
    obtain ⟨read, hRead, h⟩ := bind_ok_iff.mp h
    rw [readRequests_of_pectra hPectra] at hRead
    exact ⟨deposits, read, mapError_ok_iff.mp hDeposits, hRead, (Except.ok.inj h).symm⟩

/-- A failed request call prevents success, even if the deposits fail first. -/
theorem blockRequests_ne_ok_of_readRequests_error {depositContract : Address} {body : BodyState}
    {logs : List Log} {result : BodyState × List ByteArray} {error : BlockError}
    (hfork : .pectra ≤ fork) (hread : readRequests env body = .error error) :
    blockRequests depositContract env body logs ≠ .ok result := by
  intro h
  obtain ⟨_, read, _, hr, _⟩ := (blockRequests_eq_ok h).2 hfork
  rw [← readRequests_of_pectra hfork, hread] at hr
  cases hr

end EthLib.Execution.Blocks
