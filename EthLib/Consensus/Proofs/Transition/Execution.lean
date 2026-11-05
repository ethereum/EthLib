module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.Execution

/-!
# Proofs: the execution payload of a block

By default, the execution layer rejects a payload with a transaction of no bytes.

A block passes the payload step only when the execution layer accepts its payload request.

Once the merge is complete, and always from Capella, the payload extends the latest payload.

The state after the step differs from the state before only in the header of the latest payload.

That header is the header of the payload of the block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork}

/-- By default, the execution layer rejects a payload with a transaction of no bytes. -/
theorem verifyAndNotify_hasEmptyTransaction
    {isValidBlockHash notifyNewPayload : PayloadCheck preset fork}
    {isValidVersionedHashes : NewPayloadRequest preset fork → Bool}
    {request : NewPayloadRequest preset fork}
    (empty : request.executionPayload.hasEmptyTransaction = true) :
    verifyAndNotify isValidBlockHash isValidVersionedHashes notifyNewPayload request ≠
      .ok true := by
  unfold verifyAndNotify
  cases request.requestsList <;> simp [bind, Except.bind, pure, Except.pure, empty]

/-- By default, the execution layer accepts a request exactly when each of its checks passes. -/
theorem verifyAndNotify_ok_true_iff {isValidBlockHash notifyNewPayload : PayloadCheck preset fork}
    {isValidVersionedHashes : NewPayloadRequest preset fork → Bool}
    {request : NewPayloadRequest preset fork} :
    verifyAndNotify isValidBlockHash isValidVersionedHashes notifyNewPayload request = .ok true ↔
      ∃ requests, request.requestsList = .ok requests ∧
        request.executionPayload.hasEmptyTransaction = false ∧
        isValidBlockHash request.executionPayload request.parentBeaconBlockRoot requests ∧
        (.dencun ≤ fork → isValidVersionedHashes request) ∧
        notifyNewPayload request.executionPayload request.parentBeaconBlockRoot requests := by
  unfold verifyAndNotify
  cases h : request.requestsList with
  | error e => simp [bind, Except.bind]
  | ok requests =>
    simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq, Bool.and_eq_true,
      Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨⟨empty, hash⟩, hashes⟩, notified⟩
      exact ⟨requests, rfl, empty, hash, fun deneb => hashes.resolve_left (by
        exact Nat.not_lt_of_le deneb), notified⟩
    · rintro ⟨_, found, empty, hash, hashes, notified⟩
      cases found
      refine ⟨⟨⟨empty, hash⟩, ?_⟩, notified⟩
      by_cases deneb : .dencun ≤ fork
      · exact .inr (hashes deneb)
      · exact .inl (Nat.lt_of_not_le deneb)

/-- The default answer is the answer of an execution layer that does not change it. -/
theorem ExecutionEngine.verifyAndNotifyNewPayload_default
    (isValidBlockHash notifyNewPayload : PayloadCheck preset fork)
    (isValidVersionedHashes : NewPayloadRequest preset fork → Bool) :
    ({ isValidBlockHash, isValidVersionedHashes, notifyNewPayload } :
      ExecutionEngine preset fork).verifyAndNotifyNewPayload =
      verifyAndNotify isValidBlockHash isValidVersionedHashes notifyNewPayload :=
  rfl

/-- What a payload step that succeeds has checked, and the state it gives.

The execution layer accepted the payload request of the block.

The state after is the state before with the header of the payload as the latest one. -/
theorem processExecutionPayload_ok {config : Config} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    engine.verifyAndNotifyNewPayload (body.newPayloadRequest state bellatrix) = .ok true ∧
      ∃ header, (body.executionPayload bellatrix).header = .ok header ∧
        after = { state with latestExecutionPayloadHeader := fun _ => header } := by
  unfold processExecutionPayload at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, valid, accepted, _, isTrue, header, made, result⟩ :=
    computed
  subst isTrue
  exact ⟨accepted, header, made, (Except.ok.inj result).symm⟩

/-- Once the merge is complete, and always from Capella, an accepted payload extends the latest. -/
theorem processExecutionPayload_parentHash {config : Config} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after)
    (extends_ : .shapella ≤ fork ∨ isMergeTransitionComplete state bellatrix = true) :
    (body.executionPayload bellatrix).parentHash =
      (state.latestExecutionPayloadHeader bellatrix).blockHash := by
  unfold processExecutionPayload at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, parent, _⟩ := computed
  exact parent extends_

/-- An accepted payload reads the RANDAO mix of the current epoch and carries the slot's time. -/
theorem processExecutionPayload_randao_time {config : Config}
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    getRandaoMix state (getCurrentEpoch state) = .ok (body.executionPayload bellatrix).prevRandao ∧
      computeTimeAtSlot config state.genesisTime state.slot =
        .ok (body.executionPayload bellatrix).timestamp := by
  unfold processExecutionPayload at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftArith] at computed
  obtain ⟨_, _, mix, mixOk, _, isMix, time, timeOk, _, isTime, _⟩ := computed
  subst isMix isTime
  exact ⟨mixOk, mapError_ok_iff.mp timeOk⟩

/-- An execution layer that rejects every request makes every payload step fail. -/
theorem processExecutionPayload_constant_false {config : Config}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} :
    processExecutionPayload config (.constant false) state body bellatrix ≠ .ok after := fun ok =>
  nomatch (processExecutionPayload_ok ok).1

end EthLib.Consensus
