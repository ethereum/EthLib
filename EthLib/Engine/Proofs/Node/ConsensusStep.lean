module

public import EthLib.Consensus.Proofs.Transition.Execution
public import EthLib.Engine.Proofs.ConsensusRoute
public import EthLib.Engine.Proofs.Node
import EthLib.Execution.Proofs.Blocks.Transition

/-!
# Proofs: a payload that the beacon chain accepts on the chain of a node is valid on that node

The beacon chain's model of the execution layer is built from the chain of the node at its head.

From Bellatrix to Gloas, the node then answers valid to the JSON of the request.
-/

public section

namespace EthLib.Engine

open EthLib.Base

namespace Node

variable {preset : Consensus.Preset} {fork : Fork} {node : Node}

/-- The last block of the chain of a known valid block passes the terminal check if that block does.
-/
private theorem terminal_of_chainAt {parent : Hash32} {post : Execution.State.State}
    (hParent : node.validState parent = some post)
    -- Every parent from Paris on passes it, so only the first payload after the merge needs it.
    (hTerminal : ∀ b, node.blocks.lookup parent = some b →
      passesTerminalCheck node.transition (node.totalDifficulty parent) b.block = true) :
    ∀ last, (node.chainAt parent post).recent.getLast? = some last →
      passesTerminalCheck node.transition (node.totalDifficulty parent) last = true := by
  obtain ⟨b, hb, -⟩ := validState_eq_some_iff.mp hParent
  intro last hLast
  rw [(chainAt_last post hb).1, Option.some.injEq] at hLast
  rw [← hLast]
  exact hTerminal b hb

/-- From Bellatrix to Gloas, a request that the model accepts on the chain of the head is valid.

The parent of the payload is the valid head of the node, and it passes the terminal check.

The node does not know the payload as invalid.

The JSON of the request then exists, and the node answers valid, with the payload's block hash. -/
theorem newPayloadStep_valid_of_accepts {r : Consensus.NewPayloadRequest preset fork}
    {post : Execution.State.State}
    (hFork : .bellatrix ≤ fork ∧ fork < .hegota)
    (hParent : node.validState r.executionPayload.parentHash = some post)
    (hHead : r.executionPayload.parentHash = node.forkchoice.headBlockHash)
    -- Every parent from Paris on passes it, so only the first payload after the merge needs it.
    (hTerminal : ∀ b, node.blocks.lookup r.executionPayload.parentHash = some b →
      passesTerminalCheck node.transition (node.totalDifficulty r.executionPayload.parentHash)
        b.block = true)
    (hKnown : ∀ b, node.blocks.lookup r.executionPayload.blockHash = some b →
      b.validity ≠ .invalid)
    (hAccept : Consensus.ExecutionEngine.verifyAndNotifyNewPayload
      (executionEngine (node.chainAt r.executionPayload.parentHash post)) r = .ok true) :
    ∃ params, newPayloadRequestJson r (fun h => absurd h (Nat.not_le.mpr hFork.2)) = some params ∧
      (node.newPayloadStep (newPayloadVersion fork) params).1 =
        .ok (⟨.valid, some r.executionPayload.blockHash⟩, none) := by
  have hTerminal' := terminal_of_chainAt hParent hTerminal
  -- The chain route gives the JSON of the request, and a valid answer of the method on the chain.
  obtain ⟨params, ⟨status, reason, next⟩, hJson, hRun, hValid⟩ :=
    (newPayloadOnChain_valid_iff_accepts (fun h => absurd h (Nat.not_le.mpr hFork.2)) hFork
      hTerminal').mpr hAccept
  refine ⟨params, hJson, ?_⟩
  obtain ⟨block, post', rfl⟩ := (valid_iff_of_newPayloadOnChain hRun).mp hValid
  obtain ⟨-, checked, hCheck, hRunBlock, -⟩ := of_newPayloadOnChain_some hRun
  -- The chain of the node has the configuration of the node, so the node's checks pass too.
  replace hCheck : checkNewPayload node.config (newPayloadVersion fork) params =
      .ok (.ok checked) := hCheck
  -- The block of the checks extends the parent of the payload and has its block hash.
  obtain ⟨hParentHash, hHash⟩ := header_of_checkNewPayload hFork hJson hCheck
  -- On the chain, the answer is valid with the hash of the block as the latest valid hash.
  obtain ⟨-, -, hBlockCheck, -⟩ := Execution.Blocks.stateTransition_eq_ok hRunBlock
  obtain ⟨last, hLast, -, hLastHash⟩ := Execution.Blocks.checkBlock_link hBlockCheck
  have hOn := newPayloadOnChain_of_stateTransition_ok hCheck hLast hLastHash
    (hTerminal' _ hLast) hRunBlock
  -- The node runs the payload on the head, its parent, or knows it as valid.
  exact newPayloadStep_valid_of_newPayloadOnChain hCheck hHash (by rw [hParentHash]; exact hParent)
    (by rw [hParentHash]; exact hHead) hKnown (by rw [hParentHash]; exact hOn)

/-- From Bellatrix to Gloas, a payload new to a node is valid on it exactly when the model accepts.

The model is built from the chain of the head, which is the parent of the payload.

That parent passes the terminal check, and the node knows the payload at most as accepted. -/
theorem newPayloadStep_valid_iff_accepts {r : Consensus.NewPayloadRequest preset fork}
    {post : Execution.State.State}
    (hFork : .bellatrix ≤ fork ∧ fork < .hegota)
    (hParent : node.validState r.executionPayload.parentHash = some post)
    (hHead : r.executionPayload.parentHash = node.forkchoice.headBlockHash)
    -- Every parent from Paris on passes it, so only the first payload after the merge needs it.
    (hTerminal : ∀ b, node.blocks.lookup r.executionPayload.parentHash = some b →
      passesTerminalCheck node.transition (node.totalDifficulty r.executionPayload.parentHash)
        b.block = true)
    (hNew : ∀ b, node.blocks.lookup r.executionPayload.blockHash = some b →
      b.validity.isAccepted = true) :
    (∃ params answer,
        newPayloadRequestJson r (fun h => absurd h (Nat.not_le.mpr hFork.2)) = some params ∧
        (node.newPayloadStep (newPayloadVersion fork) params).1 = .ok answer ∧
        answer.1.status = .valid) ↔
      Consensus.ExecutionEngine.verifyAndNotifyNewPayload
        (executionEngine (node.chainAt r.executionPayload.parentHash post)) r = .ok true := by
  constructor
  · rintro ⟨params, answer, hJson, hStep, hValid⟩
    cases hCheck : checkNewPayload node.config (newPayloadVersion fork) params with
    | error e =>
      rw [newPayloadStep_of_checkNewPayload_error hCheck] at hStep
      cases hStep
    | ok result =>
      cases result with
      | error failure =>
        obtain ⟨status, reason⟩ := failure
        rw [newPayloadStep_of_checkNewPayload_invalid hCheck] at hStep
        cases hStep
        -- A payload that fails the checks is invalid, or has an invalid block hash.
        rcases (status_of_checkNewPayload hCheck).2 with hs | ⟨hs, -⟩ <;> rw [hs] at hValid <;>
          cases hValid
      | ok checked =>
        -- The block of the checks extends the head, so the node answers as the method on its chain.
        obtain ⟨hParentHash, hHash⟩ := header_of_checkNewPayload hFork hJson hCheck
        rw [newPayloadStep_of_head hCheck hHash hNew (by rw [hParentHash]; exact hParent)
          (by rw [hParentHash]; exact hHead), hParentHash] at hStep
        cases hOn : newPayloadOnChain node.transition
            (node.totalDifficulty r.executionPayload.parentHash)
            (node.chainAt r.executionPayload.parentHash post) (newPayloadVersion fork) params with
        | error e => simp [hOn, Functor.map, Except.map] at hStep
        | ok a =>
          simp only [hOn, Functor.map, Except.map, Except.ok.injEq] at hStep
          subst hStep
          exact (newPayloadOnChain_valid_iff_accepts _ hFork
            (terminal_of_chainAt hParent hTerminal)).mp ⟨params, a, hJson, hOn, hValid⟩
  · intro hAccept
    -- A payload that the node keeps at most as accepted is not known as invalid.
    have hKnown : ∀ b, node.blocks.lookup r.executionPayload.blockHash = some b →
        b.validity ≠ .invalid := fun b e hInvalid => by
      have accepted := hNew b e
      rw [hInvalid] at accepted
      cases accepted
    obtain ⟨params, hJson, hStep⟩ :=
      newPayloadStep_valid_of_accepts hFork hParent hHead hTerminal hKnown hAccept
    exact ⟨params, _, hJson, hStep, rfl⟩

/-- From Bellatrix, before Gloas, a payload step that passes on the chain of the head is valid.

The parent of the payload is the valid head of the node, and it passes the terminal check.

The node does not know the payload as invalid.

The JSON of the payload request of the block exists, and the node answers valid, with its hash. -/
theorem newPayloadStep_valid_of_processExecutionPayload {config : Consensus.Config}
    {state after : Consensus.BeaconState preset fork}
    {body : Consensus.BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam} {post : Execution.State.State}
    (hParent : node.validState (body.executionPayload bellatrix).parentHash = some post)
    (hHead : (body.executionPayload bellatrix).parentHash = node.forkchoice.headBlockHash)
    -- Every parent from Paris on passes it, so only the first payload after the merge needs it.
    (hTerminal : ∀ b, node.blocks.lookup (body.executionPayload bellatrix).parentHash = some b →
      passesTerminalCheck node.transition
        (node.totalDifficulty (body.executionPayload bellatrix).parentHash) b.block = true)
    (hKnown : ∀ b, node.blocks.lookup (body.executionPayload bellatrix).blockHash = some b →
      b.validity ≠ .invalid)
    (computed : Consensus.processExecutionPayload config
      (executionEngine (node.chainAt (body.executionPayload bellatrix).parentHash post))
      state body bellatrix = .ok after) :
    ∃ params, newPayloadRequestJson (body.newPayloadRequest state bellatrix)
        (fun h => absurd h (Nat.not_le.mpr (Nat.lt_trans bellatrix.2 (by decide)))) =
          some params ∧
      (node.newPayloadStep (newPayloadVersion fork) params).1 =
        .ok (⟨.valid, some (body.executionPayload bellatrix).blockHash⟩, none) :=
  -- A passing step means that the model on the chain of the head accepts the payload request.
  newPayloadStep_valid_of_accepts ⟨bellatrix.1, Nat.lt_trans bellatrix.2 (by decide)⟩ hParent
    hHead hTerminal hKnown (Consensus.processExecutionPayload_ok computed).1

end Node

end EthLib.Engine
