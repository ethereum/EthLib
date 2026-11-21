module

public import EthLib.Engine.Node
public import EthLib.Engine.Proofs.ForkchoiceUpdated
public import EthLib.Engine.Proofs.NewPayload

/-!
# Proofs: the steps of an execution node

Each step answers with the rule of its method, on a view of the node.

A payload on a known valid parent gets the answer of the method on the chain of that parent.

That chain has the parent as its last block, and the state after the parent.

A payload whose parent the node does not know as valid is syncing.

A payload that fails the checks before execution gets their answer, and the node does not change.

A valid payload is then known as valid, with the state after it.

So the next update, with it as the head, is not syncing.

A forkchoice update gives the response of the method on the tree of the known blocks.

It applies its forkchoice state exactly when it applies its head.

A request for a payload gives the answer of the method on the builds.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Blocks (RecentBlock)

namespace Node

variable {node : Node} {version : Nat} {params : Lean.Json}

/-! ## The views -/

/-- The tree holds the blocks that the node knows, each as the forkchoice update reads it. -/
theorem tree_lookup (node : Node) (hash : Hash32) :
    node.tree.lookup hash = (node.blocks.lookup hash).map (·.toKnownPayload) := by
  unfold tree
  induction node.blocks with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨key, b⟩ := entry
    by_cases hk : hash = key
    · subst hk
      simp [List.lookup]
    · have hne : (hash == key) = false := by simp [hk]
      simp [List.lookup, hne, ih]

/-- The chain that ends at a known block has that block last. -/
theorem recentTo_getLast? {hash : Hash32} {b : KnownBlock}
    (hb : node.blocks.lookup hash = some b) :
    (node.recentTo hash).getLast? = some b.block := by
  have ht : node.tree.lookup hash = some b.toKnownPayload := by
    rw [tree_lookup, hb]
    rfl
  have hAnc : ancestors node.tree 255 hash =
      hash :: ancestors node.tree 254 b.toKnownPayload.parentHash := by
    rw [show (255 : Nat) = 254 + 1 from rfl, ancestors, ht]
  rw [recentTo, hAnc, List.filterMap_cons, hb, List.getLast?_reverse]
  simp

/-- The chain that ends at a known block has that block last, the state given and the configuration.
-/
theorem chainAt_last {hash : Hash32} {b : KnownBlock} (post : Execution.State.State)
    (hb : node.blocks.lookup hash = some b) :
    (node.chainAt hash post).recent.getLast? = some b.block ∧
      (node.chainAt hash post).state = post ∧ (node.chainAt hash post).config = node.config :=
  ⟨recentTo_getLast? hb, rfl, rfl⟩

/-- A block with a state as a known valid block is a known block whose validity is valid. -/
theorem validState_eq_some_iff {hash : Hash32} {post : Execution.State.State} :
    node.validState hash = some post ↔
      ∃ b : KnownBlock, node.blocks.lookup hash = some b ∧ b.validity = .valid post := by
  unfold validState
  split
  · rename_i r p hr
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨_, hr, rfl⟩
    · rintro ⟨b, hb, hv⟩
      rw [hr] at hb
      cases hb
      cases hv
      rfl
  · rename_i hr
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro b hb hv
    obtain ⟨blk, pow, v⟩ := b
    cases hv
    exact hr blk pow post hb

/-! ## `engine_newPayload` -/

/-- A request that the checks refuse gets their error, and the node does not change. -/
theorem newPayloadStep_of_checkNewPayload_error {e : EngineError}
    (h : checkNewPayload node.config version params = .error e) :
    node.newPayloadStep version params = (.error e, node) := by
  simp [newPayloadStep, h]

/-- A payload that fails the checks gets their status and reason, and the node does not change.

The theorem on the checks gives that status: invalid, or an invalid block hash at version 1. -/
theorem newPayloadStep_of_checkNewPayload_invalid {status : PayloadStatus}
    {reason : PayloadError}
    (h : checkNewPayload node.config version params = .ok (.error (status, reason))) :
    node.newPayloadStep version params = (.ok (status, some reason), node) := by
  simp [newPayloadStep, h]

/-- A new payload on a parent that the node does not know as valid is syncing.

The node does not change. -/
theorem newPayloadStep_of_validState_eq_none {checked : CheckedBlock version} {hash : Hash32}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash) (hNew : node.blocks.lookup hash = none)
    (hParent : node.validState checked.block.header.parentHash = none) :
    node.newPayloadStep version params = (.ok (⟨.syncing, none⟩, none), node) := by
  simp [newPayloadStep, hCheck, hHash, hNew, hParent]

/-- A new payload on a known valid parent gets the answer of the method on the parent's chain.

That chain ends at the parent, with the state after it, by the theorem on the chain of a block.

The total difficulty is that of the parent, which only a parent of proof of work has. -/
theorem newPayloadStep_of_validState {checked : CheckedBlock version} {hash : Hash32}
    {post : Execution.State.State}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash) (hNew : node.blocks.lookup hash = none)
    (hParent : node.validState checked.block.header.parentHash = some post) :
    (node.newPayloadStep version params).1 =
      (fun r => (r.1, r.2.1)) <$> newPayloadOnChain node.transition
        (node.totalDifficulty checked.block.header.parentHash)
        (node.chainAt checked.block.header.parentHash post) version params := by
  simp only [newPayloadStep, hCheck, hHash, hNew, hParent]
  cases newPayloadOnChain node.transition (node.totalDifficulty checked.block.header.parentHash)
    (node.chainAt checked.block.header.parentHash post) version params <;> rfl

/-- A valid payload is known as valid after the step, and its hash is the latest valid hash.

The payload is one that passes the checks, with the hash of its block. -/
theorem validState_of_newPayloadStep {checked : CheckedBlock version} {hash : Hash32}
    {status : PayloadStatus} {reason : Option PayloadError} {next : Node}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hValid : status.status = .valid) :
    status.latestValidHash = some hash ∧ ∃ post, next.validState hash = some post := by
  simp only [newPayloadStep, hCheck, hHash] at h
  split at h
  · rename_i blk pow post hb
    simp only [Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨⟨rfl, -⟩, rfl⟩ := h
    exact ⟨rfl, post, validState_eq_some_iff.mpr ⟨_, hb, rfl⟩⟩
  · simp only [Prod.mk.injEq, Except.ok.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    cases hValid
  · split at h
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      cases hValid
    · rename_i post hParent
      split at h
      · simp at h
      · rename_i st re nx hOn
        simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, -⟩, rfl⟩ := h
        -- The method on the parent's chain reads the same checks, so it is the same block.
        unfold newPayloadOnChain at hOn
        simp only [show (node.chainAt checked.block.header.parentHash post).config =
          node.config from rfl, hCheck, bind, Except.bind] at hOn
        repeat' split at hOn
        all_goals simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hOn
        all_goals obtain ⟨rfl, -, rfl⟩ := hOn
        all_goals try (cases hValid; done)
        rename_i post' _
        refine ⟨by simp [hHash, Except.toOption], post', ?_⟩
        exact validState_eq_some_iff.mpr
          ⟨⟨⟨checked.fork, checked.block.header, []⟩, none, .valid post'⟩,
            by simp [recordExecution, record], rfl⟩

/-! ## `engine_forkchoiceUpdated` -/

/-- An update gives the response of the method on the tree and the finalized block of the node.
-/
theorem forkchoiceUpdatedStep_answer (node : Node) (version : Nat) (params : Lean.Json) :
    (node.forkchoiceUpdatedStep version params).1 = forkchoiceUpdatedResponse <$>
      forkchoiceUpdatedCall node.config node.transition version node.tree node.finalized params :=
  rfl

/-- An update that applies its head applies its forkchoice state, whatever its attributes give.
-/
theorem forkchoiceUpdatedStep_of_applied {state : ForkchoiceState} {attributes : Option Lean.Json}
    {status : PayloadStatus} {head : Hash32}
    (hParams : forkchoiceUpdatedParams version params = .ok (state, attributes))
    (hHead : Engine.forkchoiceUpdated node.transition node.tree node.finalized state =
      .ok (status, some head)) :
    (node.forkchoiceUpdatedStep version params).2 = node.applyForkchoice state := by
  simp [forkchoiceUpdatedStep, appliedState, hParams, hHead]

/-- An update that applies no head leaves the node as it was. -/
theorem forkchoiceUpdatedStep_of_not_applied
    (h : ∀ state attributes, forkchoiceUpdatedParams version params = .ok (state, attributes) →
      ∀ status head, Engine.forkchoiceUpdated node.transition node.tree node.finalized state ≠
        .ok (status, some head)) :
    (node.forkchoiceUpdatedStep version params).2 = node := by
  simp only [forkchoiceUpdatedStep, appliedState]
  split
  · rename_i state hs
    split at hs
    · rename_i st attributes hp
      split at hs
      · rename_i status head hf
        exact absurd hf (h st attributes hp status head)
      · cases hs
    · cases hs
  · rfl

/-- A payload that a step answers valid is not syncing in the next update, with it as the head.

The payload is one that passes the checks, with the hash of its block. -/
theorem forkchoiceUpdatedStep_ne_syncing_of_newPayloadStep {checked : CheckedBlock version}
    {hash : Hash32} {status : PayloadStatus} {reason : Option PayloadError} {next : Node}
    {version' : Nat} {params' : Lean.Json} {state : ForkchoiceState}
    {attributes : Option Lean.Json} {response : PayloadStatus × Option PayloadId}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hValid : status.status = .valid)
    (hParams : forkchoiceUpdatedParams version' params' = .ok (state, attributes))
    (hHead : state.headBlockHash = hash)
    (hAnswer : (next.forkchoiceUpdatedStep version' params').1 = .ok response) :
    response.1.status ≠ .syncing := by
  obtain ⟨-, post, hs⟩ := validState_of_newPayloadStep hCheck hHash h hValid
  obtain ⟨b, hb, -⟩ := validState_eq_some_iff.mp hs
  rw [forkchoiceUpdatedStep_answer] at hAnswer
  cases hCall : forkchoiceUpdatedCall next.config next.transition version' next.tree
    next.finalized params' with
  | error e => simp [hCall, Functor.map, Except.map] at hAnswer
  | ok r =>
    simp only [hCall, Functor.map, Except.map, Except.ok.injEq] at hAnswer
    subst hAnswer
    obtain ⟨state', _, st, hd, hp, hf, h1, -⟩ := forkchoiceUpdatedCall_ok_cases hCall
    rw [hParams] at hp
    cases hp
    rw [forkchoiceUpdatedResponse, h1, ne_eq, forkchoiceUpdated_syncing_iff hf, hHead,
      tree_lookup, hb]
    simp

/-! ## `engine_getPayload` -/

/-- A request for a payload gives the answer of the method on the builds, and the node as it was.
-/
theorem getPayloadStep_eq (node : Node) (setup : TrustedSetup) (version : Nat) (id : PayloadId) :
    node.getPayloadStep setup version id =
      (getPayload node.config setup node.store version id, node) :=
  rfl

end Node

end EthLib.Engine
