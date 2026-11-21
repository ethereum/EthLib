module

public import EthLib.Engine.Node
public import EthLib.Engine.Proofs.ForkchoiceUpdated
public import EthLib.Engine.Proofs.NewPayload

/-!
# Proofs: the steps of an execution node

Each step answers with the rule of its method, on a view of the node.

A payload on the valid head gets the answer of the method on the chain of the head.

That chain has the head as its last block, and the state after the head.

A payload on another known parent that is not invalid is accepted, with no latest valid hash.

That holds for a payload sent again too, and no other answer is accepted.

A payload whose parent is invalid is invalid, with the latest valid hash of the parent's chain.

A payload whose parent is unknown is syncing.

A payload that fails the checks before execution gets their answer, and the node does not change.

A valid payload is then known as valid, with the state after it.

So the next update, with it as the head, is not syncing.

A forkchoice update first validates the accepted blocks of the chain of its head.

A block on a parent found invalid is invalid too.

It keeps every valid block valid, and its forkchoice state as it was.

It then gives the response of the method on the tree of the known blocks.

On the validated node, it applies its forkchoice state exactly when it applies its head.

That head is then a block that the node knows as valid.

A request for a payload gives the answer of the method on the builds.

An update that answers a payload ID stores the build of its request, on the chain of its head.

Every step keeps each block that the node knows as valid or invalid, and the configuration.

So a request whose checks pass, once answered valid or invalid, gets that answer again later.

The checks before execution read the whole request, so they can still answer invalid for it.

An invalid block hash depends on the request and the configuration alone.
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

/-- The method on a chain never answers that a payload is accepted. -/
theorem status_ne_accepted_of_newPayloadOnChain {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : Execution.Blocks.BlockChain} {status : PayloadStatus}
    {reason : Option PayloadError} {next : Option (RecentBlock × Execution.State.State)}
    (h : newPayloadOnChain transition totalDifficulty chain version params =
      .ok (status, reason, next)) :
    status.status ≠ .accepted := by
  unfold newPayloadOnChain at h
  cases hC : checkNewPayload chain.config version params with
  | error e => simp [hC, bind, Except.bind] at h
  | ok r =>
    cases r with
    | error q =>
      obtain ⟨st, re⟩ := q
      simp only [hC, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      rcases (status_of_checkNewPayload hC).2 with hs | ⟨hs, -⟩ <;> simp [hs]
    | ok checked =>
      simp only [hC, bind, Except.bind] at h
      repeat' split at h
      all_goals simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      all_goals obtain ⟨rfl, -, -⟩ := h
      all_goals simp

/-- A run on a known valid parent answers what the method answers on the chain of that parent. -/
theorem executeOn_fst (node : Node) (hash : Hash32) (block : RecentBlock)
    (post : Execution.State.State) (version : Nat) (params : Lean.Json) :
    (node.executeOn hash block post version params).1 =
      (fun r => (r.1, r.2.1)) <$> newPayloadOnChain node.transition
        (node.totalDifficulty block.header.parentHash)
        (node.chainAt block.header.parentHash post) version params := by
  simp only [executeOn]
  cases newPayloadOnChain node.transition (node.totalDifficulty block.header.parentHash)
    (node.chainAt block.header.parentHash post) version params <;> rfl

/-- A payload that the node does not know as valid or invalid gets the answer that its parent gives.

That holds for a new payload and for one that the node keeps as accepted. -/
theorem newPayloadStep_of_fresh {checked : CheckedBlock version} {hash : Hash32}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (hNew : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true) :
    node.newPayloadStep version params =
      node.onParent hash ⟨checked.fork, checked.block.header, []⟩ version params := by
  cases hk : node.blocks.lookup hash with
  | none => simp [newPayloadStep, hCheck, hHash, hk]
  | some b =>
    obtain ⟨blk, pow, v⟩ := b
    have hv := hNew _ hk
    cases v with
    | accepted v' p' => simp [newPayloadStep, hCheck, hHash, hk]
    | _ => simp [Validity.isAccepted] at hv

/-- A payload whose parent is unknown is syncing, and the node does not change.

The payload is not one that the node knows as valid or invalid. -/
theorem newPayloadStep_syncing_of_unknown_parent {checked : CheckedBlock version} {hash : Hash32}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (hNew : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true)
    (hParent : node.blocks.lookup checked.block.header.parentHash = none) :
    node.newPayloadStep version params = (.ok (⟨.syncing, none⟩, none), node) := by
  rw [newPayloadStep_of_fresh hCheck hHash hNew]
  simp [onParent, hParent]

/-- A payload whose parent is invalid is invalid, and the node keeps it as invalid.

Its latest valid hash is the latest valid block of the parent's chain.

That hash is zero when that latest valid block is of proof of work.

The payload is not one that the node knows as valid or invalid. -/
theorem newPayloadStep_of_invalid_parent {checked : CheckedBlock version} {hash : Hash32}
    {parent : KnownBlock}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (hNew : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true)
    (hParent : node.blocks.lookup checked.block.header.parentHash = some parent)
    (hInvalid : parent.validity = .invalid) :
    node.newPayloadStep version params =
      (.ok (⟨.invalid, latestValidHash node.tree checked.block.header.parentHash⟩, none),
        node.record hash ⟨⟨checked.fork, checked.block.header, []⟩, none, .invalid⟩) := by
  rw [newPayloadStep_of_fresh hCheck hHash hNew]
  obtain ⟨blk, pow, v⟩ := parent
  simp only at hInvalid
  subst hInvalid
  simp [onParent, hParent]

/-- A payload on the valid head gets the answer of the method on the chain of the head.

That chain ends at the head, with the state after it, by the theorem on the chain of a block.

The total difficulty is that of the head, which only a block of proof of work has.

The payload is not one that the node knows as valid or invalid. -/
theorem newPayloadStep_of_head {checked : CheckedBlock version} {hash : Hash32}
    {post : Execution.State.State}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (hNew : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true)
    (hParent : node.validState checked.block.header.parentHash = some post)
    (hHead : checked.block.header.parentHash = node.forkchoice.headBlockHash) :
    (node.newPayloadStep version params).1 =
      (fun r => (r.1, r.2.1)) <$> newPayloadOnChain node.transition
        (node.totalDifficulty checked.block.header.parentHash)
        (node.chainAt checked.block.header.parentHash post) version params := by
  rw [newPayloadStep_of_fresh hCheck hHash hNew]
  obtain ⟨⟨blk, pow, v⟩, hb, hv⟩ := validState_eq_some_iff.mp hParent
  simp only at hv
  subst hv
  simp only [onParent, hb, ite_eq_left_of_eq_true _ _ (eq_true hHead)]
  exact executeOn_fst _ _ _ _ _ _

/-- A payload off the head, on a known parent that is not invalid, is accepted.

The parent is valid but not the head, or accepted itself.

The payload is not one that the node knows as valid or invalid.

The status has no latest valid hash, and the node keeps the payload as accepted, with its request.
-/
theorem newPayloadStep_of_not_head {checked : CheckedBlock version} {hash : Hash32}
    {b : KnownBlock}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (hNew : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true)
    (hParent : node.blocks.lookup checked.block.header.parentHash = some b)
    (hOff : (∃ post, b.validity = .valid post ∧
        checked.block.header.parentHash ≠ node.forkchoice.headBlockHash) ∨
      b.validity.isAccepted = true) :
    node.newPayloadStep version params = (.ok (⟨.accepted, none⟩, none),
      node.record hash
        ⟨⟨checked.fork, checked.block.header, []⟩, none, .accepted version params⟩) := by
  rw [newPayloadStep_of_fresh hCheck hHash hNew]
  obtain ⟨blk, pow, v⟩ := b
  rcases hOff with ⟨post, hv, hne⟩ | hv
  · simp only at hv
    subst hv
    simp [onParent, hParent, hne]
  · cases v with
    | accepted v' p' => simp [onParent, hParent]
    | _ => simp [Validity.isAccepted] at hv

/-- A payload is accepted, with no latest valid hash, exactly when its parent is off the head.

The parent is known and is not invalid: it is valid but not the head, or accepted itself.

The payload is not one that the node knows as valid or invalid. -/
theorem newPayloadStep_accepted_iff {checked : CheckedBlock version} {hash : Hash32}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (hNew : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true) :
    (node.newPayloadStep version params).1 = .ok (⟨.accepted, none⟩, none) ↔
      ∃ b, node.blocks.lookup checked.block.header.parentHash = some b ∧
        ((∃ post, b.validity = .valid post ∧
          checked.block.header.parentHash ≠ node.forkchoice.headBlockHash) ∨
        b.validity.isAccepted = true) := by
  constructor
  · intro h
    cases hb : node.blocks.lookup checked.block.header.parentHash with
    | none =>
      rw [newPayloadStep_syncing_of_unknown_parent hCheck hHash hNew hb] at h
      simp at h
    | some b =>
      refine ⟨b, rfl, ?_⟩
      obtain ⟨blk, pow, v⟩ := b
      cases v with
      | valid post =>
        by_cases hHead : checked.block.header.parentHash = node.forkchoice.headBlockHash
        · -- On the head the payload runs, and the method never answers accepted.
          have hp : node.validState checked.block.header.parentHash = some post :=
            validState_eq_some_iff.mpr ⟨_, hb, rfl⟩
          rw [newPayloadStep_of_head hCheck hHash hNew hp hHead] at h
          cases hOn : newPayloadOnChain node.transition
              (node.totalDifficulty checked.block.header.parentHash)
              (node.chainAt checked.block.header.parentHash post) version params with
          | error e => simp [hOn, Functor.map, Except.map] at h
          | ok r =>
            obtain ⟨st, re, nx⟩ := r
            simp only [hOn, Functor.map, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
            exact absurd (by rw [h.1]) (status_ne_accepted_of_newPayloadOnChain hOn)
        · exact .inl ⟨post, rfl, hHead⟩
      | invalid =>
        rw [newPayloadStep_of_invalid_parent hCheck hHash hNew hb rfl] at h
        simp at h
      | accepted v' p' => exact .inr rfl
  · rintro ⟨b, hb, hOff⟩
    rw [newPayloadStep_of_not_head hCheck hHash hNew hb hOff]

/-- Every accepted answer has no latest valid hash and no reason, whatever the payload. -/
theorem newPayloadStep_accepted {status : PayloadStatus} {reason : Option PayloadError}
    {next : Node} (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hs : status.status = .accepted) :
    status.latestValidHash = none ∧ reason = none := by
  unfold newPayloadStep at h
  cases hC : checkNewPayload node.config version params with
  | error e => simp [hC] at h
  | ok r =>
    cases r with
    | error q =>
      obtain ⟨st, re⟩ := q
      simp only [hC, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      rcases (status_of_checkNewPayload hC).2 with h' | ⟨h', -⟩ <;> rw [h'] at hs <;> cases hs
    | ok checked =>
      simp only [hC] at h
      split at h
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        cases hs
      · split at h
        · simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨⟨rfl, -⟩, -⟩ := h
          cases hs
        · simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨⟨rfl, -⟩, -⟩ := h
          cases hs
        · dsimp only [onParent] at h
          split at h
          · split at h
            · simp only [executeOn] at h
              split at h
              · simp at h
              · rename_i st re nx hOn
                simp only [Prod.mk.injEq, Except.ok.injEq] at h
                obtain ⟨⟨rfl, rfl⟩, -⟩ := h
                exact absurd hs (status_ne_accepted_of_newPayloadOnChain hOn)
            · simp only [Prod.mk.injEq, Except.ok.injEq] at h
              obtain ⟨⟨rfl, rfl⟩, -⟩ := h
              exact ⟨rfl, rfl⟩
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, rfl⟩, -⟩ := h
            exact ⟨rfl, rfl⟩
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs

/-- A valid payload is known as valid after the step, and its hash is the latest valid hash.

The payload is one that passes the checks, with the hash of its block. -/
theorem validState_of_newPayloadStep {checked : CheckedBlock version} {hash : Hash32}
    {status : PayloadStatus} {reason : Option PayloadError} {next : Node}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hValid : status.status = .valid) :
    status.latestValidHash = some hash ∧ ∃ post, next.validState hash = some post := by
  by_cases hFresh : ∀ b, node.blocks.lookup hash = some b → b.validity.isAccepted = true
  · rw [newPayloadStep_of_fresh hCheck hHash hFresh] at h
    cases hb : node.blocks.lookup checked.block.header.parentHash with
    | none =>
      simp only [onParent, hb, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      cases hValid
    | some b =>
      obtain ⟨blk, pow, v⟩ := b
      cases v with
      | invalid =>
        simp only [onParent, hb, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        cases hValid
      | accepted v' p' =>
        simp only [onParent, hb, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        cases hValid
      | valid post =>
        by_cases hHead : checked.block.header.parentHash = node.forkchoice.headBlockHash
        · simp only [onParent, hb, ite_eq_left_of_eq_true _ _ (eq_true hHead), executeOn] at h
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
        · simp only [onParent, hb, hHead, ↓reduceIte, Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨⟨rfl, -⟩, -⟩ := h
          cases hValid
  · simp only [Classical.not_forall] at hFresh
    obtain ⟨⟨blk, pow, v⟩, hk, hv⟩ := hFresh
    cases v with
    | valid post =>
      simp only [newPayloadStep, hCheck, hHash, hk, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, rfl⟩ := h
      exact ⟨rfl, post, validState_eq_some_iff.mpr ⟨_, hk, rfl⟩⟩
    | invalid =>
      simp only [newPayloadStep, hCheck, hHash, hk, Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      cases hValid
    | accepted v' p' => simp [Validity.isAccepted] at hv

/-! ## Validation of the chain of a head -/

/-- A run keeps the forkchoice state and the known finalized block of the node. -/
theorem executeOn_forkchoice (node : Node) (hash : Hash32) (block : RecentBlock)
    (post : Execution.State.State) (version : Nat) (params : Lean.Json) :
    (node.executeOn hash block post version params).2.forkchoice = node.forkchoice ∧
      (node.executeOn hash block post version params).2.finalized = node.finalized := by
  simp only [executeOn]
  split
  · exact ⟨rfl, rfl⟩
  · simp only [recordExecution]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- A run keeps the configuration of the transition. -/
theorem executeOn_transition (node : Node) (hash : Hash32) (block : RecentBlock)
    (post : Execution.State.State) (version : Nat) (params : Lean.Json) :
    (node.executeOn hash block post version params).2.transition = node.transition := by
  simp only [executeOn]
  split
  · rfl
  · simp only [recordExecution]
    split
    · rfl
    · split <;> rfl

/-- Validation keeps the configuration of the transition. -/
theorem validateChain_transition (node : Node) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).transition = node.transition := by
  induction fuel generalizing node hash with
  | zero => rfl
  | succ fuel ih =>
    simp only [validateChain]
    split
    · rename_i block pow version params hb
      split
      · rw [executeOn_transition, ih]
      · exact ih _ _
      · exact ih _ _
    · rfl

/-- The validation of an update keeps the configuration of the transition. -/
theorem validateHead_transition (node : Node) (version : Nat) (params : Lean.Json) :
    (node.validateHead version params).transition = node.transition := by
  simp only [validateHead]
  split
  · exact validateChain_transition _ _ _
  · rfl

/-- Recording a block keeps every other known block as it was. -/
theorem record_lookup_of_ne {hash other : Hash32} (node : Node) (b : KnownBlock)
    (hne : other ≠ hash) : (node.record hash b).blocks.lookup other = node.blocks.lookup other := by
  have hb : (other == hash) = false := by simp [hne]
  simp [record, List.lookup, hb]

/-- A run keeps every other known block as it was. -/
theorem executeOn_lookup_of_ne {hash other : Hash32} (node : Node) (block : RecentBlock)
    (post : Execution.State.State) (version : Nat) (params : Lean.Json) (hne : other ≠ hash) :
    (node.executeOn hash block post version params).2.blocks.lookup other =
      node.blocks.lookup other := by
  simp only [executeOn]
  split
  · rfl
  · simp only [recordExecution]
    split
    · exact record_lookup_of_ne _ _ hne
    · split
      · exact record_lookup_of_ne _ _ hne
      · rfl

/-- Validation keeps the forkchoice state and the known finalized block of the node. -/
theorem validateChain_forkchoice (node : Node) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).forkchoice = node.forkchoice ∧
      (node.validateChain fuel hash).finalized = node.finalized := by
  induction fuel generalizing node hash with
  | zero => exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    simp only [validateChain]
    split
    · rename_i block pow version params hb
      obtain ⟨h1, h2⟩ := ih node block.header.parentHash
      split
      · rename_i post hp
        obtain ⟨e1, e2⟩ := executeOn_forkchoice (node.validateChain fuel block.header.parentHash)
          hash block post version params
        exact ⟨e1.trans h1, e2.trans h2⟩
      · exact ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
    · exact ⟨rfl, rfl⟩

/-- Validation keeps each known block that is not accepted as it was. -/
theorem validateChain_lookup {node : Node} {fuel : Nat} {hash other : Hash32} {b : KnownBlock}
    (h : node.blocks.lookup other = some b) (hb : b.validity.isAccepted = false) :
    (node.validateChain fuel hash).blocks.lookup other = some b := by
  induction fuel generalizing node hash with
  | zero => exact h
  | succ fuel ih =>
    simp only [validateChain]
    split
    · rename_i block pow version params hk
      have hInner := ih (hash := block.header.parentHash) h
      -- Validation records only the accepted block, which is not this one.
      have hne : other ≠ hash := by
        rintro rfl
        rw [hk] at h
        cases h
        simp [Validity.isAccepted] at hb
      split
      · rw [executeOn_lookup_of_ne _ _ _ _ _ hne, hInner]
      · rw [record_lookup_of_ne _ _ hne, hInner]
      · exact hInner
    · exact h

/-- Validation keeps each valid block of the node valid, with the same state after it. -/
theorem validateChain_validState {node : Node} {fuel : Nat} {hash other : Hash32}
    {post : Execution.State.State} (h : node.validState other = some post) :
    (node.validateChain fuel hash).validState other = some post := by
  obtain ⟨b, hb, hv⟩ := validState_eq_some_iff.mp h
  exact validState_eq_some_iff.mpr
    ⟨b, validateChain_lookup hb (by simp [hv, Validity.isAccepted]), hv⟩

/-- The validation of an update keeps the forkchoice state and the known finalized block. -/
theorem validateHead_forkchoice (node : Node) (version : Nat) (params : Lean.Json) :
    (node.validateHead version params).forkchoice = node.forkchoice ∧
      (node.validateHead version params).finalized = node.finalized := by
  simp only [validateHead]
  split
  · exact validateChain_forkchoice _ _ _
  · exact ⟨rfl, rfl⟩

/-- The validation of an update keeps each known block that is not accepted as it was. -/
theorem validateHead_lookup {hash : Hash32} {b : KnownBlock}
    (h : node.blocks.lookup hash = some b) (hb : b.validity.isAccepted = false) :
    (node.validateHead version params).blocks.lookup hash = some b := by
  simp only [validateHead]
  split
  · exact validateChain_lookup h hb
  · exact h

/-- The validation of an update keeps each valid block of the node valid. -/
theorem validateHead_validState {hash : Hash32} {post : Execution.State.State}
    (h : node.validState hash = some post) :
    (node.validateHead version params).validState hash = some post := by
  simp only [validateHead]
  split
  · exact validateChain_validState h
  · exact h

/-! ## `engine_forkchoiceUpdated` -/

/-- An update gives the response of the method on the tree and the finalized block of the node.

The node is the one after the validation of the chain of the head.

The head is not one that the node still knows as accepted. -/
theorem forkchoiceUpdatedStep_answer (node : Node) (version : Nat) (params : Lean.Json)
    (h : (node.validateHead version params).headAccepted version params = false) :
    (node.forkchoiceUpdatedStep version params).1 = forkchoiceUpdatedResponse <$>
      forkchoiceUpdatedCall (node.validateHead version params).config
        (node.validateHead version params).transition version
        (node.validateHead version params).tree (node.validateHead version params).finalized
        params := by
  simp only [forkchoiceUpdatedStep, h]
  rfl

/-- An update whose head the node still knows as accepted after validation is syncing.

It applies nothing. -/
theorem forkchoiceUpdatedStep_of_headAccepted (node : Node) (version : Nat) (params : Lean.Json)
    (h : (node.validateHead version params).headAccepted version params = true) :
    node.forkchoiceUpdatedStep version params =
      (.ok (⟨.syncing, none⟩, none), node.validateHead version params) := by
  simp [forkchoiceUpdatedStep, h]

/-- An update on a validated node gives the response of the method on its tree. -/
theorem updateStep_answer (node : Node) (version : Nat) (params : Lean.Json) :
    (node.updateStep version params).1 = forkchoiceUpdatedResponse <$>
      forkchoiceUpdatedCall node.config node.transition version node.tree node.finalized params :=
  rfl

/-- An update that applies its head applies its forkchoice state, whatever its attributes give.
-/
theorem updateStep_of_applied {state : ForkchoiceState} {attributes : Option Lean.Json}
    {status : PayloadStatus} {head : Hash32}
    (hParams : forkchoiceUpdatedParams version params = .ok (state, attributes))
    (hHead : Engine.forkchoiceUpdated node.transition node.tree node.finalized state =
      .ok (status, some head)) :
    (node.updateStep version params).2 = node.applyForkchoice state := by
  simp [updateStep, appliedState, hParams, hHead]

/-- An update that applies no head leaves the node as it was. -/
theorem updateStep_of_not_applied
    (h : ∀ state attributes, forkchoiceUpdatedParams version params = .ok (state, attributes) →
      ∀ status head, Engine.forkchoiceUpdated node.transition node.tree node.finalized state ≠
        .ok (status, some head)) :
    (node.updateStep version params).2 = node := by
  simp only [updateStep, appliedState]
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

/-- An update applies its forkchoice state when it applies its head, after the validation.

The head of the request is not one that the node still knows as accepted after it. -/
theorem forkchoiceUpdatedStep_of_applied {state : ForkchoiceState}
    {attributes : Option Lean.Json} {status : PayloadStatus} {head : Hash32}
    (hNot : (node.validateHead version params).headAccepted version params = false)
    (hParams : forkchoiceUpdatedParams version params = .ok (state, attributes))
    (hHead : Engine.forkchoiceUpdated (node.validateHead version params).transition
      (node.validateHead version params).tree (node.validateHead version params).finalized state =
      .ok (status, some head)) :
    (node.forkchoiceUpdatedStep version params).2 =
      (node.validateHead version params).applyForkchoice state := by
  simp only [forkchoiceUpdatedStep, hNot, Bool.false_eq_true, ↓reduceIte]
  exact updateStep_of_applied hParams hHead

/-- An update to a head that the node knows as invalid is invalid, and applies nothing.

Its latest valid hash is the latest valid block of the chain of the head.

That hash is zero when that latest valid block is of proof of work.

The chain of the head must pass the terminal block check. -/
theorem forkchoiceUpdatedStep_of_invalid_head {state : ForkchoiceState}
    {attributes : Option Lean.Json} {b : KnownBlock}
    (hParams : forkchoiceUpdatedParams version params = .ok (state, attributes))
    (hb : node.blocks.lookup state.headBlockHash = some b) (hInvalid : b.validity = .invalid)
    (hTerminal : chainPassesTerminalCheck node.transition (node.validateHead version params).tree
      state.headBlockHash = true) :
    node.forkchoiceUpdatedStep version params =
      (.ok (⟨.invalid, latestValidHash (node.validateHead version params).tree
        state.headBlockHash⟩, none), node.validateHead version params) := by
  have hb' := validateHead_lookup (version := version) (params := params) hb
    (by simp [hInvalid, Validity.isAccepted])
  have hNot : (node.validateHead version params).headAccepted version params = false := by
    simp [headAccepted, hParams, hb', hInvalid, Validity.isAccepted]
  have hTree : (node.validateHead version params).tree.lookup state.headBlockHash =
      some b.toKnownPayload := by
    rw [tree_lookup, hb']
    rfl
  have hf := forkchoiceUpdated_of_invalid
    (finalized := (node.validateHead version params).finalized) hTree
    (by simp [KnownBlock.toKnownPayload, hInvalid, Validity.isValid]) hTerminal
  rw [← validateHead_transition node version params] at hf
  simp [forkchoiceUpdatedStep, hNot, updateStep, appliedState, forkchoiceUpdatedCall, hParams, hf,
    bind, Except.bind, pure, Except.pure, forkchoiceUpdatedResponse, Functor.map, Except.map]

/-- An update either keeps the forkchoice state of the node, or makes a valid block its head.

So the node never applies a head that has not run and passed. -/
theorem forkchoiceUpdatedStep_head_valid (node : Node) (version : Nat) (params : Lean.Json) :
    (node.forkchoiceUpdatedStep version params).2.forkchoice = node.forkchoice ∨
      ∃ b, (node.forkchoiceUpdatedStep version params).2.blocks.lookup
        (node.forkchoiceUpdatedStep version params).2.forkchoice.headBlockHash = some b ∧
        b.validity.isValid = true := by
  have hKeep := (validateHead_forkchoice node version params).1
  simp only [forkchoiceUpdatedStep]
  split
  · exact .inl hKeep
  · simp only [updateStep, appliedState]
    split
    · rename_i state hs
      split at hs
      · rename_i st attributes hp
        split at hs
        · rename_i status head hf
          cases hs
          obtain ⟨rfl, p, hp', hv⟩ := valid_of_forkchoiceUpdated hf
          rw [tree_lookup] at hp'
          obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hp'
          exact .inr ⟨b, hb, hv⟩
        · cases hs
      · cases hs
    · exact .inl hKeep

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
  have hs' := validateHead_validState (version := version') (params := params') hs
  obtain ⟨b, hb, hv⟩ := validState_eq_some_iff.mp hs'
  have hNot : (next.validateHead version' params').headAccepted version' params' = false := by
    simp [headAccepted, hParams, hHead, hb, hv, Validity.isAccepted]
  rw [forkchoiceUpdatedStep_answer _ _ _ hNot] at hAnswer
  cases hCall : forkchoiceUpdatedCall (next.validateHead version' params').config
    (next.validateHead version' params').transition version'
    (next.validateHead version' params').tree (next.validateHead version' params').finalized
    params' with
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

/-! ## Validation is idempotent -/

/-- The method on a chain whose checks pass never answers an invalid block hash. -/
theorem status_ne_invalidBlockHash_of_newPayloadOnChain {transition : TransitionConfiguration}
    {totalDifficulty : Nat} {chain : Execution.Blocks.BlockChain} {checked : CheckedBlock version}
    {status : PayloadStatus} {reason : Option PayloadError}
    {next : Option (RecentBlock × Execution.State.State)}
    (hCheck : checkNewPayload chain.config version params = .ok (.ok checked))
    (h : newPayloadOnChain transition totalDifficulty chain version params =
      .ok (status, reason, next)) :
    status.status ≠ .invalidBlockHash := by
  unfold newPayloadOnChain at h
  simp only [hCheck, bind, Except.bind] at h
  repeat' split at h
  all_goals simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, -, -⟩ := h
  all_goals simp

/-- A payload that the node knows as valid is valid again, with its own hash.

The node does not change. -/
theorem newPayloadStep_of_known_valid {checked : CheckedBlock version} {hash : Hash32}
    {b : KnownBlock} {post : Execution.State.State}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash) (hb : node.blocks.lookup hash = some b)
    (hValid : b.validity = .valid post) :
    node.newPayloadStep version params = (.ok (⟨.valid, some hash⟩, none), node) := by
  obtain ⟨blk, pow, v⟩ := b
  simp only at hValid
  subst hValid
  simp [newPayloadStep, hCheck, hHash, hb]

/-- A payload that the node knows as invalid is invalid again.

Its latest valid hash is the latest valid block of its chain.

The node does not change. -/
theorem newPayloadStep_of_known_invalid {checked : CheckedBlock version} {hash : Hash32}
    {b : KnownBlock}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash) (hb : node.blocks.lookup hash = some b)
    (hInvalid : b.validity = .invalid) :
    node.newPayloadStep version params =
      (.ok (⟨.invalid, latestValidHash node.tree hash⟩, none), node) := by
  obtain ⟨blk, pow, v⟩ := b
  simp only at hInvalid
  subst hInvalid
  simp [newPayloadStep, hCheck, hHash, hb]

/-- The answer by the parent records only the payload, so it keeps every other known block. -/
theorem onParent_lookup {hash other : Hash32} {block : RecentBlock} {b : KnownBlock}
    (hne : other ≠ hash) (h : node.blocks.lookup other = some b) :
    (node.onParent hash block version params).2.blocks.lookup other = some b := by
  simp only [onParent]
  split
  · split
    · rw [executeOn_lookup_of_ne _ _ _ _ _ hne, h]
    · rw [record_lookup_of_ne _ _ hne, h]
  · rw [record_lookup_of_ne _ _ hne, h]
  · rw [record_lookup_of_ne _ _ hne, h]
  · exact h

/-- A step of `engine_newPayload` keeps every known block that is not accepted as it was.

So a block known as valid stays valid, with the same state, and one known as invalid stays invalid.
-/
theorem newPayloadStep_lookup {other : Hash32} {b : KnownBlock}
    (h : node.blocks.lookup other = some b) (hb : b.validity.isAccepted = false) :
    (node.newPayloadStep version params).2.blocks.lookup other = some b := by
  cases hCheck : checkNewPayload node.config version params with
  | error e => simp [newPayloadStep, hCheck, h]
  | ok r =>
    cases r with
    | error q => simp [newPayloadStep, hCheck, h]
    | ok checked =>
      cases hHash : checked.block.header.hash with
      | error e => simp [newPayloadStep, hCheck, hHash, h]
      | ok hash =>
        by_cases hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true
        · rw [newPayloadStep_of_fresh hCheck hHash hFresh]
          -- The payload is new or accepted, and the block here is neither, so they differ.
          have hne : other ≠ hash := by
            rintro rfl
            rw [hFresh b h] at hb
            cases hb
          exact onParent_lookup hne h
        · simp only [Classical.not_forall] at hFresh
          obtain ⟨⟨blk, pow, v⟩, hk, hv⟩ := hFresh
          cases v with
          | valid post => rw [newPayloadStep_of_known_valid hCheck hHash hk rfl]; exact h
          | invalid => rw [newPayloadStep_of_known_invalid hCheck hHash hk rfl]; exact h
          | accepted v' p' => simp [Validity.isAccepted] at hv

/-- A step of `engine_forkchoiceUpdated` keeps every known block that is not accepted as it was.
-/
theorem forkchoiceUpdatedStep_lookup {other : Hash32} {b : KnownBlock}
    (h : node.blocks.lookup other = some b) (hb : b.validity.isAccepted = false) :
    (node.forkchoiceUpdatedStep version params).2.blocks.lookup other = some b := by
  have hv := validateHead_lookup (version := version) (params := params) h hb
  simp only [forkchoiceUpdatedStep]
  split
  · exact hv
  · simp only [updateStep]
    split <;> exact hv

/-! ## Builds -/

/-- Storing a build keeps the known blocks, the configuration and the forkchoice state. -/
theorem storeBuild_keeps (node : Node) (builder : Builder) (version : Nat) (params : Lean.Json)
    (id : PayloadId) :
    (node.storeBuild builder version params id).blocks = node.blocks ∧
      (node.storeBuild builder version params id).config = node.config ∧
      (node.storeBuild builder version params id).forkchoice = node.forkchoice := by
  simp only [storeBuild]
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- An update that builds gives the response of the update. -/
theorem forkchoiceUpdatedBuildStep_answer (node : Node) (builder : Builder) (version : Nat)
    (params : Lean.Json) :
    (node.forkchoiceUpdatedBuildStep builder version params).1 =
      (node.forkchoiceUpdatedStep version params).1 := by
  simp only [forkchoiceUpdatedBuildStep]
  split <;> simp_all

/-- An update that builds keeps what the update gives, apart from the builds. -/
theorem forkchoiceUpdatedBuildStep_keeps (node : Node) (builder : Builder) (version : Nat)
    (params : Lean.Json) :
    (node.forkchoiceUpdatedBuildStep builder version params).2.blocks =
        (node.forkchoiceUpdatedStep version params).2.blocks ∧
      (node.forkchoiceUpdatedBuildStep builder version params).2.config =
        (node.forkchoiceUpdatedStep version params).2.config ∧
      (node.forkchoiceUpdatedBuildStep builder version params).2.forkchoice =
        (node.forkchoiceUpdatedStep version params).2.forkchoice := by
  simp only [forkchoiceUpdatedBuildStep]
  split
  · rename_i status id next h
    rw [h]
    exact storeBuild_keeps _ _ _ _ _
  · exact ⟨rfl, rfl, rfl⟩

/-- A run keeps the builds. -/
theorem executeOn_builds (node : Node) (hash : Hash32) (block : RecentBlock)
    (post : Execution.State.State) (version : Nat) (params : Lean.Json) :
    (node.executeOn hash block post version params).2.builds = node.builds := by
  simp only [executeOn]
  split
  · rfl
  · simp only [recordExecution]
    split
    · rfl
    · split <;> rfl

/-- Validation keeps the builds. -/
theorem validateChain_builds (node : Node) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).builds = node.builds := by
  induction fuel generalizing node hash with
  | zero => rfl
  | succ fuel ih =>
    simp only [validateChain]
    split
    · split
      · rw [executeOn_builds, ih]
      · exact ih _ _
      · exact ih _ _
    · rfl

/-- An update keeps the builds. -/
theorem forkchoiceUpdatedStep_builds (node : Node) (version : Nat) (params : Lean.Json) :
    (node.forkchoiceUpdatedStep version params).2.builds = node.builds := by
  have hv : (node.validateHead version params).builds = node.builds := by
    simp only [validateHead]
    split
    · exact validateChain_builds _ _ _
    · rfl
  simp only [forkchoiceUpdatedStep]
  split
  · exact hv
  · simp only [updateStep]
    split <;> exact hv

/-- A stored build stays, so a second update with the same payload ID keeps it.

Step 6 of payload building asks that a build of the same attributes not restart. -/
theorem forkchoiceUpdatedBuildStep_store_of_some {builder : Builder} {id : PayloadId}
    {stored : StoredPayload} (h : node.store id = some stored) :
    (node.forkchoiceUpdatedBuildStep builder version params).2.store id = some stored := by
  have hs : (node.forkchoiceUpdatedStep version params).2.store id = some stored := by
    simp only [store, forkchoiceUpdatedStep_builds]
    exact h
  simp only [forkchoiceUpdatedBuildStep]
  split
  · rename_i status id' next hStep
    rw [hStep] at hs
    simp only [storeBuild]
    split
    · exact hs
    · by_cases hid : id = id'
      · subst hid
        rename_i hNone
        simp [store] at hs
        simp [hs] at hNone
      · have hb : (id == id') = false := by simp [hid]
        repeat' split
        all_goals first
          | exact hs
          | simp [store, List.lookup, hb] at hs ⊢; exact hs
  · rename_i hNot
    exact hs

/-- An update that answers a payload ID, with no build under it, stores the build of its request.

The build runs on the chain of the head of the request, a valid block of the node after the update.

It uses the attributes as the version decodes them, and the builder of the node.

So the theorems on a build on a chain apply to the stored build. -/
theorem store_of_forkchoiceUpdatedBuildStep {builder : Builder} {status : PayloadStatus}
    {pid : PayloadId} {next : Node} {stored : StoredPayload}
    (hStep : node.forkchoiceUpdatedBuildStep builder version params =
      (.ok (status, some pid), next))
    (hNone : node.builds.lookup pid = none) (hStored : next.store pid = some stored) :
    ∃ state j decoded post b, forkchoiceUpdatedParams version params = .ok (state, some j) ∧
      payloadAttributesOfVersion version j = .ok decoded ∧
      (node.forkchoiceUpdatedStep version params).2.blocks.lookup state.headBlockHash = some b ∧
      b.validity = .valid post ∧
      ((node.forkchoiceUpdatedStep version params).2.chainAt state.headBlockHash
        post).recent.getLast? = some b.block ∧
      buildPayloadOnChain ((node.forkchoiceUpdatedStep version params).2.chainAt
        state.headBlockHash post) version decoded (builder decoded).1 (builder decoded).2 =
          .ok ⟨stored.fork, stored.built⟩ := by
  simp only [forkchoiceUpdatedBuildStep] at hStep
  split at hStep
  · rename_i status' pid' mid hMid
    simp only [Prod.mk.injEq, Except.ok.injEq, Option.some.injEq] at hStep
    obtain ⟨⟨-, rfl⟩, rfl⟩ := hStep
    rw [hMid]
    have hMidNone : mid.builds.lookup pid' = none := by
      rw [show mid = (node.forkchoiceUpdatedStep version params).2 by rw [hMid],
        forkchoiceUpdatedStep_builds]
      exact hNone
    simp only [storeBuild, hMidNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      at hStored
    split at hStored
    · rename_i state j hp
      split at hStored
      · rename_i decoded post hd hpost
        split at hStored
        · rename_i fork built hb
          simp only [store, List.lookup, beq_self_eq_true, Option.some.injEq] at hStored
          subst hStored
          obtain ⟨b, hbk, hv⟩ := validState_eq_some_iff.mp hpost
          exact ⟨state, j, decoded, post, b, hp, hd, hbk, hv, recentTo_getLast? hbk, hb⟩
        · simp [store, hMidNone] at hStored
      · simp [store, hMidNone] at hStored
    · simp [store, hMidNone] at hStored
  · rename_i hNot
    exact absurd hStep (hNot _ _ _)

/-- The nodes that the steps reach from a node, by any sequence of calls. -/
inductive Reachable (start : Node) : Node → Prop where
  /-- The node itself. -/
  | refl : Reachable start start
  /-- The node after a step of `engine_newPayload`. -/
  | newPayload {node : Node} (version : Nat) (params : Lean.Json) :
    Reachable start node → Reachable start (node.newPayloadStep version params).2
  /-- The node after a step of `engine_forkchoiceUpdated`. -/
  | forkchoiceUpdated {node : Node} (version : Nat) (params : Lean.Json) :
    Reachable start node → Reachable start (node.forkchoiceUpdatedStep version params).2
  /-- The node after a step of `engine_forkchoiceUpdated` that builds. -/
  | forkchoiceUpdatedBuild {node : Node} (builder : Builder) (version : Nat) (params : Lean.Json) :
    Reachable start node →
      Reachable start (node.forkchoiceUpdatedBuildStep builder version params).2
  /-- The node after a step of `engine_getPayload`. -/
  | getPayload {node : Node} (setup : TrustedSetup) (version : Nat) (id : PayloadId) :
    Reachable start node → Reachable start (node.getPayloadStep setup version id).2

/-- Every node that the steps reach keeps each known block that is not accepted as it was. -/
theorem Reachable.lookup {start node : Node} {other : Hash32} {b : KnownBlock}
    (hr : Reachable start node) (h : start.blocks.lookup other = some b)
    (hb : b.validity.isAccepted = false) : node.blocks.lookup other = some b := by
  induction hr with
  | refl => exact h
  | newPayload version params _ ih => exact newPayloadStep_lookup ih hb
  | forkchoiceUpdated version params _ ih => exact forkchoiceUpdatedStep_lookup ih hb
  | forkchoiceUpdatedBuild builder version params _ ih =>
    rw [(forkchoiceUpdatedBuildStep_keeps _ _ _ _).1]
    exact forkchoiceUpdatedStep_lookup ih hb
  | getPayload setup version id _ ih => exact ih

/-- A payload known as valid in a node is valid in every node that the steps reach from it.

It keeps the same state after it. -/
theorem Reachable.validState {start node : Node} {hash : Hash32} {post : Execution.State.State}
    (hr : Reachable start node) (h : start.validState hash = some post) :
    node.validState hash = some post := by
  obtain ⟨b, hb, hv⟩ := validState_eq_some_iff.mp h
  exact validState_eq_some_iff.mpr
    ⟨b, hr.lookup hb (by simp [hv, Validity.isAccepted]), hv⟩

/-- A payload known as invalid in a node is invalid in every node that the steps reach from it. -/
theorem Reachable.invalid {start node : Node} {hash : Hash32} {b : KnownBlock}
    (hr : Reachable start node) (h : start.blocks.lookup hash = some b)
    (hInvalid : b.validity = .invalid) : node.blocks.lookup hash = some b :=
  hr.lookup h (by simp [hInvalid, Validity.isAccepted])

/-- A run keeps the configuration of the chain. -/
theorem executeOn_config (node : Node) (hash : Hash32) (block : RecentBlock)
    (post : Execution.State.State) (version : Nat) (params : Lean.Json) :
    (node.executeOn hash block post version params).2.config = node.config := by
  simp only [executeOn]
  split
  · rfl
  · simp only [recordExecution]
    split
    · rfl
    · split <;> rfl

/-- A step of `engine_newPayload` keeps the configuration of the chain. -/
theorem newPayloadStep_config (node : Node) (version : Nat) (params : Lean.Json) :
    (node.newPayloadStep version params).2.config = node.config := by
  simp only [newPayloadStep]
  split
  · rfl
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rfl
      · simp only [onParent]
        split
        · split
          · exact executeOn_config _ _ _ _ _ _
          · rfl
        · rfl
        · rfl
        · rfl

/-- Validation keeps the configuration of the chain. -/
theorem validateChain_config (node : Node) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).config = node.config := by
  induction fuel generalizing node hash with
  | zero => rfl
  | succ fuel ih =>
    simp only [validateChain]
    split
    · split
      · rw [executeOn_config, ih]
      · exact ih _ _
      · exact ih _ _
    · rfl

/-- A step of `engine_forkchoiceUpdated` keeps the configuration of the chain. -/
theorem forkchoiceUpdatedStep_config (node : Node) (version : Nat) (params : Lean.Json) :
    (node.forkchoiceUpdatedStep version params).2.config = node.config := by
  have hv : (node.validateHead version params).config = node.config := by
    simp only [validateHead]
    split
    · exact validateChain_config _ _ _
    · rfl
  simp only [forkchoiceUpdatedStep]
  split
  · exact hv
  · simp only [updateStep]
    split <;> exact hv

/-- Every node that the steps reach keeps the configuration of the chain. -/
theorem Reachable.config {start node : Node} (hr : Reachable start node) :
    node.config = start.config := by
  induction hr with
  | refl => rfl
  | newPayload version params _ ih => rw [newPayloadStep_config, ih]
  | forkchoiceUpdated version params _ ih => rw [forkchoiceUpdatedStep_config, ih]
  | forkchoiceUpdatedBuild builder version params _ ih =>
    rw [(forkchoiceUpdatedBuildStep_keeps _ _ _ _).2.1, forkchoiceUpdatedStep_config, ih]
  | getPayload setup version id _ ih => exact ih

/-- A payload that passes the checks and is answered invalid is then known as invalid. -/
theorem newPayloadStep_invalid_known {checked : CheckedBlock version} {hash : Hash32}
    {status : PayloadStatus} {reason : Option PayloadError} {next : Node}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hs : status.status = .invalid) :
    ∃ b, next.blocks.lookup hash = some b ∧ b.validity = .invalid := by
  by_cases hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true
  · rw [newPayloadStep_of_fresh hCheck hHash hFresh] at h
    simp only [onParent] at h
    split at h
    · split at h
      · simp only [executeOn] at h
        split at h
        · simp at h
        · rename_i st re nx hOn
          simp only [Prod.mk.injEq, Except.ok.injEq] at h
          obtain ⟨⟨rfl, -⟩, rfl⟩ := h
          -- An invalid answer brings back no block, so the payload is recorded as invalid.
          cases nx with
          | some bp =>
            obtain ⟨blk, post⟩ := bp
            have := (valid_iff_of_newPayloadOnChain hOn).mpr ⟨_, _, rfl⟩
            rw [hs] at this
            cases this
          | none =>
            exact ⟨⟨⟨checked.fork, checked.block.header, []⟩, none, .invalid⟩,
              by simp [recordExecution, hs, record], rfl⟩
      · simp only [Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        cases hs
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      cases hs
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, rfl⟩ := h
      exact ⟨⟨⟨checked.fork, checked.block.header, []⟩, none, .invalid⟩, by simp [record], rfl⟩
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      cases hs
  · simp only [Classical.not_forall] at hFresh
    obtain ⟨⟨blk, pow, v⟩, hk, hv⟩ := hFresh
    cases v with
    | valid post =>
      rw [newPayloadStep_of_known_valid hCheck hHash hk rfl] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, -⟩ := h
      cases hs
    | invalid =>
      rw [newPayloadStep_of_known_invalid hCheck hHash hk rfl] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, -⟩, rfl⟩ := h
      exact ⟨_, hk, rfl⟩
    | accepted v' p' => simp [Validity.isAccepted] at hv

/-- A payload answered valid is valid again, with its own hash, in every node reached after.

The request is the same, and its checks pass. -/
theorem newPayloadStep_valid_again {checked : CheckedBlock version} {hash : Hash32}
    {status : PayloadStatus} {reason : Option PayloadError} {next later : Node}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hs : status.status = .valid) (hr : Reachable next later) :
    later.newPayloadStep version params = (.ok (⟨.valid, some hash⟩, none), later) := by
  obtain ⟨-, post, hp⟩ := validState_of_newPayloadStep hCheck hHash h hs
  obtain ⟨b, hb, hv⟩ := validState_eq_some_iff.mp (hr.validState hp)
  have hConfig : later.config = node.config := by
    rw [hr.config, show next = (node.newPayloadStep version params).2 by rw [h],
      newPayloadStep_config]
  exact newPayloadStep_of_known_valid (hConfig ▸ hCheck) hHash hb hv

/-- A payload answered invalid after its checks pass is invalid again in every node reached after.

The request is the same, and its latest valid hash is that of its chain in the later node. -/
theorem newPayloadStep_invalid_again {checked : CheckedBlock version} {hash : Hash32}
    {status : PayloadStatus} {reason : Option PayloadError} {next later : Node}
    (hCheck : checkNewPayload node.config version params = .ok (.ok checked))
    (hHash : checked.block.header.hash = .ok hash)
    (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hs : status.status = .invalid) (hr : Reachable next later) :
    later.newPayloadStep version params =
      (.ok (⟨.invalid, latestValidHash later.tree hash⟩, none), later) := by
  obtain ⟨b, hb, hv⟩ := newPayloadStep_invalid_known hCheck hHash h hs
  have hConfig : later.config = node.config := by
    rw [hr.config, show next = (node.newPayloadStep version params).2 by rw [h],
      newPayloadStep_config]
  exact newPayloadStep_of_known_invalid (hConfig ▸ hCheck) hHash (hr.invalid hb hv) hv

/-- An invalid block hash comes from the checks before execution, and so from the request alone.

Any node with the same configuration gives the same answer. -/
theorem newPayloadStep_invalidBlockHash {status : PayloadStatus} {reason : Option PayloadError}
    {next : Node} (h : node.newPayloadStep version params = (.ok (status, reason), next))
    (hs : status.status = .invalidBlockHash) (other : Node) (hConfig : other.config = node.config) :
    (other.newPayloadStep version params).1 = .ok (status, reason) := by
  cases hCheck : checkNewPayload node.config version params with
  | error e => simp [newPayloadStep, hCheck] at h
  | ok r =>
    cases r with
    | error q =>
      obtain ⟨st, re⟩ := q
      rw [newPayloadStep_of_checkNewPayload_invalid hCheck] at h
      simp only [Prod.mk.injEq, Except.ok.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      rw [newPayloadStep_of_checkNewPayload_invalid (hConfig ▸ hCheck)]
    | ok checked =>
      exfalso
      cases hHash : checked.block.header.hash with
      | error e =>
        simp only [newPayloadStep, hCheck, hHash, Prod.mk.injEq, Except.ok.injEq] at h
        obtain ⟨⟨rfl, -⟩, -⟩ := h
        cases hs
      | ok hash =>
        by_cases hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true
        · rw [newPayloadStep_of_fresh hCheck hHash hFresh] at h
          simp only [onParent] at h
          split at h
          · split at h
            · simp only [executeOn] at h
              split at h
              · simp at h
              · rename_i st re nx hOn
                simp only [Prod.mk.injEq, Except.ok.injEq] at h
                obtain ⟨⟨rfl, -⟩, -⟩ := h
                exact status_ne_invalidBlockHash_of_newPayloadOnChain hCheck hOn hs
            · simp only [Prod.mk.injEq, Except.ok.injEq] at h
              obtain ⟨⟨rfl, -⟩, -⟩ := h
              cases hs
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs
          · simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs
        · simp only [Classical.not_forall] at hFresh
          obtain ⟨⟨blk, pow, v⟩, hk, hv⟩ := hFresh
          cases v with
          | valid post =>
            rw [newPayloadStep_of_known_valid hCheck hHash hk rfl] at h
            simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs
          | invalid =>
            rw [newPayloadStep_of_known_invalid hCheck hHash hk rfl] at h
            simp only [Prod.mk.injEq, Except.ok.injEq] at h
            obtain ⟨⟨rfl, -⟩, -⟩ := h
            cases hs
          | accepted v' p' => simp [Validity.isAccepted] at hv

end Node

end EthLib.Engine
