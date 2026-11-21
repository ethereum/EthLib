module

public import EthLib.Engine.Proofs.BuildPayload
public import EthLib.Engine.Proofs.GetPayload
public import EthLib.Engine.Proofs.Node

/-!
# Proofs: a proposal on an execution node

A proposer's execution layer builds a block in three calls.

An update with payload attributes answers a payload ID and builds on its head.

A request for that ID returns the payload of the build.

The same payload sent back for validation is then valid, with its own hash.

The payload sits on the head of the update and carries the values of its attributes.

The node must be consistent: each known block is under its own hash, with sound totals.

Every node that the steps reach from a consistent node is consistent.

The sources are the [payload building][building] of Paris and [`engine_getPayloadV1`][get].

[building]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#payload-building
[get]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/engine/paris.md#engine_getpayloadv1
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Blocks (Block)
open EthLib.Execution.Transactions (Transaction)

namespace Node

variable {node : Node} {version : Nat} {params : Lean.Json}

/-! ## Consistent nodes -/

/-- A node is consistent when each known block is under its own hash, with sound totals.

A block from Paris on needs nothing more.

An older block is not accepted, and its total difficulty is at least its difficulty.

The total that it records for its parent is then its own total minus its difficulty. -/
def Consistent (node : Node) : Prop :=
  ∀ hash b, node.blocks.lookup hash = some b →
    b.block.header.hash = .ok hash ∧
      (.paris ≤ b.block.fork ∨ b.validity.isAccepted = false ∧
        ∃ total, b.powTotalDifficulty = some (total, total - b.block.header.difficulty) ∧
          b.block.header.difficulty ≤ total)

/-- A node that starts from a block is consistent. -/
theorem consistent_of_start {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : Execution.Blocks.RecentBlock} {post : Execution.State.State} {total : Nat}
    (h : Node.start config transition anchor post total = some node) : node.Consistent := by
  unfold start at h
  cases hh : anchor.header.hash with
  | error e => simp [hh, Except.toOption] at h
  | ok hash =>
    simp only [hh, Except.toOption] at h
    -- The node knows the anchor alone, under its hash.
    have hOne : ∀ pow, (.paris ≤ anchor.fork ∨
        ∃ total, pow = some (total, total - anchor.header.difficulty) ∧
          anchor.header.difficulty ≤ total) →
        (⟨config, transition, [(hash, ⟨anchor, pow, .valid post⟩)],
          ⟨hash, ZERO_HASH, ZERO_HASH⟩, none, []⟩ : Node).Consistent := by
      intro pow hp other b hb
      by_cases hne : other = hash
      · subst hne
        simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hb
        subst hb
        exact ⟨hh, hp.imp_right fun h => ⟨rfl, h⟩⟩
      · have : (other == hash) = false := by simp [hne]
        simp [List.lookup, this] at hb
    by_cases hp : anchor.fork < .paris
    · by_cases hd : anchor.header.difficulty ≤ total
      · simp only [hp, hd, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        exact hOne _ (.inr ⟨total, rfl, hd⟩)
      · simp [hp, hd] at h
    · simp only [hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact hOne _ (.inl (Nat.not_lt.mp hp))

/-- A node with the known blocks of a consistent node is consistent. -/
private theorem Consistent.of_blocks {node' : Node} (hc : node.Consistent)
    (h : node'.blocks = node.blocks) : node'.Consistent := by
  intro hash b hb
  rw [h] at hb
  exact hc hash b hb

/-- Recording a block from Paris on, under its own hash, keeps a node consistent. -/
private theorem Consistent.record {hash : Hash32} {b : KnownBlock} (hc : node.Consistent)
    (hHash : b.block.header.hash = .ok hash) (hFork : .paris ≤ b.block.fork) :
    (node.record hash b).Consistent := by
  intro other c hl
  by_cases hne : other = hash
  · subst hne
    simp only [Node.record, List.lookup, beq_self_eq_true, Option.some.injEq] at hl
    subst hl
    exact ⟨hHash, .inl hFork⟩
  · rw [record_lookup_of_ne _ _ hne] at hl
    exact hc other c hl

/-- Recording an execution of a block from Paris on, under its own hash, keeps consistency. -/
private theorem Consistent.recordExecution {hash : Hash32}
    {block : Execution.Blocks.RecentBlock} {status : PayloadStatus}
    {next : Option (Execution.Blocks.RecentBlock × Execution.State.State)}
    (hc : node.Consistent) (hHash : block.header.hash = .ok hash) (hFork : .paris ≤ block.fork) :
    (node.recordExecution hash block status next).Consistent := by
  unfold Node.recordExecution
  split
  · exact Consistent.record hc hHash hFork
  · split
    · exact Consistent.record hc hHash hFork
    · exact hc

/-- A run of a block from Paris on, under its own hash, keeps a node consistent. -/
private theorem Consistent.executeOn {hash : Hash32} {block : Execution.Blocks.RecentBlock}
    {post : Execution.State.State} (hc : node.Consistent) (hHash : block.header.hash = .ok hash)
    (hFork : .paris ≤ block.fork) :
    (node.executeOn hash block post version params).2.Consistent := by
  simp only [Node.executeOn]
  split
  · exact hc
  · exact Consistent.recordExecution hc hHash hFork

/-- The answer by the parent of a block from Paris on, under its own hash, keeps consistency. -/
private theorem Consistent.onParent {hash : Hash32} {block : Execution.Blocks.RecentBlock}
    (hc : node.Consistent)
    (hHash : block.header.hash = .ok hash) (hFork : .paris ≤ block.fork) :
    (node.onParent hash block version params).2.Consistent := by
  simp only [Node.onParent]
  split
  · split
    · exact Consistent.executeOn hc hHash hFork
    · exact Consistent.record hc hHash hFork
  · exact Consistent.record hc hHash hFork
  · exact Consistent.record hc hHash hFork
  · exact hc

/-- Validation of a chain keeps a node consistent. -/
private theorem Consistent.validateChain (hc : node.Consistent) (fuel : Nat) (hash : Hash32) :
    (node.validateChain fuel hash).Consistent := by
  induction fuel generalizing node hash with
  | zero => exact hc
  | succ fuel ih =>
    simp only [Node.validateChain]
    split
    · rename_i block pow v p hb
      obtain ⟨hHash, hFork⟩ := hc hash _ hb
      -- An accepted block of a consistent node is from Paris on.
      have hFork : .paris ≤ block.fork := by
        rcases hFork with h | ⟨h, -⟩
        · exact h
        · simp [Validity.isAccepted] at h
      have hc' := ih hc block.header.parentHash
      split
      · exact Consistent.executeOn hc' hHash hFork
      · exact Consistent.record hc' hHash hFork
      · exact hc'
    · exact hc

/-- The validation of an update keeps a node consistent. -/
private theorem Consistent.validateHead (hc : node.Consistent) :
    (node.validateHead version params).Consistent := by
  unfold Node.validateHead
  split
  · exact Consistent.validateChain hc _ _
  · exact hc

/-- A step of `engine_newPayload` keeps a node consistent. -/
theorem Consistent.newPayloadStep (hc : node.Consistent) :
    (node.newPayloadStep version params).2.Consistent := by
  unfold Node.newPayloadStep
  split
  · exact hc
  · exact hc
  · rename_i checked hCheck
    dsimp only
    split
    · exact hc
    · rename_i hash hHash
      split
      · exact hc
      · exact hc
      -- A checked payload is from Paris on, since some version takes its fork.
      · exact Consistent.onParent hc hHash
          ((exists_acceptsFork_iff checked.fork).mp ⟨_, checked.accepted⟩)

/-- A step of `engine_forkchoiceUpdated` keeps a node consistent. -/
theorem Consistent.forkchoiceUpdatedStep (hc : node.Consistent) :
    (node.forkchoiceUpdatedStep version params).2.Consistent := by
  have hv := Consistent.validateHead (version := version) (params := params) hc
  simp only [Node.forkchoiceUpdatedStep]
  split
  · exact hv
  · simp only [Node.updateStep]
    split
    · exact Consistent.of_blocks hv rfl
    · exact hv

/-- A step of `engine_forkchoiceUpdated` that builds keeps a node consistent. -/
theorem Consistent.forkchoiceUpdatedBuildStep (hc : node.Consistent) (builder : Builder) :
    (node.forkchoiceUpdatedBuildStep builder version params).2.Consistent := by
  exact Consistent.of_blocks (Consistent.forkchoiceUpdatedStep hc)
    (forkchoiceUpdatedBuildStep_keeps _ _ _ _).1

/-- Every node that the steps reach from a consistent node is consistent. -/
theorem Reachable.consistent {start : Node} (hs : start.Consistent) (hr : Reachable start node) :
    node.Consistent := by
  induction hr with
  | refl => exact hs
  | newPayload version params _ ih => exact Consistent.newPayloadStep ih
  | forkchoiceUpdated version params _ ih => exact Consistent.forkchoiceUpdatedStep ih
  | forkchoiceUpdatedBuild builder version params _ ih =>
    exact Consistent.forkchoiceUpdatedBuildStep ih builder
  | getPayload setup version id _ ih => exact ih

/-! ## The proposal -/

/-- An update that answers a payload ID applies the head of its request, after the validation.

The method on the validated node then applies that head. -/
private theorem forkchoiceUpdatedStep_of_payloadId {status : PayloadStatus} {pid : PayloadId}
    (h : (node.forkchoiceUpdatedStep version params).1 = .ok (status, some pid)) :
    ∃ state attributes st, forkchoiceUpdatedParams version params = .ok (state, attributes) ∧
      Engine.forkchoiceUpdated (node.validateHead version params).transition
        (node.validateHead version params).tree (node.validateHead version params).finalized
        state = .ok (st, some state.headBlockHash) ∧
      (node.forkchoiceUpdatedStep version params).2 =
        (node.validateHead version params).applyForkchoice state := by
  cases hA : (node.validateHead version params).headAccepted version params
  · rw [forkchoiceUpdatedStep_answer _ _ _ hA] at h
    cases hCall : forkchoiceUpdatedCall (node.validateHead version params).config
      (node.validateHead version params).transition version
      (node.validateHead version params).tree (node.validateHead version params).finalized
      params with
    | error e => simp [hCall, Functor.map, Except.map] at h
    | ok r =>
      simp only [hCall, Functor.map, Except.map, Except.ok.injEq] at h
      obtain ⟨state, attributes, st, head, hp, hf, -, h2⟩ := forkchoiceUpdatedCall_ok_cases hCall
      -- A payload ID needs attributes, which the call returns only with an applied head.
      rcases h2 with h2 | ⟨j, hd, known, decoded, a, -, rfl, -⟩
      · cases head <;> simp [forkchoiceUpdatedResponse, h2] at h
      · obtain ⟨rfl, -⟩ := valid_of_forkchoiceUpdated hf
        exact ⟨state, attributes, st, hp, hf, forkchoiceUpdatedStep_of_applied hA hp hf⟩
  · rw [forkchoiceUpdatedStep_of_headAccepted _ _ _ hA] at h
    simp at h

/-- The stored build of an update is the build on the head of the node after the build.

The update answers a payload ID, with no build under it before.

The node after the update has the head of the request as its head, a valid block with a state.

The stored build is the build on the chain of that head, in the node after the update.

It uses the attributes as the version decodes them, and the builder of the node. -/
theorem build_of_forkchoiceUpdatedBuildStep {builder : Builder} {status : PayloadStatus}
    {pid : PayloadId} {next : Node} {stored : StoredPayload}
    (hStep : node.forkchoiceUpdatedBuildStep builder version params =
      (.ok (status, some pid), next))
    (hNone : node.builds.lookup pid = none) (hStored : next.store pid = some stored) :
    ∃ state j decoded post b, forkchoiceUpdatedParams version params = .ok (state, some j) ∧
      payloadAttributesOfVersion version j = .ok decoded ∧
      next.forkchoice.headBlockHash = state.headBlockHash ∧
      next.blocks.lookup state.headBlockHash = some b ∧ b.validity = .valid post ∧
      buildPayloadOnChain (next.chainAt state.headBlockHash post) version decoded
        (builder decoded).1 (builder decoded).2 = .ok ⟨stored.fork, stored.built⟩ := by
  obtain ⟨state, j, decoded, post, b, hp, hd, hb, hv, -, hbuild⟩ :=
    store_of_forkchoiceUpdatedBuildStep hStep hNone hStored
  have hAns : (node.forkchoiceUpdatedStep version params).1 = .ok (status, some pid) := by
    rw [← forkchoiceUpdatedBuildStep_answer _ builder, hStep]
  obtain ⟨state', attributes, st, hp', -, hMid⟩ := forkchoiceUpdatedStep_of_payloadId hAns
  rw [hp] at hp'
  cases hp'
  -- The build only adds to the builds of the node after the update.
  obtain ⟨hBlocks, hConfig, hFc⟩ := forkchoiceUpdatedBuildStep_keeps node builder version params
  simp only [hStep] at hBlocks hConfig hFc
  have hChain : next.chainAt state.headBlockHash post =
      (node.forkchoiceUpdatedStep version params).2.chainAt state.headBlockHash post := by
    simp only [chainAt, recentTo, tree, hBlocks, hConfig]
  refine ⟨state, j, decoded, post, b, hp, hd, ?_, ?_, hv, ?_⟩
  · rw [hFc, hMid]
    rfl
  · rw [hBlocks]
    exact hb
  · rw [hChain]
    exact hbuild

/-- An update that applies a head has a chain that passes the terminal block check. -/
private theorem chainPassesTerminalCheck_of_forkchoiceUpdated
    {transition : TransitionConfiguration} {tree : PayloadTree} {finalized : Option Hash32}
    {state : ForkchoiceState} {status : PayloadStatus} {head : Hash32}
    (hf : Engine.forkchoiceUpdated transition tree finalized state = .ok (status, some head)) :
    chainPassesTerminalCheck transition tree state.headBlockHash = true := by
  cases hT : chainPassesTerminalCheck transition tree state.headBlockHash
  · unfold Engine.forkchoiceUpdated at hf
    split at hf
    · simp [pure, Except.pure] at hf
    · simp [hT, pure, Except.pure] at hf
  · rfl

/-- Storing a build keeps the configuration of the transition. -/
private theorem storeBuild_transition (node : Node) (builder : Builder) (version : Nat)
    (params : Lean.Json) (id : PayloadId) :
    (node.storeBuild builder version params id).transition = node.transition := by
  simp only [storeBuild]
  repeat' split
  all_goals rfl

/-- The payload of an update's build, sent back for validation, is valid with its own hash.

The update answers a payload ID, with no build under it before, on a consistent node.

The request for that ID returns the payload, and the node does not know its block as invalid.

The parameters of the validation pass the checks before execution, and give that block.

Those checks give the block a hash, which the theorem names.

The block's parent is the head of the update.

Its timestamp, RANDAO mix, withdrawals, parent beacon block root and slot are the attributes'.

The attributes are those of the request, as its version decodes them, at the fork of the build.

The fee recipient is not among them, since the builder may choose another one. -/
theorem newPayloadStep_of_getPayloadStep {builder : Builder} {status : PayloadStatus}
    {pid : PayloadId} {next : Node} {setup : TrustedSetup} {version' version'' : Nat}
    {r : GetPayloadResponse} {params' : Lean.Json} {checked : CheckedBlock version''}
    {hash : Hash32} (hc : node.Consistent)
    (hStep : node.forkchoiceUpdatedBuildStep builder version params =
      (.ok (status, some pid), next))
    (hNone : node.builds.lookup pid = none)
    (hGet : (next.getPayloadStep setup version' pid).1 = .ok r)
    (hCheck : checkNewPayload next.config version'' params' = .ok (.ok checked))
    (hBlock : (⟨checked.fork, checked.block⟩ : Σ f, Block f Transaction) =
      ⟨r.stored.fork, r.stored.built.block⟩)
    (hHash : checked.block.header.hash = .ok hash)
    (hKnown : ∀ b, next.blocks.lookup hash = some b → b.validity ≠ .invalid) :
    ∃ state j decoded attributes, forkchoiceUpdatedParams version params = .ok (state, some j) ∧
      payloadAttributesOfVersion version j = .ok decoded ∧
      PayloadAttributes.atFork decoded r.stored.fork = some attributes ∧
      r.stored.built.block.header.parentHash = state.headBlockHash ∧
      r.stored.built.block.header.timestamp.toNat = attributes.timestamp.toNat ∧
      r.stored.built.block.header.prevRandao = attributes.prevRandao ∧
      r.stored.built.block.withdrawals = attributes.withdrawals ∧
      r.stored.built.block.header.parentBeaconBlockRoot = attributes.parentBeaconBlockRoot ∧
      r.stored.built.block.header.slotNumber = attributes.slotNumber ∧
      (next.newPayloadStep version'' params').1 = .ok (⟨.valid, some hash⟩, none) := by
  obtain ⟨state, j, decoded, post, b, hp, hd, hFc, hb, hv, hbuild⟩ :=
    build_of_forkchoiceUpdatedBuildStep hStep hNone
      (of_getPayload_eq_ok (by rw [getPayloadStep_eq] at hGet; exact hGet)).1
  -- The update applied the head, on the validated node.
  have hAns : (node.forkchoiceUpdatedStep version params).1 = .ok (status, some pid) := by
    rw [← forkchoiceUpdatedBuildStep_answer _ builder, hStep]
  obtain ⟨state', attributes', st, hp', hf, hMid⟩ := forkchoiceUpdatedStep_of_payloadId hAns
  rw [hp] at hp'
  cases hp'
  -- The build changes neither the known blocks nor the configuration of the transition.
  have hBlocks : next.blocks = (node.validateHead version params).blocks := by
    have := (forkchoiceUpdatedBuildStep_keeps node builder version params).1
    simp only [hStep] at this
    rw [this, hMid]
    rfl
  have hTr : next.transition = (node.validateHead version params).transition := by
    have : (node.forkchoiceUpdatedBuildStep builder version params).2.transition =
        (node.forkchoiceUpdatedStep version params).2.transition := by
      simp only [forkchoiceUpdatedBuildStep]
      split
      · rename_i h
        rw [h]
        exact storeBuild_transition _ _ _ _ _
      · rfl
    simp only [hStep] at this
    rw [this, hMid]
    rfl
  -- So the chain of the head passes the terminal block check in the tree of the next node.
  have hT := chainPassesTerminalCheck_of_forkchoiceUpdated hf
  rw [show (node.validateHead version params).tree = next.tree by simp only [tree, hBlocks],
    ← hTr] at hT
  -- The next node is consistent, so the head is a block under its own hash.
  have hcn : next.Consistent := by
    have := Consistent.forkchoiceUpdatedBuildStep (version := version) (params := params) hc
      builder
    rwa [hStep] at this
  obtain ⟨hHeadHash, hHeadFork⟩ := hcn _ _ hb
  have hRecent : (next.chainAt state.headBlockHash post).recent.getLast? = some b.block :=
    recentTo_getLast? hb
  obtain ⟨parent, attributes, transactions, hLast, hAttr, -, hBuilt⟩ :=
    buildPayload_of_buildPayloadOnChain hbuild
  rw [hRecent] at hLast
  cases hLast
  obtain ⟨-, -, hAt, -⟩ := checkAttributes_eq_ok_iff.mp hAttr
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, parent', hLast', hParentHash, -⟩ :=
    buildPayload_fields hBuilt
  rw [hRecent] at hLast'
  cases hLast'
  -- The built block's parent hash is the hash of the head block.
  have hPar : r.stored.built.block.header.parentHash = state.headBlockHash :=
    Except.ok.inj (hParentHash.symm.trans hHeadHash)
  refine ⟨state, j, decoded, attributes, hp, hd, hAt, hPar, h1, h2, h3, h4, h5, ?_⟩
  -- The head passes the terminal block check, with its total difficulty.
  have hTerm : ∀ p, (next.chainAt state.headBlockHash post).recent.getLast? = some p →
      passesTerminalCheck next.transition (next.totalDifficulty state.headBlockHash) p = true := by
    intro p hl
    rw [hRecent] at hl
    cases hl
    rcases hHeadFork with hP | ⟨-, total, hPow, hD⟩
    · simp [passesTerminalCheck, hP]
    · have htd : next.totalDifficulty state.headBlockHash = total := by
        simp [totalDifficulty, hb, hPow]
      have hTree : next.tree.lookup state.headBlockHash = some b.toKnownPayload := by
        rw [tree_lookup, hb]
        rfl
      rw [chainPassesTerminalCheck_of_lookup hTree hPow] at hT
      simp [passesTerminalCheck, htd, hD, hT]
  -- The checked block is the built block, at the fork of the build.
  obtain ⟨cfork, cacc, cblock⟩ := checked
  obtain ⟨hf1, hf2⟩ := Sigma.mk.inj hBlock
  subst hf1
  cases eq_of_heq hf2
  by_cases hNew : ∀ c, next.blocks.lookup hash = some c → c.validity.isAccepted = true
  · -- A payload not known as valid or invalid runs on the head, its valid parent.
    rw [newPayloadStep_of_head (post := post) hCheck hHash hNew
      (by rw [hPar]; exact validState_eq_some_iff.mpr ⟨b, hb, hv⟩) (by rw [hPar, hFc]),
      hPar, newPayloadOnChain_of_buildPayload hCheck hBuilt rfl hTerm]
    simp [hHash, Except.toOption, Functor.map, Except.map]
  · -- A payload known as valid is valid again, and it is not known as invalid.
    simp only [Classical.not_forall] at hNew
    obtain ⟨⟨blk, pow, v⟩, hk, hv'⟩ := hNew
    cases v with
    | valid p => rw [newPayloadStep_of_known_valid hCheck hHash hk rfl]
    | invalid => exact absurd rfl (hKnown _ hk)
    | accepted v' p' => simp [Validity.isAccepted] at hv'

end Node

end EthLib.Engine
