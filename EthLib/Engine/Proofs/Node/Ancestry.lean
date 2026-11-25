module

public import EthLib.Engine.Proofs.Node.Grounded
import all EthLib.Engine.Proofs.Node
import all EthLib.Engine.Proofs.Node.Grounded

/-!
# Proofs: the recorded ancestors of a valid block of an execution node

The chain that ends at a valid block stays the same in every later node.

It holds while the later node knows no block under the parent hash of the starting block.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Execution.Blocks (Block RecentBlock)
open EthLib.Execution.Transactions (Transaction)

namespace Node

variable {node : Node}

/-! ## A later node keeps the blocks that are not accepted -/

/-- A node with the same known blocks and configuration as another keeps its blocks. -/
private theorem keeps_of_blocks_eq {later : Node} (hb : later.blocks = node.blocks)
    (hc : later.config = node.config) : Keeps node later :=
  ⟨fun h _ => by rw [hb]; exact h, fun h => by rw [hb] at h; exact h, hc⟩

/-- Recording a block over a new or accepted hash keeps the blocks. -/
private theorem keeps_record {hash : Hash32} {b : KnownBlock}
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true) :
    Keeps node (node.record hash b) := by
  refine ⟨fun {x c} hc hca => ?_, lookup_eq_none_of_suffix (List.suffix_cons _ _), rfl⟩
  have hne : x ≠ hash := by
    rintro rfl
    rw [hFresh c hc] at hca
    cases hca
  rw [record_lookup_of_ne _ _ hne]
  exact hc

/-- A run over a new or accepted hash keeps the blocks. -/
private theorem keeps_executeOn {hash : Hash32}
    {block : (fork : Fork) × Block fork Transaction} {post : Execution.State.State}
    {version : Nat} {params : Lean.Json}
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true) :
    Keeps node (node.executeOn hash block post version params).2 := by
  simp only [Node.executeOn]
  split
  · exact Keeps.refl _
  · simp only [recordExecution]
    split
    · exact keeps_record hFresh
    · split
      · exact keeps_record hFresh
      · exact Keeps.refl _

/-- Validation keeps the blocks. -/
private theorem keeps_validateChain (fuel : Nat) (hash : Hash32) :
    Keeps node (node.validateChain fuel hash) :=
  ⟨fun h hb => validateChain_lookup h hb, lookup_eq_none_of_suffix (validateChain_suffix _ _ _),
    validateChain_config _ _ _⟩

/-! ## Valid blocks sit on valid parents -/

/-- Every known valid block of a node sits on a known valid parent, or on a root hash. -/
structure ValidParents (node : Node) (root : Hash32) : Prop where
  /-- The parent of a known valid block is a known valid block, or the root hash. -/
  parent : ∀ hash b post, node.blocks.lookup hash = some b → b.validity = .valid post →
    (∃ s, node.validState b.block.header.parentHash = some s) ∨
      b.block.header.parentHash = root

/-- Two nodes with the same known blocks have the same valid blocks. -/
private theorem validState_of_blocks_eq {node' : Node} (hb : node'.blocks = node.blocks)
    (hash : Hash32) : node'.validState hash = node.validState hash := by
  simp only [validState, hb]

/-- Two nodes with the same known blocks have the same valid parents. -/
private theorem ValidParents.of_blocks_eq {node' : Node} {root : Hash32}
    (hv : node.ValidParents root) (hb : node'.blocks = node.blocks) : node'.ValidParents root :=
  ⟨fun hash b post h hval => by
    rw [hb] at h
    simp only [validState_of_blocks_eq hb]
    exact hv.parent hash b post h hval⟩

/-- Recording a block over a new or accepted hash keeps each valid block valid. -/
private theorem validState_record {hash x : Hash32} {b : KnownBlock} {s : Execution.State.State}
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (h : node.validState x = some s) : (node.record hash b).validState x = some s := by
  obtain ⟨c, hc, hv⟩ := validState_eq_some_iff.mp h
  have hne : x ≠ hash := by
    rintro rfl
    have := hFresh c hc
    simp [hv, Validity.isAccepted] at this
  exact validState_eq_some_iff.mpr ⟨c, by rw [record_lookup_of_ne _ _ hne]; exact hc, hv⟩

/-- Recording a block over a new or accepted hash keeps the valid parents.

A valid recorded block needs a known valid parent, or the root hash as its parent. -/
private theorem ValidParents.record {root hash : Hash32} {b : KnownBlock}
    (hv : node.ValidParents root)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hValid : ∀ post, b.validity = .valid post →
      (∃ s, node.validState b.block.header.parentHash = some s) ∨
        b.block.header.parentHash = root) :
    (node.record hash b).ValidParents root := by
  refine ⟨fun x c post hc hval => ?_⟩
  by_cases hx : x = hash
  · subst hx
    simp only [Node.record, List.lookup, beq_self_eq_true, Option.some.injEq] at hc
    subst hc
    rcases hValid post hval with ⟨s, hs⟩ | h
    · exact .inl ⟨s, validState_record hFresh hs⟩
    · exact .inr h
  · rw [record_lookup_of_ne _ _ hx] at hc
    rcases hv.parent x c post hc hval with ⟨s, hs⟩ | h
    · exact .inl ⟨s, validState_record hFresh hs⟩
    · exact .inr h

/-- A run on a known valid parent, over a new or accepted hash, keeps the valid parents. -/
private theorem ValidParents.executeOn {root hash : Hash32}
    {block : (fork : Fork) × Block fork Transaction} {post : Execution.State.State}
    {version : Nat} {params : Lean.Json} (hv : node.ValidParents root)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true)
    (hp : node.validState block.2.header.parentHash = some post) :
    (node.executeOn hash block post version params).2.ValidParents root := by
  simp only [Node.executeOn]
  split
  · exact hv
  · simp only [recordExecution]
    split
    · exact hv.record hFresh fun _ _ => .inl ⟨post, hp⟩
    · split
      · exact hv.record hFresh fun _ h => by cases h
      · exact hv

/-- The answer by the parent, over a new or accepted hash, keeps the valid parents. -/
private theorem ValidParents.onParent {root hash : Hash32}
    {block : (fork : Fork) × Block fork Transaction} {version : Nat} {params : Lean.Json}
    (hv : node.ValidParents root)
    (hFresh : ∀ c, node.blocks.lookup hash = some c → c.validity.isAccepted = true) :
    (node.onParent hash block version params).2.ValidParents root := by
  simp only [Node.onParent]
  split
  · rename_i blk pow post hp
    split
    · exact hv.executeOn hFresh (validState_eq_some_iff.mpr ⟨_, hp, rfl⟩)
    · exact hv.record hFresh fun _ h => by cases h
  · exact hv.record hFresh fun _ h => by cases h
  · exact hv.record hFresh fun _ h => by cases h
  · exact hv

/-- A step of `engine_newPayload` keeps the valid parents. -/
theorem ValidParents.newPayloadStep {root : Hash32} {version : Nat} {params : Lean.Json}
    (hv : node.ValidParents root) : (node.newPayloadStep version params).2.ValidParents root := by
  unfold Node.newPayloadStep
  split
  · exact hv
  · exact hv
  · dsimp only
    split
    · exact hv
    · rename_i hash hHash
      split
      · exact hv
      · exact hv
      · rename_i hNotValid hNotInvalid
        -- The payload is neither valid nor invalid, so it is new or accepted.
        refine hv.onParent fun ⟨blk, pow, v⟩ hk => ?_
        cases v with
        | valid post => exact absurd hk (hNotValid blk pow post)
        | invalid => exact absurd hk (hNotInvalid blk pow)
        | accepted v' p' => rfl

/-- Validation of a chain keeps the valid parents. -/
private theorem ValidParents.validateChain {root : Hash32} (hv : node.ValidParents root)
    (fuel : Nat) (hash : Hash32) : (node.validateChain fuel hash).ValidParents root := by
  induction fuel generalizing node hash with
  | zero => exact hv
  | succ fuel ih =>
    simp only [Node.validateChain]
    split
    · rename_i block pow v p hb
      have hv' := ih hv block.2.header.parentHash
      -- The block is still accepted after the validation of the chain of its parent.
      have hk : (node.validateChain fuel block.2.header.parentHash).blocks.lookup hash =
          some _ := validateChain_lookup_accepted hb rfl fuel
      have hFresh : ∀ c, (node.validateChain fuel block.2.header.parentHash).blocks.lookup hash =
          some c → c.validity.isAccepted = true := by
        intro c hc
        rw [hk] at hc
        cases hc
        rfl
      split
      · rename_i post hp
        exact hv'.executeOn hFresh (validState_eq_some_iff.mpr ⟨_, hp, rfl⟩)
      · exact hv'.record hFresh fun _ h => by cases h
      · exact hv'
    · exact hv

/-- A step of `engine_forkchoiceUpdated` keeps the valid parents. -/
theorem ValidParents.forkchoiceUpdatedStep {root : Hash32} {version : Nat} {params : Lean.Json}
    (hv : node.ValidParents root) :
    (node.forkchoiceUpdatedStep version params).2.ValidParents root := by
  have hh : (node.validateHead version params).ValidParents root := by
    simp only [Node.validateHead]
    split
    · exact hv.validateChain _ _
    · exact hv
  simp only [Node.forkchoiceUpdatedStep]
  split
  · exact hh
  · simp only [updateStep]
    split
    · exact hh.of_blocks_eq rfl
    · exact hh

/-- A node that starts from a block knows it alone, with an empty body, as its head. -/
private theorem blocks_of_start {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat}
    (h : Node.start config transition anchor post total = some node) :
    ∃ hash pow, node.blocks = [(hash, ⟨⟨anchor.fork, ⟨anchor.header, [], anchor.ommers,
      fun _ => []⟩⟩, pow, .valid post⟩)] ∧ node.forkchoice.headBlockHash = hash := by
  unfold start at h
  cases hh : anchor.header.hash with
  | error e => simp [hh, Except.toOption] at h
  | ok hash =>
    cases hc : commitsToEmptyBody anchor
    · simp [hh, hc, Except.toOption] at h
    simp only [hh, hc, Except.toOption] at h
    by_cases hp : anchor.fork < .paris
    · by_cases hd : anchor.header.difficulty ≤ total
      · simp only [hp, hd, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
          Option.pure_def, Option.some.injEq] at h
        subst h
        exact ⟨hash, _, rfl, rfl⟩
      · simp [hp, hd] at h
    · simp only [hp, ↓reduceIte, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
        Option.some.injEq] at h
      subst h
      exact ⟨hash, _, rfl, rfl⟩

/-- The only block found in a list of one entry is the block of that entry. -/
private theorem eq_of_lookup_singleton {x k : Hash32} {b c : KnownBlock}
    (h : [(k, c)].lookup x = some b) : b = c := by
  by_cases hx : x = k
  · subst hx
    simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at h
    exact h.symm
  · have : (x == k) = false := by simp [hx]
    simp [List.lookup, this] at h

/-- A node that starts from a block has valid parents, under the parent hash of that block. -/
theorem validParents_of_start {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat}
    (h : Node.start config transition anchor post total = some node) :
    node.ValidParents anchor.header.parentHash := by
  obtain ⟨hash, pow, hb, -⟩ := blocks_of_start h
  -- The node knows the anchor alone, and its parent is the root hash.
  refine ⟨fun other b s hc _ => .inr ?_⟩
  rw [hb] at hc
  cases eq_of_lookup_singleton hc
  rfl

/-- Every node that the steps reach from a node with valid parents has them too. -/
theorem Reachable.validParents {start : Node} {root : Hash32} (hv : start.ValidParents root)
    (hr : Reachable start node) : node.ValidParents root := by
  induction hr with
  | refl => exact hv
  | newPayload version params _ ih => exact ih.newPayloadStep
  | forkchoiceUpdated version params _ ih => exact ih.forkchoiceUpdatedStep
  | forkchoiceUpdatedBuild builder version params _ ih =>
    exact ih.forkchoiceUpdatedStep.of_blocks_eq (forkchoiceUpdatedBuildStep_keeps _ _ _ _).1
  | getPayload setup version id _ ih => exact ih

/-! ## The chain that ends at a valid block -/

/-- The walk from a hash that a node does not know is empty. -/
private theorem ancestors_of_lookup_none {hash : Hash32} (h : node.blocks.lookup hash = none)
    (n : Nat) : ancestors node.tree n hash = [] := by
  cases n with
  | zero => rfl
  | succ n => simp [ancestors, tree_lookup, h]

/-- The walk from a known valid block meets only known valid blocks.

The node has valid parents under a root hash that it does not know. -/
theorem ValidParents.ancestors_valid {root hash x : Hash32} {s : Execution.State.State}
    (hv : node.ValidParents root) (hRoot : node.blocks.lookup root = none) (n : Nat)
    (hs : node.validState hash = some s) (hx : x ∈ ancestors node.tree n hash) :
    ∃ s', node.validState x = some s' := by
  induction n generalizing hash s with
  | zero => simp [ancestors] at hx
  | succ n ih =>
    obtain ⟨b, hb, hval⟩ := validState_eq_some_iff.mp hs
    simp only [ancestors, tree_lookup, hb, Option.map_some] at hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨s, hs⟩
    · rcases hv.parent hash b s hb hval with ⟨s', hs'⟩ | hp
      · exact ih hs' hx
      · rw [show b.toKnownPayload.parentHash = root from hp,
          ancestors_of_lookup_none hRoot] at hx
        simp at hx

/-- The walk from a known valid block is the same in a later node.

The node has valid parents under a root hash, which the later node does not know. -/
theorem Keeps.ancestors_eq {later : Node} {root hash : Hash32} {s : Execution.State.State}
    (hv : node.ValidParents root) (hk : Keeps node later)
    (hRoot : later.blocks.lookup root = none) (n : Nat) (hs : node.validState hash = some s) :
    ancestors later.tree n hash = ancestors node.tree n hash := by
  have hRootN := hk.lookup_eq_none hRoot
  induction n generalizing hash s with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b, hb, hval⟩ := validState_eq_some_iff.mp hs
    have hbL := hk.lookup hb (by simp [hval, Validity.isAccepted])
    simp only [ancestors, tree_lookup, hb, hbL, Option.map_some]
    congr 1
    rcases hv.parent hash b s hb hval with ⟨s', hs'⟩ | hp
    · exact ih hs'
    · rw [show b.toKnownPayload.parentHash = root from hp, ancestors_of_lookup_none hRoot,
        ancestors_of_lookup_none hRootN]

/-- The chain that ends at a known valid block is the same in a later node.

The node has valid parents under a root hash, which the later node does not know. -/
theorem Keeps.recentTo_eq {later : Node} {root hash : Hash32} {s : Execution.State.State}
    (hv : node.ValidParents root) (hk : Keeps node later)
    (hRoot : later.blocks.lookup root = none) (hs : node.validState hash = some s) :
    later.recentTo hash = node.recentTo hash := by
  have hRootN := hk.lookup_eq_none hRoot
  unfold recentTo
  rw [hk.ancestors_eq hv hRoot 255 hs]
  congr 1
  refine filterMap_congr fun x hx => ?_
  -- Each block of the walk is valid, so the later node keeps it.
  obtain ⟨s', hs'⟩ := hv.ancestors_valid hRootN 255 hs hx
  obtain ⟨c, hc, hcv⟩ := validState_eq_some_iff.mp hs'
  rw [hk.lookup hc (by simp [hcv, Validity.isAccepted]), hc]

/-- The chain that ends at a known valid block, with any state after it, is the same later on.

The node has valid parents under a root hash, which the later node does not know. -/
theorem Keeps.chainAt_eq {later : Node} {root hash : Hash32} {s : Execution.State.State}
    (hv : node.ValidParents root) (hk : Keeps node later)
    (hRoot : later.blocks.lookup root = none) (hs : node.validState hash = some s)
    (after : Execution.State.State) : later.chainAt hash after = node.chainAt hash after := by
  simp only [chainAt, hk.config, hk.recentTo_eq hv hRoot hs]

/-- The chain that ends at a valid block, with any state after it, is the same in later nodes.

The nodes are reached from a starting block.

It assumes that the last node knows no block under the parent hash of the starting block.

Such a block would close a cycle of block hashes. -/
theorem Reachable.chainAt_eq {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start later : Node}
    {hash : Hash32} {state : Execution.State.State}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node) (hLater : Reachable node later)
    (hRoot : later.blocks.lookup anchor.header.parentHash = none)
    (hValid : node.validState hash = some state) (after : Execution.State.State) :
    later.chainAt hash after = node.chainAt hash after := by
  exact hLater.keeps.chainAt_eq (hr.validParents (validParents_of_start hStart)) hRoot hValid
    after

end Node

end EthLib.Engine
