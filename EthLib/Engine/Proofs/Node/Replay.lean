module

public import EthLib.Engine.Node.View
public import EthLib.Engine.Proofs.Node.Ancestry
import EthLib.Base.Proofs.MapM
import all EthLib.Engine.Proofs.Node.ReplayRuns
import all EthLib.Engine.Proofs.Node.View

/-!
# Proofs: the valid blocks of an execution node run again

Each valid block of a node reached from a starting block has a record, so the node has a view.

It assumes that the last node knows no block under the parent hash of the starting block.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg (TrustedSetup)
open EthLib.Execution.Blocks (RecentBlock)

namespace Node

variable {node : Node}

/-! ## The records of the valid blocks -/

/-- Every valid block of a node reached from a starting block has a record.

A block on a valid parent runs again on the chain of that parent.

The starting block has no transaction.

It assumes that the node knows no block under the parent hash of the starting block.

Such a block would close a cycle of block hashes. -/
theorem validRecord_isSome {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start : Node}
    {hash : Hash32} {state : Execution.State.State}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node)
    (hRoot : node.blocks.lookup anchor.header.parentHash = none)
    (hValid : node.validState hash = some state) :
    (node.validRecord hash).isSome := by
  have hR := Reachable.runs hStart hr hRoot
  obtain ⟨b, hb, hval⟩ := validState_eq_some_iff.mp hValid
  obtain ⟨⟨fork, block⟩, pow, v⟩ := b
  cases hval
  unfold validRecord
  simp only [hb]
  rcases hR hash _ state hb rfl with ⟨before, hs, r, hrun⟩ | ⟨hP, hT⟩
  · -- The body runs again on the chain of its valid parent.
    simp only at hs hrun
    simp only [hs, Execution.Rpc.BlockRecord.ofRun, hrun, bind, Except.bind, pure, Except.pure,
      Except.toOption, Option.isSome_some]
  · -- The first block sits on the root hash, which the node does not know, and has no transaction.
    have hNone : node.validState anchor.header.parentHash = none := by
      unfold Node.validState
      rw [hRoot]
    simp only at hP hT
    simp [hP, hNone, hT]

/-- A node reached from a starting block has a chain view, under any network ID and trusted setup.

It assumes that the node knows no block under the parent hash of the starting block.

Such a block would close a cycle of block hashes. -/
theorem view_isSome {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start : Node}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node)
    (hRoot : node.blocks.lookup anchor.header.parentHash = none)
    (networkId : Nat) (setup : TrustedSetup) :
    (node.view networkId setup).isSome := by
  have hv := hr.validParents (validParents_of_start hStart)
  have hRec : ∀ x s, node.validState x = some s → (node.validRecord x).isSome :=
    fun _ _ h => validRecord_isSome hStart hr hRoot h
  -- The head is valid, so each block of its chain is valid and has a record.
  obtain ⟨s, hs⟩ := hr.head_valid hStart
  have hCanon : ∀ x ∈ node.canonicalHashes, (node.validRecord x).isSome := by
    intro x hx
    simp only [canonicalHashes, chainOf, List.mem_reverse] at hx
    obtain ⟨s', hs'⟩ := hv.ancestors_valid hRoot _ hs hx
    exact hRec x s' hs'
  -- Each other valid block has a record too.
  have hSide : ∀ x ∈ node.validHashes.filter (· ∉ node.canonicalHashes),
      (node.validRecord x).isSome := by
    intro x hx
    simp only [validHashes, List.mem_filter] at hx
    obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.mp hx.1.2
    exact hRec x s' hs'
  obtain ⟨canonical, hc⟩ := Option.isSome_iff_exists.mp (isSome_mapM_iff.mpr hCanon)
  obtain ⟨side, hd⟩ := Option.isSome_iff_exists.mp (isSome_mapM_iff.mpr hSide)
  -- The head is on its own chain, so the canonical records are not empty.
  have hHead : node.forkchoice.headBlockHash ∈ node.canonicalHashes := by
    obtain ⟨b, hb, -⟩ := validState_eq_some_iff.mp hs
    have h := chainOf_head (tree := node.tree) (by rw [tree_lookup, hb]; rfl)
    simp only [canonicalHashes, List.mem_reverse]
    exact List.mem_of_mem_head? h
  have hne : canonical ≠ [] := by
    obtain ⟨r, hr, -⟩ := exists_mem_of_mapM hc hHead
    rintro rfl
    simp at hr
  unfold view
  simp only [hc, hd, bind, Option.bind_some, hne, ↓reduceDIte, Option.isSome_some]

/-- The record of a valid block, with its receipts and logs, is the same in every later node.

The nodes are reached from a starting block.

It assumes that the last node knows no block under the parent hash of the starting block.

Such a block would close a cycle of block hashes. -/
theorem Reachable.validRecord_eq {config : ChainConfig} {transition : TransitionConfiguration}
    {anchor : RecentBlock} {post : Execution.State.State} {total : Nat} {start later : Node}
    {hash : Hash32} {state : Execution.State.State}
    (hStart : Node.start config transition anchor post total = some start)
    (hr : Reachable start node) (hLater : Reachable node later)
    (hRoot : later.blocks.lookup anchor.header.parentHash = none)
    (hValid : node.validState hash = some state) :
    later.validRecord hash = node.validRecord hash := by
  have hv := hr.validParents (validParents_of_start hStart)
  have hRootN := hLater.lookup_eq_none hRoot
  obtain ⟨b, hb, hval⟩ := validState_eq_some_iff.mp hValid
  have hbL := hLater.lookup hb (by simp [hval, Validity.isAccepted])
  rcases hv.parent hash b state hb hval with ⟨s, hs⟩ | hP
  · obtain ⟨⟨fork, block⟩, pow, v⟩ := b
    cases hval
    -- The parent stays valid, and its chain stays the same.
    unfold validRecord
    simp only [hb, hbL]
    change node.validState block.header.parentHash = some s at hs
    simp only [hLater.validState hs, hs]
    rw [Reachable.chainAt_eq hStart hr hLater hRoot hs]
  · obtain ⟨⟨fork, block⟩, pow, v⟩ := b
    cases hval
    -- The parent is the root hash, which neither node knows.
    change block.header.parentHash = anchor.header.parentHash at hP
    have hNone : ∀ n : Node, n.blocks.lookup anchor.header.parentHash = none →
        n.validState block.header.parentHash = none := by
      intro n hn
      unfold Node.validState
      rw [hP, hn]
    unfold validRecord
    simp only [hb, hbL, hNone later hRoot, hNone node hRootN]

end Node

end EthLib.Engine
