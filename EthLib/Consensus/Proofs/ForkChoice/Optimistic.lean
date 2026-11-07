module

public import EthLib.Consensus.ForkChoice.Optimistic
public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: an invalid payload removes a block and its descendants

When the execution layer finds a payload invalid, the store drops some blocks.

The dropped blocks are exactly the known blocks that descend from one known block.

So a block that stays never has a dropped parent.

A linked store therefore stays linked, and its head is still the head of LMD-GHOST.

The latest valid hash decides where the removal starts.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- The elements that a monadic filter map in `Except` gives: the images of the list. -/
theorem mem_filterMapM_ok {α β ε : Type} {f : α → Except ε (Option β)} :
    ∀ {l : List α} {out : List β}, l.filterMapM f = .ok out →
      ∀ y, y ∈ out ↔ ∃ x ∈ l, f x = .ok (some y)
  | [], out, mapped, y => by
    simp only [List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at mapped
    simp [← mapped]
  | x :: l, out, mapped, y => by
    rw [List.filterMapM_cons, bind_ok_iff] at mapped
    obtain ⟨image, first, mapped⟩ := mapped
    cases image with
    | none =>
      rw [mem_filterMapM_ok mapped]
      constructor
      · rintro ⟨x', mem, ok⟩
        exact ⟨x', List.mem_cons_of_mem _ mem, ok⟩
      · rintro ⟨x', mem, ok⟩
        rcases List.mem_cons.mp mem with rfl | mem
        · rw [first] at ok
          cases ok
        · exact ⟨x', mem, ok⟩
    | some z =>
      simp only at mapped
      rw [bind_ok_iff] at mapped
      obtain ⟨rest, restOk, mapped⟩ := mapped
      simp only [pure, Except.pure, Except.ok.injEq] at mapped
      subst mapped
      rw [List.mem_cons, mem_filterMapM_ok restOk]
      constructor
      · rintro (rfl | ⟨x', mem, ok⟩)
        · exact ⟨x, List.mem_cons_self, first⟩
        · exact ⟨x', List.mem_cons_of_mem _ mem, ok⟩
      · rintro ⟨x', mem, ok⟩
        rcases List.mem_cons.mp mem with rfl | mem
        · rw [first, Except.ok.injEq, Option.some.injEq] at ok
          exact .inl ok.symm
        · exact .inr ⟨x', mem, ok⟩

/-- Outside the forks with a payload in the block body, the zero hash names every block.

Another hash names none. -/
theorem marksLatestValid_of_not_range {hash : Hash32} {block : BeaconBlock preset fork}
    (range : ¬ (.bellatrix ≤ fork ∧ fork < .glamsterdam)) :
    marksLatestValid hash block = true ↔ hash = Vector.replicate 32 0 := by
  simp [marksLatestValid, range]

/-- In the forks with a payload, the zero hash names exactly the blocks with the empty payload. -/
theorem marksLatestValid_zero {block : BeaconBlock preset fork}
    (range : .bellatrix ≤ fork ∧ fork < .glamsterdam) :
    marksLatestValid (Vector.replicate 32 0) block = true ↔
      block.body.executionPayload range = .empty preset fork := by
  simp [marksLatestValid, range]

/-- In the forks with a payload, a nonzero hash names the blocks whose payload has that hash. -/
theorem marksLatestValid_of_ne_zero {hash : Hash32} {block : BeaconBlock preset fork}
    (range : .bellatrix ≤ fork ∧ fork < .glamsterdam) (nonzero : hash ≠ Vector.replicate 32 0) :
    marksLatestValid hash block = true ↔
      (block.body.executionPayload range).blockHash = hash := by
  simp only [marksLatestValid, range, and_self, ↓reduceDIte, nonzero, ↓reduceIte,
    Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  constructor
  · exact fun named => named.2
  · -- The empty payload has the zero hash, so a payload with another hash is not empty.
    refine fun same => ⟨fun empty => nonzero ?_, same⟩
    rw [← same, empty]
    rfl

namespace Store

variable {store : Store preset fork}

/-- A block stays after a removal unless its root is removed. -/
theorem removeBlocks_blocks (roots : List Root) (root : Root) :
    (store.removeBlocks roots).blocks[root]? =
      if roots.contains root then none else store.blocks[root]? := by
  simp only [removeBlocks, Std.TreeMap.getElem?_filter']
  cases store.blocks[root]? <;> by_cases removed : root ∈ roots <;> simp [removed]

/-- A state stays after a removal unless the root of its block is removed. -/
theorem removeBlocks_blockStates (roots : List Root) (root : Root) :
    (store.removeBlocks roots).blockStates[root]? =
      if roots.contains root then none else store.blockStates[root]? := by
  simp only [removeBlocks, Std.TreeMap.getElem?_filter']
  cases store.blockStates[root]? <;> by_cases removed : root ∈ roots <;> simp [removed]

/-- The timeliness of a block stays after a removal unless its root is removed. -/
theorem removeBlocks_blockTimeliness (roots : List Root) (root : Root) :
    (store.removeBlocks roots).blockTimeliness[root]? =
      if roots.contains root then none else store.blockTimeliness[root]? := by
  simp only [removeBlocks, Std.TreeMap.getElem?_filter']
  cases store.blockTimeliness[root]? <;> by_cases removed : root ∈ roots <;> simp [removed]

/-- The unrealized justification of a block stays after a removal unless its root is removed. -/
theorem removeBlocks_unrealizedJustifications (roots : List Root) (root : Root) :
    (store.removeBlocks roots).unrealizedJustifications[root]? =
      if roots.contains root then none else store.unrealizedJustifications[root]? := by
  simp only [removeBlocks, Std.TreeMap.getElem?_filter']
  cases store.unrealizedJustifications[root]? <;> by_cases removed : root ∈ roots <;> simp [removed]

/-- A vote stays after a removal unless it is for a removed block. -/
theorem removeBlocks_latestMessages (roots : List Root) (validator : ValidatorIndex) :
    (store.removeBlocks roots).latestMessages[validator]? =
      store.latestMessages[validator]?.filter fun message => !roots.contains message.root := by
  simp only [removeBlocks, Std.TreeMap.getElem?_filter']

/-- The boost stays after a removal unless it is for a removed block. -/
theorem removeBlocks_proposerBoostRoot (roots : List Root) :
    (store.removeBlocks roots).proposerBoostRoot =
      if roots.contains store.proposerBoostRoot then Vector.replicate 32 0
      else store.proposerBoostRoot := by
  simp [removeBlocks]

/-- A removal keeps the clock, the checkpoints, their states and the equivocators. -/
theorem removeBlocks_frame (roots : List Root) :
    (store.removeBlocks roots).timeMs = store.timeMs ∧
      (store.removeBlocks roots).genesisTimeMs = store.genesisTimeMs ∧
      (store.removeBlocks roots).justifiedCheckpoint = store.justifiedCheckpoint ∧
      (store.removeBlocks roots).finalizedCheckpoint = store.finalizedCheckpoint ∧
      (store.removeBlocks roots).unrealizedJustifiedCheckpoint =
        store.unrealizedJustifiedCheckpoint ∧
      (store.removeBlocks roots).unrealizedFinalizedCheckpoint =
        store.unrealizedFinalizedCheckpoint ∧
      (store.removeBlocks roots).checkpointStates = store.checkpointStates ∧
      (store.removeBlocks roots).equivocatingIndices = store.equivocatingIndices :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The blocks that a removal of descendants drops are the known descendants of its root.

An unknown root leaves the store as it was. -/
theorem removeDescendants_eq {first : Root} {after : Store preset fork}
    (removed : store.removeDescendants first = .ok after) :
    (store.blocks.contains first = false ∧ after = store) ∨
      ∃ roots, store.blocks.contains first ∧
        (∀ root, root ∈ roots ↔ store.blocks.contains root ∧
          store.isAncestor ⟨root, .pending⟩ ⟨first, .pending⟩ = .ok true) ∧
        after = store.removeBlocks roots := by
  unfold removeDescendants at removed
  by_cases known : store.blocks.contains first
  · simp only [known, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_ok_iff] at removed
    obtain ⟨roots, mapped, rest⟩ := removed
    simp only [pure, Except.pure, Except.ok.injEq] at rest
    refine .inr ⟨roots, known, fun root => ?_, rest.symm⟩
    rw [mem_filterMapM_ok mapped]
    constructor
    · rintro ⟨x, mem, ok⟩
      rw [bind_ok_iff] at ok
      obtain ⟨descends, ancestor, ok⟩ := ok
      cases descends <;> simp only [pure, Except.pure, Except.ok.injEq, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq, Option.some.injEq] at ok
      subst ok
      exact ⟨by simpa using mem, ancestor⟩
    · rintro ⟨contains, ancestor⟩
      refine ⟨root, by simpa using contains, ?_⟩
      simp [ancestor, bind, Except.bind, pure, Except.pure]
  · simp only [known, Bool.not_false, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at removed
    exact .inl ⟨Bool.eq_false_iff.mpr known, removed.symm⟩

/-- The removal of a root and its descendants succeeds on a store whose chains are well formed.

Each known parent must sit below its child.

Each known block whose parent is unknown must sit at or below every known block. -/
theorem removeDescendants_ok (lower : store.ParentsBelow)
    (orphansLe : ∀ (root other : Root) (block otherBlock : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = none →
      store.blocks[other]? = some otherBlock → block.slot ≤ otherBlock.slot)
    (first : Root) : ∃ after, store.removeDescendants first = .ok after := by
  by_cases known : store.blocks.contains first
  · have knownSome : (store.blocks[first]?).isSome = true := by
      rw [← Std.TreeMap.contains_eq_isSome_getElem?]
      exact known
    obtain ⟨firstBlock, firstFound⟩ := Option.isSome_iff_exists.mp knownSome
    obtain ⟨out, mapped⟩ := filterMapM_ok_of_forall (f := fun known => do
        return if ← store.isAncestor ⟨known, .pending⟩ ⟨first, .pending⟩ then some known
          else none) (l := store.blocks.keys) fun other mem => by
      obtain ⟨otherBlock, otherFound⟩ := Option.isSome_iff_exists.mp
        (Std.TreeMap.mem_iff_isSome_getElem?.mp (Std.TreeMap.mem_keys.mp mem))
      obtain ⟨ancestor, walk⟩ := getAncestor_ok_of_orphans_le lower (slot := firstBlock.slot)
        (fun r b found parentUnknown => orphansLe r first b firstBlock found parentUnknown
          firstFound) (node := ⟨other, .pending⟩) otherFound
      have blockOk : store.block first = .ok firstBlock := by simp [Store.block, firstFound]; rfl
      have decided : ∃ b, store.isAncestor ⟨other, .pending⟩ ⟨first, .pending⟩ = .ok b := by
        unfold Store.isAncestor
        simp only [blockOk, walk, bind, Except.bind]
        split <;> exact ⟨_, rfl⟩
      obtain ⟨b, decided⟩ := decided
      refine ⟨if b then some other else none, ?_⟩
      simp [decided, bind, Except.bind, pure, Except.pure]
    refine ⟨store.removeBlocks out, ?_⟩
    simp only [bind, Except.bind, pure, Except.pure] at mapped
    simp only [Store.removeDescendants, known, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, mapped]
  · exact ⟨store, by simp [Store.removeDescendants, known, pure, Except.pure]⟩

/-- The removal of a root and its descendants succeeds on a reachable store.

The anchor block must sit at or before the slot of the anchor state.

The parent root of the anchor must name no known block. -/
theorem Reachable.removeDescendants_ok {config : Config} {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork}
    (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none) (first : Root) :
    ∃ after, store.removeDescendants first = .ok after :=
  Store.removeDescendants_ok (reachable.parentsBelow anchorSlot unknown)
    (fun _ _ _ _ found parentUnknown otherFound =>
      reachable.orphans_le anchorSlot found parentUnknown otherFound) first

/-- The store after an invalid payload is the store as it was, or a removal of descendants. -/
theorem onInvalidPayload_eq {block : BeaconBlock preset fork} {latestValidHash : Option Hash32}
    {after : Store preset fork}
    (invalidated : store.onInvalidPayload block latestValidHash = .ok after) :
    after = store ∨ ∃ first, store.removeDescendants first = .ok after := by
  unfold onInvalidPayload at invalidated
  by_cases gloas : .glamsterdam ≤ fork
  · simp [gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at invalidated
  simp only [gloas, ↓reduceIte, bind_ok_iff] at invalidated
  obtain ⟨root, -, rest⟩ := invalidated
  cases latestValidHash with
  | none =>
    simp only [pure_bind] at rest
    exact .inr ⟨root, rest⟩
  | some hash =>
    by_cases marks : marksLatestValid hash block
    · simp only [marks, ↓reduceIte, pure_bind] at rest
      simp only [pure, Except.pure, Except.ok.injEq] at rest
      exact .inl rest.symm
    · simp only [marks, Bool.false_eq_true, ↓reduceIte, pure_bind, bind_ok_iff] at rest
      obtain ⟨found, -, rest⟩ := rest
      exact .inr ⟨_, rest⟩

/-- A removal keeps a store linked when it takes every known child of a removed root. -/
theorem Linked.removeBlocks {orphanParent : Root} {roots : List Root}
    (linked : store.Linked orphanParent)
    (closed : ∀ (root : Root) (block : BeaconBlock preset fork), store.blocks[root]? = some block →
      block.parentRoot ∈ roots → root ∈ roots) :
    (store.removeBlocks roots).Linked orphanParent := by
  refine ⟨fun r s found => ?_, fun r b found unknown => ?_, fun r b p found parentOf => ?_⟩
  · rw [removeBlocks_blockStates] at found
    rw [removeBlocks_blocks]
    by_cases removed : r ∈ roots
    · simp [removed] at found
    · simp only [List.contains_iff_mem, removed, ↓reduceIte] at found ⊢
      exact linked.stateAfter r s found
  · rw [removeBlocks_blocks] at found unknown
    by_cases removed : r ∈ roots
    · simp [removed] at found
    simp only [List.contains_iff_mem, removed, ↓reduceIte] at found
    by_cases parentRemoved : b.parentRoot ∈ roots
    · exact absurd (closed r b found parentRemoved) removed
    simp only [List.contains_iff_mem, parentRemoved, ↓reduceIte] at unknown
    exact linked.orphan r b found unknown
  · rw [removeBlocks_blocks] at found parentOf
    by_cases removed : r ∈ roots
    · simp [removed] at found
    by_cases parentRemoved : b.parentRoot ∈ roots
    · simp [parentRemoved] at parentOf
    simp only [List.contains_iff_mem, removed, parentRemoved, ↓reduceIte] at found parentOf
    exact linked.parentsBelow r b p found parentOf

/-- From Gloas the rule for an invalid payload is not yet specified here, so it fails. -/
theorem onInvalidPayload_of_gloas {block : BeaconBlock preset fork}
    {latestValidHash : Option Hash32} (gloas : .glamsterdam ≤ fork) :
    store.onInvalidPayload block latestValidHash = .error (.forkNotYetSpecified fork) := by
  simp [onInvalidPayload, gloas, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- An invalid payload keeps a store linked. -/
theorem Linked.onInvalidPayload {orphanParent : Root} {block : BeaconBlock preset fork}
    {latestValidHash : Option Hash32} {after : Store preset fork}
    (linked : store.Linked orphanParent)
    (invalidated : store.onInvalidPayload block latestValidHash = .ok after) :
    after.Linked orphanParent := by
  have before : fork < .glamsterdam := Nat.lt_of_not_le fun gloas => by
    rw [onInvalidPayload_of_gloas gloas] at invalidated
    cases invalidated
  rcases onInvalidPayload_eq invalidated with same | ⟨first, removed⟩
  · exact same ▸ linked
  rcases removeDescendants_eq removed with ⟨-, same⟩ | ⟨roots, -, member, rest⟩
  · exact same ▸ linked
  subst rest
  refine linked.removeBlocks fun r b found parentRemoved => ?_
  obtain ⟨contains, descends⟩ := (member _).mp parentRemoved
  rw [Std.TreeMap.contains_eq_isSome_getElem?] at contains
  obtain ⟨parent, parentFound⟩ := Option.isSome_iff_exists.mp contains
  refine (member r).mpr ⟨?_, isAncestor_of_parent before found parentFound
    (linked.parentsBelow r b parent found parentFound) descends⟩
  rw [Std.TreeMap.contains_eq_isSome_getElem?, found]
  rfl

/-- Before Gloas and without a boost, an invalid payload leaves the head of LMD-GHOST.

The store must be linked before the payload.

The model starts at the justified block, over the view of the viable nodes that stay. -/
theorem Linked.getHead_eq_ghost_of_onInvalidPayload {config : Config} {orphanParent : Root}
    {block : BeaconBlock preset fork} {latestValidHash : Option Hash32}
    {after : Store preset fork} {state : BeaconState preset fork}
    {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (linked : store.Linked orphanParent)
    (invalidated : store.onInvalidPayload block latestValidHash = .ok after)
    (before : fork < .glamsterdam) (noBoost : after.proposerBoostRoot = Vector.replicate 32 0)
    (justifiedState : after.checkpointState after.justifiedCheckpoint = .ok state)
    (tree : after.getFilteredNodeTree config = .ok nodes)
    (found : after.getHead config = .ok head) :
    Models.ForkChoice.ghost (voters state) (balanceAt state)
      (view (linked.onInvalidPayload invalidated).parentsBelow nodes) rootValue
      (some after.justifiedCheckpoint.root) = some head.root :=
  Store.getHead_eq_ghost _ before noBoost justifiedState tree found

/-- A known block sits in the chain of a root only when that root is known. -/
theorem known_of_ancestor {first root : Root} {firstBlock : BeaconBlock preset fork}
    (lower : store.ParentsBelow) (firstFound : store.blocks[first]? = some firstBlock)
    (descends : (blockTree lower).Ancestor (some first) (some root)) :
    ∃ block, store.blocks[root]? = some block := by
  cases found : store.blocks[root]? with
  | some block => exact ⟨block, rfl⟩
  | none =>
    -- An unknown root sits at height 1, and a known block at its slot plus 2.
    have height := descends.height_le
    rw [blockTree_height_of firstFound] at height
    simp [blockTree, treeHeight, found] at height

/-- A block in the chain of the parent of a known block is in the chain of that block. -/
theorem ancestor_of_parent {x : Option Root} {root : Root} {block : BeaconBlock preset fork}
    (lower : store.ParentsBelow) (found : store.blocks[root]? = some block)
    (above : (blockTree lower).Ancestor x (some block.parentRoot)) :
    (blockTree lower).Ancestor x (some root) := by
  rw [← blockTree_parent_of (lower := lower) found] at above
  exact above.trans ⟨1, rfl⟩

/-- The walk stops at once when the hash names the block. -/
theorem firstInvalidBlock_of_named {hash : Hash32} {child root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (named : marksLatestValid hash block = true) :
    store.firstInvalidBlock hash child root = .ok (some child) := by
  rw [firstInvalidBlock]
  split
  · simp_all
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp [named, pure, Except.pure]

/-- The walk ends when it reaches an unknown root. -/
theorem firstInvalidBlock_of_unknown {hash : Hash32} {child root : Root}
    (found : store.blocks[root]? = none) :
    store.firstInvalidBlock hash child root = .ok none := by
  rw [firstInvalidBlock]
  split
  · rfl
  · simp_all

/-- The walk ends at a block with an unknown parent that the hash does not name. -/
theorem firstInvalidBlock_of_orphan {hash : Hash32} {child root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (unnamed : marksLatestValid hash block = false)
    (parentFound : store.blocks[block.parentRoot]? = none) :
    store.firstInvalidBlock hash child root = .ok none := by
  rw [firstInvalidBlock]
  split
  · rfl
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp only [unnamed, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · simp_all

/-- The walk moves to a known parent at a lower slot when the hash does not name the block. -/
theorem firstInvalidBlock_of_parent {hash : Hash32} {child root : Root}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (unnamed : marksLatestValid hash block = false)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (parentLower : parent.slot < block.slot) :
    store.firstInvalidBlock hash child root =
      store.firstInvalidBlock hash root block.parentRoot := by
  conv => lhs; rw [firstInvalidBlock]
  split
  · simp_all
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp only [unnamed, Bool.false_eq_true, ↓reduceIte]
    split
    · simp_all
    · rename_i p same
      rw [parentFound, Option.some.injEq] at same
      subst same
      simp [parentLower]

/-- The walk fails at a known parent not at a lower slot when the hash does not name the block. -/
theorem firstInvalidBlock_of_not_lower {hash : Hash32} {child root : Root}
    {block parent : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    (unnamed : marksLatestValid hash block = false)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (notLower : ¬ parent.slot < block.slot) :
    store.firstInvalidBlock hash child root = .error (.parentSlotNotLower root) := by
  rw [firstInvalidBlock]
  split
  · simp_all
  · rename_i b same
    rw [found, Option.some.injEq] at same
    subst same
    simp only [unnamed, Bool.false_eq_true, ↓reduceIte]
    split
    · simp_all
    · rename_i p same
      rw [parentFound, Option.some.injEq] at same
      subst same
      simp only [notLower, ↓reduceDIte]
      rfl

/-- The walk leaves the store when the hash names no block of the chain.

That needs each known parent at a lower slot, or the walk can fail. -/
theorem firstInvalidBlock_of_absent {hash : Hash32} {child root : Root}
    (lower : store.ParentsBelow)
    (absent : ∀ x block, store.blocks[x]? = some block →
      (blockTree lower).Ancestor (some x) (some root) → marksLatestValid hash block = false) :
    store.firstInvalidBlock hash child root = .ok none := by
  induction child, root using firstInvalidBlock.induct (store := store)
    (latestValidHash := hash) with
  | case1 child root found => exact firstInvalidBlock_of_unknown found
  | case2 child root block found named =>
    have := absent root block found (.refl _)
    simp_all
  | case3 child root block found unnamed parentFound =>
    exact firstInvalidBlock_of_orphan found (by simpa using unnamed) parentFound
  | case4 child root block found unnamed parent parentFound parentLower ih =>
    rw [firstInvalidBlock_of_parent found (by simpa using unnamed) parentFound parentLower]
    exact ih fun x known stored above =>
      absent x known stored (ancestor_of_parent lower found above)
  | case5 child root block found unnamed parent parentFound notLower =>
    exact absurd (lower root block parent found parentFound) notLower

/-- The walk finds the child on the chain of the nearest block that the hash names.

No block from that child to the start of the walk may be named.

That needs each known parent at a lower slot. -/
theorem firstInvalidBlock_of_chain {hash : Hash32} {child root first : Root}
    {firstBlock namedBlock : BeaconBlock preset fork} (lower : store.ParentsBelow)
    (firstFound : store.blocks[first]? = some firstBlock)
    (namedFound : store.blocks[firstBlock.parentRoot]? = some namedBlock)
    (names : marksLatestValid hash namedBlock = true)
    (descends : (blockTree lower).Ancestor (some first) (some root))
    (between : ∀ x block, store.blocks[x]? = some block →
      (blockTree lower).Ancestor (some first) (some x) →
      (blockTree lower).Ancestor (some x) (some root) → marksLatestValid hash block = false) :
    store.firstInvalidBlock hash child root = .ok (some first) := by
  induction child, root using firstInvalidBlock.induct (store := store)
    (latestValidHash := hash) with
  | case1 child root rootFound =>
    -- The chain of an unknown root holds no known block.
    obtain ⟨_, known⟩ := known_of_ancestor lower firstFound descends
    simp_all
  | case2 child root block rootFound named =>
    have := between root block rootFound descends (.refl _)
    simp_all
  | case3 child root block rootFound unnamed parentFound =>
    rcases descends.eq_or_parent with same | above
    · -- The first block has a known parent, so it is not this block.
      rw [Option.some.injEq] at same
      subst same
      rw [rootFound, Option.some.injEq] at firstFound
      subst firstFound
      simp_all
    · -- The chain of an unknown parent holds no known block.
      rw [blockTree_parent_of rootFound] at above
      obtain ⟨_, known⟩ := known_of_ancestor lower firstFound above
      simp_all
  | case4 child root block rootFound unnamed parent parentFound parentLower ih =>
    rw [firstInvalidBlock_of_parent rootFound (by simpa using unnamed) parentFound parentLower]
    rcases descends.eq_or_parent with same | above
    · -- The walk has reached the first block, and the next step reaches the named block.
      rw [Option.some.injEq] at same
      subst same
      rw [rootFound, Option.some.injEq] at firstFound
      subst firstFound
      exact firstInvalidBlock_of_named namedFound names
    · rw [blockTree_parent_of rootFound] at above
      exact ih above fun x known stored below onChain =>
        between x known stored below (ancestor_of_parent lower rootFound onChain)
  | case5 child root block rootFound unnamed parent parentFound notLower =>
    exact absurd (lower root block parent rootFound parentFound) notLower

/-- A removal from an unknown root changes nothing. -/
theorem removeDescendants_of_unknown {first : Root} (unknown : store.blocks[first]? = none) :
    store.removeDescendants first = .ok store := by
  have absent : store.blocks.contains first = false := by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, unknown]
    rfl
  simp [removeDescendants, absent, pure, Except.pure]

/-- Before Gloas and without a hash, the first invalid block is the block itself. -/
theorem onInvalidPayload_of_none {block : BeaconBlock preset fork} {root : Root}
    (before : fork < .glamsterdam) (rooted : SszType.hashTreeRoot block = .ok root) :
    store.onInvalidPayload block none = store.removeDescendants root := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [onInvalidPayload, later, rooted, bind, Except.bind, Except.mapError, pure, Except.pure]

/-- Before Gloas, when the hash names the block itself, no block is invalid. -/
theorem onInvalidPayload_of_self {hash : Hash32} {block : BeaconBlock preset fork} {root : Root}
    (before : fork < .glamsterdam) (rooted : SszType.hashTreeRoot block = .ok root)
    (named : marksLatestValid hash block = true) :
    store.onInvalidPayload block (some hash) = .ok store := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp [onInvalidPayload, later, rooted, named, bind, Except.bind, Except.mapError, pure,
    Except.pure]

/-- Before Gloas, when the hash does not name the block, the walk from its parent decides. -/
theorem onInvalidPayload_of_unnamed {hash : Hash32} {block : BeaconBlock preset fork} {root : Root}
    (before : fork < .glamsterdam) (rooted : SszType.hashTreeRoot block = .ok root)
    (unnamed : marksLatestValid hash block = false) :
    store.onInvalidPayload block (some hash) = (do
      let found ← store.firstInvalidBlock hash root block.parentRoot
      store.removeDescendants (found.getD root)) := by
  have later : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  cases walk : store.firstInvalidBlock hash root block.parentRoot <;>
    simp [onInvalidPayload, later, rooted, unnamed, walk, bind, Except.bind, Except.mapError, pure,
      Except.pure]

/-- Before Gloas, the block is the first invalid one when the hash names no block of its chain.

The chain here holds the block and its known ancestors.

That needs each known parent at a lower slot, or the walk can fail. -/
theorem onInvalidPayload_of_absent {hash : Hash32} {block : BeaconBlock preset fork} {root : Root}
    (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    (rooted : SszType.hashTreeRoot block = .ok root)
    (unnamed : marksLatestValid hash block = false)
    (absent : ∀ x found, store.blocks[x]? = some found →
      (blockTree lower).Ancestor (some x) (some block.parentRoot) →
        marksLatestValid hash found = false) :
    store.onInvalidPayload block (some hash) = store.removeDescendants root := by
  rw [onInvalidPayload_of_unnamed before rooted unnamed, firstInvalidBlock_of_absent lower absent]
  rfl

/-- Before Gloas, the block is the first invalid one if the hash names its parent but not it. -/
theorem onInvalidPayload_of_parent {hash : Hash32} {block parent : BeaconBlock preset fork}
    {root : Root} (before : fork < .glamsterdam) (rooted : SszType.hashTreeRoot block = .ok root)
    (unnamed : marksLatestValid hash block = false)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (names : marksLatestValid hash parent = true) :
    store.onInvalidPayload block (some hash) = store.removeDescendants root := by
  rw [onInvalidPayload_of_unnamed before rooted unnamed,
    firstInvalidBlock_of_named parentFound names]
  rfl

/-- Before Gloas, if the hash names an older block, its child on the chain is the first invalid one.

No block from that child to the block itself may be named.

That needs each known parent at a lower slot. -/
theorem onInvalidPayload_of_chain {hash : Hash32}
    {block firstBlock namedBlock : BeaconBlock preset fork} {root first : Root}
    (before : fork < .glamsterdam) (lower : store.ParentsBelow)
    (rooted : SszType.hashTreeRoot block = .ok root)
    (unnamed : marksLatestValid hash block = false)
    (firstFound : store.blocks[first]? = some firstBlock)
    (namedFound : store.blocks[firstBlock.parentRoot]? = some namedBlock)
    (names : marksLatestValid hash namedBlock = true)
    (descends : (blockTree lower).Ancestor (some first) (some block.parentRoot))
    (between : ∀ x found, store.blocks[x]? = some found →
      (blockTree lower).Ancestor (some first) (some x) →
      (blockTree lower).Ancestor (some x) (some block.parentRoot) →
      marksLatestValid hash found = false) :
    store.onInvalidPayload block (some hash) = store.removeDescendants first := by
  rw [onInvalidPayload_of_unnamed before rooted unnamed,
    firstInvalidBlock_of_chain lower firstFound namedFound names descends between]
  rfl

end Store

end EthLib.Consensus
