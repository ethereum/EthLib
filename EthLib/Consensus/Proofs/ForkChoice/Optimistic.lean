module

public import EthLib.Consensus.ForkChoice.Optimistic
public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: an invalid payload removes a block and its descendants

When the execution layer finds a payload invalid, the store drops some blocks.

The dropped blocks are exactly the known blocks that descend from one known block.

So a block that stays never has a dropped parent.

A linked store therefore stays linked, and its head is still the head of LMD-GHOST.
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

end Store

end EthLib.Consensus
