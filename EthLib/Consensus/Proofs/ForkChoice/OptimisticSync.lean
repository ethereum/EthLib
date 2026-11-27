module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Consensus.ForkChoice.OptimisticSync
public import EthLib.Consensus.Proofs.ForkChoice.Handlers
public import EthLib.Consensus.Proofs.Transition.Payload
public import EthLib.Consensus.Proofs.ForkChoice.Optimistic

/-!
# Proofs: optimistic sync

These proofs cover the optimistic import of a block and the latest verified ancestor of a node.

They cover the payload chain of a block, and how a valid or an invalid payload changes the store.

They also cover the optimistic head and node, and the domains an optimistic validator may not sign.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- Before Bellatrix, no block carries a payload. -/
theorem isExecutionBlock_of_lt_bellatrix (before : fork < .bellatrix)
    (block : BeaconBlock preset fork) : isExecutionBlock block = false := by
  have notGloas : ¬(Fork.glamsterdam ≤ fork) := fun gloas =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before (Nat.le_trans (by decide) gloas))
  have notBellatrix : ¬(Fork.bellatrix ≤ fork) := Nat.not_le_of_lt before
  simp [isExecutionBlock, notGloas, notBellatrix]

/-- From Bellatrix to Fulu, a block carries a payload when its payload is not the empty one. -/
theorem isExecutionBlock_of_range (range : .bellatrix ≤ fork ∧ fork < .glamsterdam)
    (block : BeaconBlock preset fork) :
    isExecutionBlock block = (block.body.executionPayload range != .empty preset fork) := by
  have notGloas : ¬(Fork.glamsterdam ≤ fork) := Nat.not_le_of_lt range.2
  simp [isExecutionBlock, notGloas, range.1]

/-- From Gloas, a block carries a payload when its bid names a nonzero block hash. -/
theorem isExecutionBlock_of_glamsterdam (gloas : .glamsterdam ≤ fork)
    (block : BeaconBlock preset fork) :
    isExecutionBlock block =
      ((block.body.signedExecutionPayloadBid gloas).message.blockHash !=
        Vector.replicate 32 0) := by
  simp [isExecutionBlock, gloas]

/-- A block may be imported optimistically exactly when its known parent allows it.

The parent carries a payload, or the slot of the block is far enough before the clock.

The sum of the slot and the number of slots is computed only for a parent without a payload. -/
theorem OptimisticStore.isOptimisticCandidateBlock_eq_ok_iff {store : OptimisticStore preset fork}
    {currentSlot safeSlots : Slot} {block : BeaconBlock preset fork} {answer : Bool} :
    store.isOptimisticCandidateBlock currentSlot block safeSlots = .ok answer ↔
      ∃ parent, store.blocks[block.parentRoot]? = some parent ∧
        ((isExecutionBlock parent = true ∧ answer = true) ∨
          (isExecutionBlock parent = false ∧ ∃ enough,
            Uint64.addChecked block.slot safeSlots = .ok enough ∧
              answer = decide (enough ≤ currentSlot))) := by
  unfold isOptimisticCandidateBlock
  cases found : store.blocks[block.parentRoot]? with
  | none =>
    simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_exists,
      not_and]
    exact fun _ none => absurd none (by simp)
  | some parent =>
    simp only [Option.some.injEq, exists_eq_left']
    cases execution : isExecutionBlock parent with
    | true =>
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq, true_and, Bool.true_eq_false,
        false_and, or_false]
      exact eq_comm
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, false_and, true_and, false_or]
      cases sum : Uint64.addChecked block.slot safeSlots with
      | error e =>
        simp only [Except.mapError, bind, Except.bind, reduceCtorEq, false_iff, not_exists,
          not_and]
        exact fun _ none => absurd none (by simp)
      | ok enough =>
        simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
          exists_eq_left']
        exact eq_comm

namespace OptimisticStore

variable (store : OptimisticStore preset fork)

/-- The roots that a walk of optimistic blocks reaches from a block, each step to the parent.

A step leaves an optimistic block whose parent root is not zero. -/
inductive OptimisticWalk : Root → Root → Prop where
  /-- The walk may stop at once. -/
  | here (root : Root) : OptimisticWalk root root
  /-- The walk may go from an optimistic block to its parent. -/
  | parent {root last : Root} {block : BeaconBlock preset fork}
      (found : store.blocks[root]? = some block) (optimistic : store.isOptimistic root = true)
      (notGenesis : block.parentRoot ≠ Vector.replicate 32 0)
      (rest : OptimisticWalk block.parentRoot last) : OptimisticWalk root last

/-- The latest verified block is reached through optimistic blocks.

It is known, and it is not optimistic or its parent root is zero. -/
theorem latestVerifiedBlock_spec {root ancestor : Root}
    (found : store.latestVerifiedBlock root = .ok ancestor) :
    store.OptimisticWalk root ancestor ∧ ∃ block, store.blocks[ancestor]? = some block ∧
      (store.isOptimistic ancestor = false ∨ block.parentRoot = Vector.replicate 32 0) := by
  induction root using latestVerifiedBlock.induct (store := store) with
  | case1 root unknown =>
    rw [latestVerifiedBlock, unknown] at found
    simp [throw, throwThe, MonadExceptOf.throw] at found
  | case2 root block known stops =>
    rw [latestVerifiedBlock, known] at found
    simp only [stops, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at found
    subst found
    refine ⟨.here _, block, known, ?_⟩
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at stops
    exact stops
  | case3 root block known goes unknown =>
    rw [latestVerifiedBlock, known] at found
    simp only [goes, Bool.false_eq_true, ↓reduceIte] at found
    split at found
    · simp [throw, throwThe, MonadExceptOf.throw] at found
    · simp_all
  | case4 root block known goes parent parentFound lower ih =>
    rw [latestVerifiedBlock, known] at found
    simp only [goes, Bool.false_eq_true, ↓reduceIte] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [parentFound, Option.some.injEq] at otherFound
      subst otherFound
      simp only [lower, ↓reduceDIte] at found
      obtain ⟨walk, rest⟩ := ih found
      simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq,
        not_or, Bool.not_eq_false] at goes
      exact ⟨.parent known goes.1 goes.2 walk, rest⟩
  | case5 root block known goes parent parentFound notLower =>
    rw [latestVerifiedBlock, known] at found
    simp only [goes, Bool.false_eq_true, ↓reduceIte] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [parentFound, Option.some.injEq] at otherFound
      subst otherFound
      simp only [notLower, ↓reduceDIte] at found
      simp [throw, throwThe, MonadExceptOf.throw] at found

/-- Before Gloas, the latest verified ancestor of a node walks back from its block.

It keeps the status of the node. -/
theorem latestVerifiedAncestor_of_lt_glamsterdam (before : fork < .glamsterdam)
    (node : ForkChoiceNode) :
    store.latestVerifiedAncestor node =
      (store.latestVerifiedBlock node.root).map (⟨·, node.payloadStatus⟩) := by
  have notGloas : ¬(Fork.glamsterdam ≤ fork) := Nat.not_le_of_lt before
  simp only [latestVerifiedAncestor, notGloas, ↓reduceDIte]
  cases store.latestVerifiedBlock node.root <;> rfl

/-- Before Gloas, the latest verified ancestor is reached through optimistic blocks.

Its block is known, and it is not optimistic or its parent root is zero. -/
theorem latestVerifiedAncestor_spec {node ancestor : ForkChoiceNode}
    (before : fork < .glamsterdam) (found : store.latestVerifiedAncestor node = .ok ancestor) :
    store.OptimisticWalk node.root ancestor.root ∧ ancestor.payloadStatus = node.payloadStatus ∧
      ∃ block, store.blocks[ancestor.root]? = some block ∧
        (store.isOptimistic ancestor.root = false ∨ block.parentRoot = Vector.replicate 32 0) := by
  rw [latestVerifiedAncestor_of_lt_glamsterdam store before] at found
  cases walked : store.latestVerifiedBlock node.root with
  | error => simp [walked, Except.map] at found
  | ok root =>
    simp only [walked, Except.map, Except.ok.injEq] at found
    subst found
    obtain ⟨walk, rest⟩ := latestVerifiedBlock_spec store walked
    exact ⟨walk, rfl, rest⟩

/-- The chain of a block that is not known fails. -/
private theorem chain_of_unknown {root : Root} (unknown : store.blocks[root]? = none) :
    store.chain root = .error (.unknownBlock root) := by
  rw [chain, unknown]
  rfl

/-- The chain of a known block whose parent is not known is the block alone. -/
private theorem chain_of_parent_unknown {root : Root} {block : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (unknown : store.blocks[block.parentRoot]? = none) :
    store.chain root = .ok [root] := by
  rw [chain, known]
  dsimp only
  split
  · rfl
  · simp_all

/-- The chain of a known block whose known parent is at a lower slot. -/
private theorem chain_of_lower {root : Root} {block parent : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) :
    store.chain root = (store.chain block.parentRoot >>= fun rest => pure (root :: rest)) := by
  rw [chain, known]
  dsimp only
  split
  · simp_all
  · rename_i other otherFound
    rw [parentFound, Option.some.injEq] at otherFound
    subst otherFound
    rw [dite_eq_left lower]

/-- The chain of a known block whose known parent is not at a lower slot fails. -/
private theorem chain_of_not_lower {root : Root} {block parent : BeaconBlock preset fork}
    (known : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (notLower : ¬parent.slot < block.slot) :
    store.chain root = .error (.parentSlotNotLower root) := by
  rw [chain, known]
  dsimp only
  split
  · simp_all
  · rename_i other otherFound
    rw [parentFound, Option.some.injEq] at otherFound
    subst otherFound
    rw [dite_eq_right notLower]
    rfl

variable {store} in
/-- The payload chain of a known block can be read when each known parent is at a lower slot. -/
theorem payloadChain_exists
    -- Each known parent of a known block is at a lower slot.
    (lower : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
        parent.slot < block.slot)
    {root : Root} {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block) :
    ∃ roots, store.payloadChain root = .ok roots := by
  -- The chain of a known block exists, by induction on its slot.
  have chainOk : ∀ (n : ℕ) (root : Root) (block : BeaconBlock preset fork),
      block.slot.toNat = n → store.blocks[root]? = some block →
        ∃ roots, store.chain root = .ok roots := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro root block hn found
    cases parentFound : store.blocks[block.parentRoot]? with
    | none => exact ⟨_, chain_of_parent_unknown store found parentFound⟩
    | some parent =>
      have below := lower root block parent found parentFound
      obtain ⟨rest, restOk⟩ := ih parent.slot.toNat
        (hn ▸ UInt64.lt_iff_toNat_lt.mp below) _ parent rfl parentFound
      exact ⟨root :: rest, by
        rw [chain_of_lower store found parentFound below, restOk]; rfl⟩
  obtain ⟨roots, rootsOk⟩ := chainOk _ root block rfl found
  by_cases gloas : .glamsterdam ≤ fork
  · exact ⟨store.payloadsOnChain gloas none roots, by
      simp [payloadChain, rootsOk, gloas, bind, Except.bind, pure, Except.pure]⟩
  · exact ⟨roots, by simp [payloadChain, rootsOk, gloas, bind, Except.bind, pure, Except.pure]⟩

/-- Each root of the chain of a known block is a known block at a slot at most its slot. -/
private theorem chain_slot_le {root : Root} {all : List Root} {block : BeaconBlock preset fork}
    (chained : store.chain root = .ok all) (known : store.blocks[root]? = some block) :
    ∀ other ∈ all, ∃ otherBlock, store.blocks[other]? = some otherBlock ∧
      otherBlock.slot.toNat ≤ block.slot.toNat := by
  induction root using chain.induct (store := store) generalizing all block with
  | case1 root unknown =>
    rw [chain_of_unknown store unknown] at chained
    cases chained
  | case2 root this thisFound unknown =>
    rw [known, Option.some.injEq] at thisFound
    subst thisFound
    rw [chain_of_parent_unknown store known unknown, Except.ok.injEq] at chained
    subst chained
    simp only [List.mem_singleton, forall_eq]
    exact ⟨block, known, Nat.le_refl _⟩
  | case3 root this thisFound parent parentFound lower ih =>
    rw [known, Option.some.injEq] at thisFound
    subst thisFound
    rw [chain_of_lower store known parentFound lower, bind_ok_iff] at chained
    obtain ⟨rest, restOk, chained⟩ := chained
    simp only [pure, Except.pure, Except.ok.injEq] at chained
    subst chained
    intro other mem
    rcases List.mem_cons.mp mem with same | mem
    · subst same
      exact ⟨block, known, Nat.le_refl _⟩
    · obtain ⟨otherBlock, otherFound, le⟩ := ih restOk parentFound other mem
      exact ⟨otherBlock, otherFound,
        Nat.le_trans le (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp lower))⟩
  | case4 root this thisFound parent parentFound notLower =>
    rw [known, Option.some.injEq] at thisFound
    subst thisFound
    rw [chain_of_not_lower store known parentFound notLower] at chained
    cases chained

/-- The chain of a block starts at the block, which is known. -/
private theorem chain_cons {root : Root} {all : List Root} (chained : store.chain root = .ok all) :
    ∃ block tail, store.blocks[root]? = some block ∧ all = root :: tail := by
  cases known : store.blocks[root]? with
  | none =>
    rw [chain_of_unknown store known] at chained
    cases chained
  | some block =>
    cases parentFound : store.blocks[block.parentRoot]? with
    | none =>
      rw [chain_of_parent_unknown store known parentFound, Except.ok.injEq] at chained
      exact ⟨block, [], rfl, chained.symm⟩
    | some parent =>
      by_cases lower : parent.slot < block.slot
      · rw [chain_of_lower store known parentFound lower, bind_ok_iff] at chained
        obtain ⟨rest, _, chained⟩ := chained
        simp only [pure, Except.pure, Except.ok.injEq] at chained
        exact ⟨block, rest, rfl, chained.symm⟩
      · rw [chain_of_not_lower store known parentFound lower] at chained
        cases chained

/-- The chain of a block has no root twice. -/
private theorem chain_nodup {root : Root} {all : List Root} (chained : store.chain root = .ok all) :
    all.Nodup := by
  induction root using chain.induct (store := store) generalizing all with
  | case1 root unknown =>
    rw [chain_of_unknown store unknown] at chained
    cases chained
  | case2 root block known unknown =>
    rw [chain_of_parent_unknown store known unknown, Except.ok.injEq] at chained
    subst chained
    exact List.nodup_singleton _
  | case3 root block known parent parentFound lower ih =>
    rw [chain_of_lower store known parentFound lower, bind_ok_iff] at chained
    obtain ⟨rest, restOk, chained⟩ := chained
    simp only [pure, Except.pure, Except.ok.injEq] at chained
    subst chained
    refine List.nodup_cons.mpr ⟨fun mem => ?_, ih restOk⟩
    obtain ⟨other, otherFound, le⟩ := chain_slot_le store restOk parentFound root mem
    rw [known, Option.some.injEq] at otherFound
    subst otherFound
    exact absurd (UInt64.lt_iff_toNat_lt.mp lower) (Nat.not_lt_of_le le)
  | case4 root block known parent parentFound notLower =>
    rw [chain_of_not_lower store known parentFound notLower] at chained
    cases chained

/-- The chain of a block, from one of its roots on, is the chain of that root. -/
private theorem chain_suffix {root middle : Root} {all : List Root}
    (chained : store.chain root = .ok all) (member : middle ∈ all) :
    ∃ before rest, store.chain middle = .ok rest ∧ all = before ++ rest := by
  induction root using chain.induct (store := store) generalizing all with
  | case1 root unknown =>
    rw [chain_of_unknown store unknown] at chained
    cases chained
  | case2 root block known unknown =>
    have same := chained
    rw [chain_of_parent_unknown store known unknown, Except.ok.injEq] at same
    subst same
    rw [List.mem_singleton] at member
    subst member
    exact ⟨[], _, chained, rfl⟩
  | case3 root block known parent parentFound lower ih =>
    have same := chained
    rw [chain_of_lower store known parentFound lower, bind_ok_iff] at same
    obtain ⟨rest, restOk, same⟩ := same
    simp only [pure, Except.pure, Except.ok.injEq] at same
    subst same
    rcases List.mem_cons.mp member with here | below
    · subst here
      exact ⟨[], _, chained, rfl⟩
    · obtain ⟨before, after, afterOk, split⟩ := ih restOk below
      exact ⟨root :: before, after, afterOk, by rw [split, List.cons_append]⟩
  | case4 root block known parent parentFound notLower =>
    rw [chain_of_not_lower store known parentFound notLower] at chained
    cases chained

/-- The filter of a chain keeps some of its roots, in their order. -/
private theorem payloadsOnChain_sublist (gloas : .glamsterdam ≤ fork) (expected : Option Hash32)
    (roots : List Root) : (store.payloadsOnChain gloas expected roots).Sublist roots := by
  induction roots generalizing expected with
  | nil => exact List.Sublist.slnil
  | cons root rest ih =>
    unfold payloadsOnChain
    split
    · exact (ih expected).cons root
    · dsimp only
      split
      · exact (ih _).cons_cons root
      · exact (ih expected).cons root

/-- From no expected hash, the filter keeps the first root when it is a known block. -/
private theorem payloadsOnChain_none_cons (gloas : .glamsterdam ≤ fork) {root : Root}
    {block : BeaconBlock preset fork} (known : store.blocks[root]? = some block)
    (rest : List Root) :
    store.payloadsOnChain gloas none (root :: rest) =
      root :: store.payloadsOnChain gloas
        (some (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) rest := by
  simp [payloadsOnChain, known]

/-- Each root that the filter keeps first, from an expected hash, has a bid naming that hash. -/
private theorem payloadsOnChain_some_head (gloas : .glamsterdam ≤ fork) {hash : Hash32}
    {roots kept : List Root} {first : Root}
    (filtered : store.payloadsOnChain gloas (some hash) roots = first :: kept) :
    ∃ block, store.blocks[first]? = some block ∧
      (block.body.signedExecutionPayloadBid gloas).message.blockHash = hash := by
  induction roots with
  | nil => simp [payloadsOnChain] at filtered
  | cons root rest ih =>
    unfold payloadsOnChain at filtered
    split at filtered
    · exact ih filtered
    · rename_i block known
      dsimp only at filtered
      split at filtered
      · rename_i named
        simp only [List.cons.injEq] at filtered
        obtain ⟨rfl, -⟩ := filtered
        simp only [Option.all_some, beq_iff_eq] at named
        exact ⟨block, known, named.symm⟩
      · exact ih filtered

/-- When the filter keeps a root that a list holds once, it goes on as from that root alone. -/
private theorem payloadsOnChain_split (gloas : .glamsterdam ≤ fork) {root : Root}
    {block : BeaconBlock preset fork} (known : store.blocks[root]? = some block)
    {before after : List Root} (distinct : (before ++ root :: after).Nodup)
    (expected : Option Hash32)
    (member : root ∈ store.payloadsOnChain gloas expected (before ++ root :: after)) :
    ∃ kept, store.payloadsOnChain gloas expected (before ++ root :: after) =
      kept ++ root :: store.payloadsOnChain gloas
        (some (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) after := by
  induction before generalizing expected with
  | nil =>
    refine ⟨[], ?_⟩
    simp only [List.nil_append] at distinct member ⊢
    simp only [payloadsOnChain, known] at member ⊢
    split at member
    · rename_i named
      simp only [named, ↓reduceIte]
    · exact absurd ((payloadsOnChain_sublist store gloas _ _).subset member)
        (List.nodup_cons.mp distinct).1
  | cons first before ih =>
    simp only [List.cons_append] at distinct member ⊢
    have rest := (List.nodup_cons.mp distinct).2
    cases firstFound : store.blocks[first]? with
    | none =>
      simp only [payloadsOnChain, firstFound] at member ⊢
      exact ih rest expected member
    | some firstBlock =>
      simp only [payloadsOnChain, firstFound] at member ⊢
      split at member
      · rename_i named
        simp only [named, ↓reduceIte]
        rcases List.mem_cons.mp member with same | member
        · subst same
          exact absurd (by simp) (List.nodup_cons.mp distinct).1
        · obtain ⟨kept, split⟩ := ih rest _ member
          exact ⟨first :: kept, by rw [split, List.cons_append]⟩
      · rename_i named
        simp only [named, ↓reduceIte, Bool.false_eq_true]
        exact ih rest expected member

/-- Before Gloas, the payload chain of a block is its chain. -/
theorem payloadChain_of_lt_glamsterdam (before : fork < .glamsterdam) (root : Root) :
    store.payloadChain root = store.chain root := by
  have notGloas : ¬(Fork.glamsterdam ≤ fork) := Nat.not_le_of_lt before
  simp only [payloadChain, notGloas, ↓reduceDIte]
  cases store.chain root <;> rfl

/-- From Gloas, the payload chain of a block is its chain, filtered from no expected hash.

It keeps the ancestors whose payload the chain builds on, linked by their bids. -/
theorem payloadChain_of_glamsterdam (gloas : .glamsterdam ≤ fork) (root : Root) :
    store.payloadChain root = (store.payloadsOnChain gloas none ·) <$> store.chain root := by
  simp only [payloadChain, gloas, ↓reduceDIte]
  cases store.chain root <;> rfl

/-- From Gloas, a payload chain is the filter of the chain of its block from no expected hash. -/
private theorem payloadChain_ok_of_glamsterdam (gloas : .glamsterdam ≤ fork) {root : Root}
    {roots : List Root} (walked : store.payloadChain root = .ok roots) :
    ∃ all, store.chain root = .ok all ∧ roots = store.payloadsOnChain gloas none all := by
  rw [payloadChain_of_glamsterdam store gloas] at walked
  cases chained : store.chain root with
  | error => simp [chained, Functor.map, Except.map] at walked
  | ok all =>
    simp only [chained, Functor.map, Except.map, Except.ok.injEq] at walked
    exact ⟨all, rfl, walked.symm⟩

/-- A payload chain keeps some roots of the chain of its block, in their order. -/
theorem payloadChain_sublist {root : Root} {roots : List Root}
    (walked : store.payloadChain root = .ok roots) :
    ∃ all, store.chain root = .ok all ∧ roots.Sublist all := by
  by_cases gloas : Fork.glamsterdam ≤ fork
  · obtain ⟨all, chained, rfl⟩ := payloadChain_ok_of_glamsterdam store gloas walked
    exact ⟨all, chained, payloadsOnChain_sublist store gloas none all⟩
  · rw [payloadChain_of_lt_glamsterdam store (Nat.lt_of_not_le gloas)] at walked
    exact ⟨roots, walked, List.Sublist.refl _⟩

/-- The payload chain of a block starts at the block. -/
theorem payloadChain_head? {root : Root} {roots : List Root}
    (walked : store.payloadChain root = .ok roots) : roots.head? = some root := by
  by_cases gloas : Fork.glamsterdam ≤ fork
  · obtain ⟨all, chained, rfl⟩ := payloadChain_ok_of_glamsterdam store gloas walked
    obtain ⟨block, tail, known, rfl⟩ := chain_cons store chained
    rw [payloadsOnChain_none_cons store gloas known]
    rfl
  · rw [payloadChain_of_lt_glamsterdam store (Nat.lt_of_not_le gloas)] at walked
    obtain ⟨block, tail, known, rfl⟩ := chain_cons store walked
    rfl

/-- Each root that the filter keeps builds on the payload of the next one it keeps. -/
private theorem payloadsOnChain_links (gloas : .glamsterdam ≤ fork) (expected : Option Hash32)
    (roots : List Root) (i : Nat)
    (next : i + 1 < (store.payloadsOnChain gloas expected roots).length) :
    store.PayloadLink (store.payloadsOnChain gloas expected roots)[i]
      (store.payloadsOnChain gloas expected roots)[i + 1] := by
  suffices key : ∀ kept, store.payloadsOnChain gloas expected roots = kept →
      ∀ i (next : i + 1 < kept.length), store.PayloadLink kept[i] kept[i + 1] from
    key _ rfl i next
  intro kept filtered
  clear next
  induction roots generalizing expected kept with
  | nil =>
    simp only [payloadsOnChain] at filtered
    subst filtered
    intro step next
    simp at next
  | cons root rest ih =>
    cases known : store.blocks[root]? with
    | none =>
      simp only [payloadsOnChain, known] at filtered
      exact ih expected kept filtered
    | some block =>
      simp only [payloadsOnChain, known] at filtered
      split at filtered
      · rename_i named
        subst filtered
        intro step next
        cases step with
        | zero =>
          simp only [List.getElem_cons_zero, List.getElem_cons_succ]
          generalize later : store.payloadsOnChain gloas _ rest = after at next ⊢
          match after, later with
          | first :: _, later =>
            obtain ⟨parent, parentFound, hash⟩ := payloadsOnChain_some_head store gloas later
            refine ⟨block, parent, known, parentFound, ?_⟩
            simp [Store.parentPayloadStatus, gloas, hash]
        | succ step =>
          simp only [List.getElem_cons_succ]
          exact ih _ _ rfl step (by simpa using next)
      · exact ih expected kept filtered

/-- From Gloas, each root of a payload chain builds on the payload of the next one. -/
theorem payloadChain_links (gloas : .glamsterdam ≤ fork) {root : Root} {roots : List Root}
    (walked : store.payloadChain root = .ok roots) (i : Nat) (next : i + 1 < roots.length) :
    store.PayloadLink roots[i] roots[i + 1] := by
  obtain ⟨all, _, rfl⟩ := payloadChain_ok_of_glamsterdam store gloas walked
  exact payloadsOnChain_links store gloas none all i next

/-- From Gloas, the parent of a block is on its payload chain exactly when it builds on its payload.

The fork choice then sees the parent as full. -/
theorem parentRoot_mem_payloadChain_iff (gloas : .glamsterdam ≤ fork) {root : Root}
    {roots : List Root} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (walked : store.payloadChain root = .ok roots) :
    block.parentRoot ∈ roots ↔ Store.parentPayloadStatus block parent = .full := by
  obtain ⟨all, chained, rfl⟩ := payloadChain_ok_of_glamsterdam store gloas walked
  by_cases lower : parent.slot < block.slot
  · rw [chain_of_lower store found parentFound lower, bind_ok_iff] at chained
    obtain ⟨rest, restOk, chained⟩ := chained
    simp only [pure, Except.pure, Except.ok.injEq] at chained
    subst chained
    obtain ⟨parent', tail, parentFound', rfl⟩ := chain_cons store restOk
    have distinct := chain_nodup store restOk
    rw [payloadsOnChain_none_cons store gloas found]
    simp only [payloadsOnChain, parentFound]
    simp only [Store.parentPayloadStatus, gloas, dite_true]
    by_cases named : (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash =
        (parent.body.signedExecutionPayloadBid gloas).message.blockHash
    · simp [named]
    · simp only [Option.all_some, named, beq_iff_eq, ↓reduceIte,
        reduceCtorEq, iff_false, List.mem_cons, not_or]
      refine ⟨fun same => ?_, fun member => ?_⟩
      · rw [same, found, Option.some.injEq] at parentFound
        subst parentFound
        exact Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp lower)
      · exact (List.nodup_cons.mp distinct).1
          ((payloadsOnChain_sublist store gloas _ tail).subset member)
  · rw [chain_of_not_lower store found parentFound lower] at chained
    cases chained

/-- Dropping the roots that fail a test leaves nothing when no root passes it. -/
private theorem dropWhile_not_of_find?_eq_none {test : Root → Bool} {roots : List Root}
    (missing : roots.find? test = none) : (roots.dropWhile fun root => !test root) = [] := by
  -- Every root fails the test, so the whole list is dropped.
  have dropped : ((roots ++ []).dropWhile fun root => !test root) = [] :=
    List.dropWhile_append_of_pos fun root member => by
      simpa using List.find?_eq_none.mp missing root member
  simpa using dropped

/-- Dropping the roots that fail a test leaves the first root that passes it and the rest. -/
private theorem dropWhile_not_of_find?_eq_some {test : Root → Bool} {roots : List Root}
    {first : Root} (search : roots.find? test = some first) :
    ∃ before after, roots = before ++ first :: after ∧
      (roots.dropWhile fun root => !test root) = first :: after := by
  -- The roots before the first passing one all fail the test, so they are dropped.
  obtain ⟨passed, before, after, split, failed⟩ := List.find?_eq_some_iff_append.mp search
  refine ⟨before, after, split, ?_⟩
  rw [split, List.dropWhile_append_of_pos fun root member => by simpa using failed root member,
    List.dropWhile_cons_of_neg (by simpa using passed)]

/-- In a list without repeated roots, what follows a root is fixed by the list. -/
private theorem suffix_eq_of_nodup {middle : Root} {before after other rest : List Root}
    (distinct : (before ++ middle :: after).Nodup)
    (same : before ++ middle :: after = other ++ middle :: rest) : after = rest := by
  induction before generalizing other with
  | nil =>
    cases other with
    | nil => simpa using same
    | cons first other =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact absurd (by simp) (List.nodup_cons.mp distinct).1
  | cons first before ih =>
    cases other with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at same
      obtain ⟨rfl, -⟩ := same
      exact absurd (by simp) (List.nodup_cons.mp distinct).1
    | cons second other =>
      simp only [List.cons_append, List.cons.injEq] at same
      exact ih (List.nodup_cons.mp distinct).2 same.2

/-- From an expected hash, the filter skips the roots before the first whose bid names it. -/
private theorem payloadsOnChain_some (gloas : .glamsterdam ≤ fork) (hash : Hash32)
    (roots : List Root) :
    store.payloadsOnChain gloas (some hash) roots = store.payloadsOnChain gloas none
      (roots.dropWhile fun ancestor => !(store.blocks[ancestor]?).any fun known =>
        (known.body.signedExecutionPayloadBid gloas).message.blockHash == hash) := by
  induction roots with
  | nil => rfl
  | cons root rest ih =>
    cases known : store.blocks[root]? with
    | none => simpa [payloadsOnChain, known] using ih
    | some block =>
      by_cases named : (block.body.signedExecutionPayloadBid gloas).message.blockHash = hash
      · simp [payloadsOnChain, known, named]
      · simpa [payloadsOnChain, known, named, Ne.symm named] using ih

/-- From Gloas, the payload chain of a block continues at the first root of its chain that it names.

That root is the first ancestor whose bid names the parent block hash of the bid of the block. -/
private theorem payloadChain_eq_cons (gloas : .glamsterdam ≤ fork) {root : Root}
    {block : BeaconBlock preset fork} {all : List Root}
    (found : store.blocks[root]? = some block) (chained : store.chain root = .ok (root :: all)) :
    store.payloadChain root = .ok (root ::
      match all.find? (fun ancestor => (store.blocks[ancestor]?).any fun known =>
          (known.body.signedExecutionPayloadBid gloas).message.blockHash ==
            (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) with
      | none => []
      | some next => (store.payloadChain next).toOption.getD []) := by
  rw [payloadChain_of_glamsterdam store gloas, chained]
  show Except.ok (store.payloadsOnChain gloas none (root :: all)) = _
  rw [payloadsOnChain_none_cons store gloas found, payloadsOnChain_some store gloas]
  congr 2
  split
  · rename_i missing
    rw [dropWhile_not_of_find?_eq_none missing]
    rfl
  · rename_i next search
    obtain ⟨before, after, split, dropped⟩ := dropWhile_not_of_find?_eq_some search
    rw [dropped]
    have member : next ∈ root :: all := by simp [split]
    obtain ⟨other, rest, restOk, whole⟩ := chain_suffix store chained member
    obtain ⟨nextBlock, tail, -, rfl⟩ := chain_cons store restOk
    have distinct := chain_nodup store chained
    rw [split, ← List.cons_append] at distinct whole
    rw [suffix_eq_of_nodup distinct whole, payloadChain_of_glamsterdam store gloas, restOk]
    rfl

/-- From Gloas, the payload chain of a block goes on at the first ancestor that its bid names.

That ancestor is the first root of the chain below the block whose bid names the parent block hash.

Its chain and its payload chain are found, and the payload chain of the block is the block on it. -/
theorem payloadChain_of_find?_some (gloas : .glamsterdam ≤ fork) {root next : Root}
    {block : BeaconBlock preset fork} {all : List Root}
    (found : store.blocks[root]? = some block) (chained : store.chain root = .ok (root :: all))
    (named : all.find? (store.namesBlockHash gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = some next) :
    ∃ nextBlock rest, store.blocks[next]? = some nextBlock ∧
      store.chain next = .ok (next :: rest) ∧
      ∃ tail, store.payloadChain next = .ok tail ∧
        store.payloadChain root = .ok (root :: tail) := by
  have member : next ∈ root :: all := List.mem_cons_of_mem _ (List.mem_of_find?_eq_some named)
  obtain ⟨-, rest, restOk, -⟩ := chain_suffix store chained member
  obtain ⟨nextBlock, tail, nextFound, rfl⟩ := chain_cons store restOk
  have walked :
      store.payloadChain next = .ok (store.payloadsOnChain gloas none (next :: tail)) := by
    rw [payloadChain_of_glamsterdam store gloas, restOk]
    rfl
  refine ⟨nextBlock, tail, nextFound, restOk, _, walked, ?_⟩
  have cons := payloadChain_eq_cons store gloas found chained
  rw [show all.find? (fun ancestor => (store.blocks[ancestor]?).any fun known =>
      (known.body.signedExecutionPayloadBid gloas).message.blockHash ==
        (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = some next
    from named] at cons
  rw [cons]
  simp only [walked]
  rfl

/-- From Gloas, the payload chain of a block is the block alone when no ancestor is named.

No root of the chain below the block has a bid that names the parent block hash of the block. -/
theorem payloadChain_of_find?_none (gloas : .glamsterdam ≤ fork) {root : Root}
    {block : BeaconBlock preset fork} {all : List Root}
    (found : store.blocks[root]? = some block) (chained : store.chain root = .ok (root :: all))
    (unnamed : all.find? (store.namesBlockHash gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = none) :
    store.payloadChain root = .ok [root] := by
  have cons := payloadChain_eq_cons store gloas found chained
  rw [show all.find? (fun ancestor => (store.blocks[ancestor]?).any fun known =>
      (known.body.signedExecutionPayloadBid gloas).message.blockHash ==
        (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = none
    from unnamed] at cons
  exact cons

/-- The payload chain of a block, from one of its roots on, is the payload chain of that root.

So a payload that builds on a payload of the chain also builds on every payload below it. -/
theorem payloadChain_suffix {root middle : Root} {roots : List Root}
    (walked : store.payloadChain root = .ok roots) (member : middle ∈ roots) :
    ∃ before rest, store.payloadChain middle = .ok rest ∧ roots = before ++ rest := by
  by_cases gloas : Fork.glamsterdam ≤ fork
  · obtain ⟨all, chained, rfl⟩ := payloadChain_ok_of_glamsterdam store gloas walked
    have inAll := (payloadsOnChain_sublist store gloas none all).subset member
    obtain ⟨before, rest, restOk, split⟩ := chain_suffix store chained inAll
    obtain ⟨middleBlock, tail, middleFound, rfl⟩ := chain_cons store restOk
    have distinct := chain_nodup store chained
    subst split
    obtain ⟨kept, filtered⟩ :=
      payloadsOnChain_split store gloas middleFound distinct none member
    refine ⟨kept, _, ?_, filtered⟩
    rw [payloadChain_of_glamsterdam store gloas, restOk,
      ← payloadsOnChain_none_cons store gloas middleFound]
    rfl
  · rw [payloadChain_of_lt_glamsterdam store (Nat.lt_of_not_le gloas)] at walked ⊢
    exact chain_suffix store walked member

/-- A root on the payload chain of a root on the payload chain of a block is on the latter. -/
theorem mem_payloadChain_trans {root middle last : Root} {roots rest : List Root}
    (walked : store.payloadChain root = .ok roots) (member : middle ∈ roots)
    (inner : store.payloadChain middle = .ok rest) (onInner : last ∈ rest) : last ∈ roots := by
  obtain ⟨before, after, afterOk, split⟩ := payloadChain_suffix store walked member
  rw [inner, Except.ok.injEq] at afterOk
  subst afterOk split
  exact List.mem_append_right before onInner

/-- From Gloas, the latest verified ancestor of a node walks the nodes of the fork choice. -/
theorem latestVerifiedAncestor_of_glamsterdam (gloas : .glamsterdam ≤ fork)
    (node : ForkChoiceNode) :
    store.latestVerifiedAncestor node = store.latestVerifiedNode gloas node := by
  simp only [latestVerifiedAncestor, gloas, ↓reduceDIte]

/-- From Gloas, the latest verified node has a known block, and is not optimistic or is of genesis.

A node of genesis has a block whose parent root is zero.

It is pending, or builds on a payload that is not optimistic. -/
theorem latestVerifiedNode_spec (gloas : .glamsterdam ≤ fork) {node ancestor : ForkChoiceNode}
    (found : store.latestVerifiedNode gloas node = .ok ancestor) :
    ∃ block, store.blocks[ancestor.root]? = some block ∧
      (store.isNodeOptimistic gloas ancestor = .ok false ∨
        block.parentRoot = Vector.replicate 32 0 ∧ (ancestor.payloadStatus = .pending ∨
          store.isOptimisticPayload gloas
            (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = false)) := by
  induction node using latestVerifiedNode.induct (store := store) (gloas := gloas)
    generalizing ancestor with
  | case1 node nf =>
    rw [latestVerifiedNode] at found
    split at found <;> simp_all [throw, throwThe, MonadExceptOf.throw]
  | case2 node block nf bid h =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      have verified : store.isNodeOptimistic gloas node = .ok false := by
        simp_all [isNodeOptimistic, bid, pure, Except.pure]
      have optimistic : (!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.blockHash) = true := h.2
      simp only [h.1, optimistic, and_self, ↓reduceIte, pure, Except.pure] at found
      cases found
      exact ⟨block, nf, Or.inl verified⟩
  | case3 node block nf bid h genesis =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      simp only [genesis, ↓reduceIte, pure, Except.pure] at found
      split_ifs at found with first stays
      · exact absurd first h
      · cases found
        exact ⟨block, nf, Or.inr ⟨genesis, Or.inr (by simpa using stays.2)⟩⟩
      · cases found
        exact ⟨block, nf, Or.inr ⟨genesis, Or.inl rfl⟩⟩
  | case4 node block nf bid h genesis unknown =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      split_ifs at found <;> simp_all [bid, throw, throwThe, MonadExceptOf.throw]
  | case5 node block nf bid h genesis known verified =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      have notVerified : ¬(node.payloadStatus = .full ∧ (!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.blockHash) = true) := h
      have knows : ¬(!store.knowsPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := known
      have optimistic : (!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := verified
      simp only [notVerified, genesis, knows, optimistic, Bool.false_eq_true, ↓reduceIte, pure,
        Except.pure] at found
      have current := Except.ok.inj found
      subst current
      refine ⟨block, ?_, Or.inl ?_⟩
      · by_cases full : node.payloadStatus = .full <;> simp [full, nf]
      · by_cases full : node.payloadStatus = .full
        · simp_all [isNodeOptimistic, bid, pure, Except.pure]
        · cases status : node.payloadStatus <;>
            simp_all [isNodeOptimistic, bid, pure, Except.pure]
  | case6 node block nf bid h genesis known verified pf =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      have notVerified : ¬(node.payloadStatus = .full ∧ (!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.blockHash) = true) := h
      have knows : ¬(!store.knowsPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := known
      have optimistic : ¬(!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := verified
      simp only [notVerified, genesis, knows, optimistic, Bool.false_eq_true, ↓reduceIte] at found
      split at found
      all_goals simp_all [throw, throwThe, MonadExceptOf.throw]
  | case7 node block nf bid h genesis known verified parent pf lower ih =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      have notVerified : ¬(node.payloadStatus = .full ∧ (!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.blockHash) = true) := h
      have knows : ¬(!store.knowsPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := known
      have optimistic : ¬(!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := verified
      simp only [notVerified, genesis, knows, optimistic, Bool.false_eq_true, ↓reduceIte] at found
      split at found
      · simp_all
      · rename_i other otherFound
        rw [pf, Option.some.injEq] at otherFound
        subst otherFound
        simp only [lower, ↓reduceDIte] at found
        exact ih found
  | case8 node block nf bid h genesis known verified parent pf lower =>
    rw [latestVerifiedNode] at found
    split at found
    · simp_all
    · rename_i other otherFound
      rw [nf, Option.some.injEq] at otherFound
      subst otherFound
      have notVerified : ¬(node.payloadStatus = .full ∧ (!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.blockHash) = true) := h
      have knows : ¬(!store.knowsPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := known
      have optimistic : ¬(!store.isOptimisticPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) = true := verified
      simp only [notVerified, genesis, knows, optimistic, Bool.false_eq_true, ↓reduceIte] at found
      split at found
      · simp_all
      · rename_i other otherFound
        rw [pf, Option.some.injEq] at otherFound
        subst otherFound
        simp only [lower, ↓reduceDIte] at found
        simp [throw, throwThe, MonadExceptOf.throw] at found

/-- From Gloas, a node that is not optimistic is its own latest verified ancestor. -/
theorem latestVerifiedNode_of_not_optimistic (gloas : .glamsterdam ≤ fork)
    {node : ForkChoiceNode} (verified : store.isNodeOptimistic gloas node = .ok false) :
    store.latestVerifiedNode gloas node = .ok node := by
  cases found : store.blocks[node.root]? with
  | none =>
    simp [isNodeOptimistic, found, throw, throwThe, MonadExceptOf.throw] at verified
  | some block =>
    rw [latestVerifiedNode]
    split
    · simp_all
    · rename_i other otherFound
      rw [found, Option.some.injEq] at otherFound
      subst otherFound
      simp only [isNodeOptimistic, found, bind, Except.bind] at verified
      cases status : node.payloadStatus <;>
        by_cases known : store.knowsPayload gloas
          (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = true <;>
        simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]


/-- From Gloas, an optimistic full node walks on as the pending node of its block. -/
theorem latestVerifiedNode_of_full_optimistic (gloas : .glamsterdam ≤ fork)
    {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    (found : store.blocks[node.root]? = some block) (full : node.payloadStatus = .full)
    (optimistic : store.isOptimisticPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.blockHash = true) :
    store.latestVerifiedNode gloas node = store.latestVerifiedNode gloas ⟨node.root, .pending⟩ := by
  conv_rhs => rw [latestVerifiedNode]
  split
  next missing => simp_all
  next other otherFound =>
    rw [found, Option.some.injEq] at otherFound
    subst otherFound
    conv_lhs => rw [latestVerifiedNode]
    split
    next missing => simp_all
    next again againFound =>
      rw [found, Option.some.injEq] at againFound
      subst againFound
      simp [full, optimistic]

/-- From Gloas, an optimistic node that is not full climbs to the node of its parent.

The block is not of genesis, and the store knows the payload it builds on and the parent. -/
theorem latestVerifiedNode_climb (gloas : .glamsterdam ≤ fork) {node : ForkChoiceNode}
    {block parent : BeaconBlock preset fork} (found : store.blocks[node.root]? = some block)
    (notFull : node.payloadStatus ≠ .full)
    (notGenesis : block.parentRoot ≠ Vector.replicate 32 0)
    (known : store.knowsPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = true)
    (optimistic : store.isOptimisticPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = true)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) :
    store.latestVerifiedNode gloas node =
      store.latestVerifiedNode gloas
        ⟨block.parentRoot, Store.parentPayloadStatus block parent⟩ := by
  conv_lhs => rw [latestVerifiedNode]
  split
  · simp_all
  · rename_i other otherFound
    rw [found, Option.some.injEq] at otherFound
    subst otherFound
    simp only [notFull, false_and, ↓reduceIte, notGenesis, known, optimistic, Bool.not_true,
      Bool.false_eq_true]
    split
    · simp_all
    · rename_i other otherFound
      rw [parentFound, Option.some.injEq] at otherFound
      subst otherFound
      simp only [lower, ↓reduceDIte]

/-- Before Gloas, the head is optimistic exactly when its block is, whatever its status. -/
theorem isHeadOptimistic_of_lt_glamsterdam (before : fork < .glamsterdam) :
    store.isHeadOptimistic = .ok (store.isOptimistic store.head.root) := by
  have notGloas : ¬(Fork.glamsterdam ≤ fork) := Nat.not_le_of_lt before
  simp only [isHeadOptimistic, notGloas, ↓reduceDIte]
  rfl

/-- From Gloas, a full head is optimistic exactly when the payload its bid names is. -/
theorem isHeadOptimistic_of_full (gloas : .glamsterdam ≤ fork)
    (full : store.head.payloadStatus = .full) {block : BeaconBlock preset fork}
    (found : store.blocks[store.head.root]? = some block) :
    store.isHeadOptimistic = .ok (store.isOptimisticPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.blockHash) := by
  simp only [isHeadOptimistic, isNodeOptimistic, gloas, ↓reduceDIte, found, full]
  rfl

/-- From Gloas, an empty or pending head is optimistic exactly when the payload it builds on is.

That payload is the one whose block hash is the parent block hash of the bid of the head.

A known block must name it. -/
theorem isHeadOptimistic_of_not_full (gloas : .glamsterdam ≤ fork)
    (notFull : store.head.payloadStatus ≠ .full) {block : BeaconBlock preset fork}
    (found : store.blocks[store.head.root]? = some block)
    (known : store.knowsPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = true) :
    store.isHeadOptimistic = .ok (store.isOptimisticPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash) := by
  simp only [isHeadOptimistic, isNodeOptimistic, gloas, ↓reduceDIte, found]
  cases status : store.head.payloadStatus
  · simp [known]
    rfl
  · exact absurd status notFull
  · simp [known]
    rfl

/-- From Gloas, an empty or pending head fails when no known block names the payload it builds on.

The store then cannot tell whether that payload is verified. -/
theorem isHeadOptimistic_of_not_full_of_unknown_payload (gloas : .glamsterdam ≤ fork)
    (notFull : store.head.payloadStatus ≠ .full) {block : BeaconBlock preset fork}
    (found : store.blocks[store.head.root]? = some block)
    (unknown : store.knowsPayload gloas
      (block.body.signedExecutionPayloadBid gloas).message.parentBlockHash = false) :
    store.isHeadOptimistic = .error (.payloadNotVerified store.head.root) := by
  simp only [isHeadOptimistic, isNodeOptimistic, gloas, ↓reduceDIte, found]
  cases status : store.head.payloadStatus
  · simp [unknown]
    rfl
  · exact absurd status notFull
  · simp [unknown]
    rfl

/-- From Gloas, the head rule fails at a head block that the store does not know. -/
theorem isHeadOptimistic_of_unknown (gloas : .glamsterdam ≤ fork)
    (missing : store.blocks[store.head.root]? = none) :
    store.isHeadOptimistic = .error (.unknownBlock store.head.root) := by
  simp only [isHeadOptimistic, isNodeOptimistic, gloas, ↓reduceDIte, missing]
  rfl

/-- From Gloas, a payload is optimistic exactly when an optimistic root names its block hash. -/
theorem isOptimisticPayload_eq_true_iff (gloas : .glamsterdam ≤ fork) {hash : Hash32} :
    store.isOptimisticPayload gloas hash = true ↔
      ∃ root ∈ store.optimisticRoots, store.namesBlockHash gloas hash root = true := by
  simp only [isOptimisticPayload, List.any_eq_true]

/-- From Gloas, a payload is optimistic as a block that names it is, when no other root does.

So the read by block hash and the read by root agree when no two optimistic roots share a payload.
-/
theorem isOptimisticPayload_eq_isOptimistic (gloas : .glamsterdam ≤ fork) {hash : Hash32}
    {root : Root} (named : store.namesBlockHash gloas hash root = true)
    (only : ∀ other ∈ store.optimisticRoots,
      store.namesBlockHash gloas hash other = true → other = root) :
    store.isOptimisticPayload gloas hash = store.isOptimistic root := by
  apply Bool.eq_iff_iff.mpr
  rw [isOptimisticPayload_eq_true_iff store gloas]
  simp only [isOptimistic, List.contains_iff_mem]
  constructor
  · rintro ⟨other, mem, names⟩
    rwa [← only other mem names]
  · intro mem
    exact ⟨root, mem, named⟩

/-- The roots of a payload chain are distinct. -/
theorem payloadChain_nodup {root : Root} {roots : List Root}
    (walked : store.payloadChain root = .ok roots) : roots.Nodup := by
  obtain ⟨all, chained, sublist⟩ := payloadChain_sublist store walked
  exact sublist.nodup (chain_nodup store chained)

/-- A valid payload removes exactly the roots of its payload chain from the optimistic set.

Those are the block and its known ancestors whose payloads it builds on.

Before Gloas they are all its known ancestors.

The head and the blocks stay as they were. -/
theorem onValidPayload_spec {root : Root} {after : OptimisticStore preset fork}
    (updated : store.onValidPayload root = .ok after) :
    ∃ ancestors, store.payloadChain root = .ok ancestors ∧
      (∀ optimistic, optimistic ∈ after.optimisticRoots ↔
        optimistic ∈ store.optimisticRoots ∧ optimistic ∉ ancestors) ∧
      after.head = store.head ∧ after.blocks = store.blocks := by
  simp only [onValidPayload, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at updated
  obtain ⟨ancestors, chained, rfl⟩ := updated
  refine ⟨ancestors, chained, fun optimistic => ?_, rfl, rfl⟩
  simp

/-- The first invalid block removes exactly the optimistic roots whose payload chain holds it.

Those are the first invalid block and its known descendants that build on its payload.

Before Gloas these are all its known descendants.

Every other root stays, and so do the head and the blocks. -/
theorem onInvalidatedPayload_spec {first : Root} {after : OptimisticStore preset fork}
    (updated : store.onInvalidatedPayload first = .ok after) :
    (∀ optimistic, optimistic ∈ after.optimisticRoots ↔
      optimistic ∈ store.optimisticRoots ∧
        ∃ chain, store.payloadChain optimistic = .ok chain ∧ first ∉ chain) ∧
      after.head = store.head ∧ after.blocks = store.blocks := by
  simp only [onInvalidatedPayload, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at updated
  obtain ⟨kept, keptOk, rfl⟩ := updated
  refine ⟨fun optimistic => ?_, rfl, rfl⟩
  rw [mem_filterMapM_ok keptOk]
  constructor
  · rintro ⟨root, member, checked⟩
    cases chained : store.payloadChain root with
    | error => simp [chained, bind, Except.bind] at checked
    | ok chain =>
      by_cases holds : first ∈ chain
      · simp [chained, holds, bind, Except.bind] at checked
      · simp only [chained, holds, bind, Except.bind, List.contains_iff_mem, ↓reduceIte,
          Except.ok.injEq, Option.some.injEq] at checked
        subst checked
        exact ⟨member, chain, chained, holds⟩
  · rintro ⟨member, chain, chained, holds⟩
    refine ⟨optimistic, member, ?_⟩
    simp [chained, holds, bind, Except.bind]

end OptimisticStore

namespace Store

variable {config : Config} {store : Store preset fork}

variable (config store) in
/-- A leaf that agrees with the checkpoints, reached from a node through children. -/
inductive ViableLeafAbove : ForkChoiceNode → ForkChoiceNode → Prop where
  /-- A node without children that agrees with the checkpoints is its own viable leaf. -/
  | leaf {node : ForkChoiceNode} : store.getNodeChildren node = .ok [] →
      store.isViableLeaf config node = .ok true → ViableLeafAbove node node
  /-- A viable leaf of a child is a viable leaf of its parent. -/
  | child {node child leaf : ForkChoiceNode} {children : List ForkChoiceNode} :
      store.getNodeChildren node = .ok children → child ∈ children →
      ViableLeafAbove child leaf → ViableLeafAbove node leaf

/-- A tree filtered from a node is non-empty exactly when a viable leaf is reached from it. -/
private theorem filterNodeTree_ne_nil_iff :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes →
      (nodes ≠ [] ↔ ∃ leaf, store.ViableLeafAbove config node leaf) := by
  intro node
  induction hrank : store.nodeRank node using Nat.strong_induction_on generalizing node with
  | _ rank ih =>
  intro nodes walk
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  by_cases empty : children.isEmpty
  · have nil : children = [] := List.isEmpty_iff.mp empty
    subst nil
    simp only [empty, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, viableOk, rfl⟩ := walk
    constructor
    · intro ne
      cases isViable
      · exact absurd rfl ne
      · exact ⟨node, .leaf childrenOk viableOk⟩
    · rintro ⟨leaf, reach⟩
      cases reach with
      | leaf _ ok =>
        rw [viableOk, Except.ok.injEq] at ok
        subst ok
        simp
      | child ok mem _ =>
        rw [childrenOk, Except.ok.injEq] at ok
        subst ok
        cases mem
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at walk
  obtain ⟨viable, viableOk, rfl⟩ := walk
  have below_iff : ∀ child ∈ children, ∀ below,
      store.nodeRank child < store.nodeRank node → store.filterNodeTree config child = .ok below →
        (below ≠ [] ↔ ∃ leaf, store.ViableLeafAbove config child leaf) :=
    fun child _ below lower belowOk => ih _ (hrank ▸ lower) rfl belowOk
  constructor
  · intro ne
    have ne' : viable ≠ [] := fun h => ne (by simp [h])
    obtain ⟨y, yMem⟩ := List.exists_mem_of_ne_nil _ ne'
    obtain ⟨child, childMem, below, belowOk, yBelow⟩ := (mem_of_flatMapM_ok viableOk y).mp yMem
    split at belowOk
    · rename_i lower
      obtain ⟨leaf, reach⟩ := (below_iff child childMem below lower belowOk).mp
        (List.ne_nil_of_mem yBelow)
      exact ⟨leaf, .child childrenOk childMem reach⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · rintro ⟨leaf, reach⟩
    cases reach with
    | leaf nil _ =>
      rw [childrenOk, Except.ok.injEq] at nil
      subst nil
      simp at empty
    | child ok childMem reach =>
      rw [childrenOk, Except.ok.injEq] at ok
      subst ok
      obtain ⟨below, belowOk⟩ := flatMapM_ok_of_mem viableOk _ childMem
      split at belowOk
      · rename_i lower
        have nonempty := (below_iff _ childMem below lower belowOk).mpr ⟨leaf, reach⟩
        obtain ⟨y, yBelow⟩ := List.exists_mem_of_ne_nil _ nonempty
        have yMem := (mem_of_flatMapM_ok viableOk y).mpr
          ⟨_, childMem, below, by simp [lower, belowOk], yBelow⟩
        have ne' : viable ≠ [] := List.ne_nil_of_mem yMem
        simp [ne']
      · simp [throw, throwThe, MonadExceptOf.throw] at belowOk

/-- A tree filtered from a node is empty exactly when no viable leaf is reached from it. -/
theorem filterNodeTree_eq_nil_iff {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (tree : store.filterNodeTree config node = .ok nodes) :
    nodes = [] ↔ ¬∃ leaf, store.ViableLeafAbove config node leaf := by
  rw [← filterNodeTree_ne_nil_iff tree]
  exact not_not.symm

/-- When the justified block was dropped, the tree has no viable branch. -/
theorem hasNoViableBranch_of_not_contains
    (dropped : store.blocks.contains store.justifiedCheckpoint.root = false) :
    store.hasNoViableBranch config = .ok true := by
  simp [hasNoViableBranch, dropped]
  rfl

/-- With the justified block known, the second case holds exactly when no viable leaf is reached.

The leaves are reached from the justified block, and the filter of the tree must succeed. -/
theorem hasNoViableBranch_eq_ok_true_iff
    (known : store.blocks.contains store.justifiedCheckpoint.root = true)
    {nodes : List ForkChoiceNode} (tree : store.getFilteredNodeTree config = .ok nodes) :
    store.hasNoViableBranch config = .ok true ↔
      ¬∃ leaf, store.ViableLeafAbove config ⟨store.justifiedCheckpoint.root, .pending⟩ leaf := by
  rw [← filterNodeTree_eq_nil_iff tree]
  simp [hasNoViableBranch, known, tree, bind, Except.bind, pure, Except.pure]

end Store

/-- A node whose head is optimistic is an optimistic node, whatever its tree, at every fork. -/
theorem isOptimisticNode_of_isHeadOptimistic {config : Config}
    {optimistic : OptimisticStore preset fork} (store : Store preset fork)
    (head : optimistic.isHeadOptimistic = .ok true) :
    isOptimisticNode config optimistic store = .ok true := by
  simp only [isOptimisticNode, head, bind, Except.bind, ↓reduceIte]
  rfl

/-- A node fails, at every fork, as the optimism of its head fails. -/
theorem isOptimisticNode_of_isHeadOptimistic_error {config : Config}
    {optimistic : OptimisticStore preset fork} (store : Store preset fork)
    {error : ForkChoiceError} (failed : optimistic.isHeadOptimistic = .error error) :
    isOptimisticNode config optimistic store = .error error := by
  simp only [isOptimisticNode, failed, bind, Except.bind]

/-- At every fork, a node whose head is not optimistic is optimistic exactly in the second case.

That case needs a dropped block at or above the justified block, then no viable branch. -/
theorem isOptimisticNode_of_not_isHeadOptimistic {config : Config}
    {optimistic : OptimisticStore preset fork} (store : Store preset fork)
    (head : optimistic.isHeadOptimistic = .ok false)
    {dropped : Bool} (found : optimistic.invalidatedAbove store = .ok dropped) :
    isOptimisticNode config optimistic store =
      if dropped then store.hasNoViableBranch config else .ok false := by
  cases dropped
  · simp [isOptimisticNode, head, found, bind, Except.bind]
    rfl
  · simp [isOptimisticNode, head, found, bind, Except.bind]

/-- The execution layer of the sources of a payload whose status is not valid.

It accepts every payload exactly when the payload is not yet validated. -/
@[simp]
theorem BlockSources.withPayloadStatus_engine_of_ne (sources : BlockSources preset fork)
    {status : PayloadValidationStatus} (notValid : status ≠ PAYLOAD_STATUS_VALID) :
    (sources.withPayloadStatus status).engine =
      .constant (decide (status = PAYLOAD_STATUS_NOT_VALIDATED)) := by
  simp [BlockSources.withPayloadStatus, notValid]

/-- The answer on the inclusion lists of the sources of a payload whose status is not valid.

The payload satisfies its lists exactly when it is not yet validated. -/
@[simp]
theorem BlockSources.withPayloadStatus_inclusionListSatisfied_of_ne
    (sources : BlockSources preset fork) {status : PayloadValidationStatus}
    (notValid : status ≠ PAYLOAD_STATUS_VALID) :
    (sources.withPayloadStatus status).inclusionListSatisfied =
      fun _ _ => decide (status = PAYLOAD_STATUS_NOT_VALIDATED) := by
  simp [BlockSources.withPayloadStatus, notValid]

/-- An invalidated payload counts as not satisfying its inclusion lists. -/
theorem BlockSources.withPayloadStatus_invalidated (sources : BlockSources preset fork) :
    (sources.withPayloadStatus PAYLOAD_STATUS_INVALIDATED).inclusionListSatisfied =
      fun _ _ => false := by
  simp [BlockSources.withPayloadStatus, PAYLOAD_STATUS_INVALIDATED, PAYLOAD_STATUS_VALID,
    PAYLOAD_STATUS_NOT_VALIDATED]

/-- From Gloas: an envelope whose payload is invalidated is rejected.

From Heze, an envelope for a block whose payload the store holds is skipped before any check. -/
theorem Store.onExecutionPayloadEnvelope_ne_ok_of_invalidated {config : Config}
    {store : Store preset fork} {checks : SignatureChecks} {sources : BlockSources preset fork}
    {gloas : .glamsterdam ≤ fork} {signed : SignedExecutionPayloadEnvelope preset fork}
    -- From Heze, the store holds no payload for this block yet.
    (fresh : .hegota ≤ fork →
      store.isPayloadVerified gloas signed.message.beaconBlockRoot = false)
    (after : Store preset fork) :
    store.onExecutionPayloadEnvelope config checks
      (sources.withPayloadStatus PAYLOAD_STATUS_INVALIDATED) gloas signed ≠ .ok after := by
  intro accepted
  obtain ⟨_, _, _, verified, _⟩ := Store.onExecutionPayloadEnvelope_ok fresh accepted
  rw [BlockSources.withPayloadStatus_engine_of_ne sources (by decide)] at verified
  exact verifyExecutionPayloadEnvelope_constant_false verified

/-- From Heze: a new payload kept before it is validated counts as satisfying its lists. -/
theorem Store.isPayloadInclusionListSatisfied_of_notValidated {config : Config}
    {store : Store preset fork} {checks : SignatureChecks} {sources : BlockSources preset fork}
    {gloas : .glamsterdam ≤ fork} (heze : .hegota ≤ fork)
    {signed : SignedExecutionPayloadEnvelope preset fork} {after : Store preset fork}
    -- The store holds no payload for this block yet.
    (fresh : store.isPayloadVerified gloas signed.message.beaconBlockRoot = false)
    (accepted : store.onExecutionPayloadEnvelope config checks
      (sources.withPayloadStatus PAYLOAD_STATUS_NOT_VALIDATED) gloas signed = .ok after) :
    after.isPayloadInclusionListSatisfied heze signed.message.beaconBlockRoot = .ok true := by
  obtain ⟨_, _, _, _, _, _, satisfied⟩ :=
    Store.onExecutionPayloadEnvelope_inclusionListSatisfied heze fresh accepted
  rw [satisfied, BlockSources.withPayloadStatus_inclusionListSatisfied_of_ne sources (by decide)]
  rfl

/-- From Heze: once a payload turns valid, the store holds the answer of the execution layer.

The store keeps the payload of the block, so the answer is also what the fork choice reads. -/
theorem Store.recordValidatedInclusionListSatisfaction_satisfied {store : Store preset fork}
    {heze : .hegota ≤ fork} {root : Root} {satisfied : Bool} {after : Store preset fork}
    (recorded : store.recordValidatedInclusionListSatisfaction heze root satisfied = .ok after) :
    (after.payloadInclusionListSatisfaction heze)[root]? = some satisfied ∧
      after.isPayloadInclusionListSatisfied heze root = .ok satisfied := by
  unfold recordValidatedInclusionListSatisfaction at recorded
  by_cases held : store.isPayloadVerified (Nat.le_trans (by decide) heze) root = true
  · simp only [held, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recorded
    subst recorded
    refine ⟨by simp, ?_⟩
    simp_all [isPayloadInclusionListSatisfied, isPayloadVerified, pure, Except.pure]
  · simp [held, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at recorded

/-- From Heze: once a payload turns valid, only the answer for its block changes.

The store takes that answer for the block, and nothing else in the store changes. -/
theorem Store.recordValidatedInclusionListSatisfaction_eq {store : Store preset fork}
    {heze : .hegota ≤ fork} {root : Root} {satisfied : Bool} {after : Store preset fork}
    (recorded : store.recordValidatedInclusionListSatisfaction heze root satisfied = .ok after) :
    after = { store with payloadInclusionListSatisfaction := fun _ =>
      (store.payloadInclusionListSatisfaction heze).insert root satisfied } := by
  unfold recordValidatedInclusionListSatisfaction at recorded
  by_cases held : store.isPayloadVerified (Nat.le_trans (by decide) heze) root = true
  · simp only [held, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at recorded
    exact recorded.symm
  · simp [held, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at recorded

/-- From Heze: once a payload turns valid, the answers for the other blocks stay as they were.

Its ancestors are among them. -/
theorem Store.recordValidatedInclusionListSatisfaction_other {store : Store preset fork}
    {heze : .hegota ≤ fork} {root : Root} {satisfied : Bool} {after : Store preset fork}
    (recorded : store.recordValidatedInclusionListSatisfaction heze root satisfied = .ok after)
    {other : Root} (different : other ≠ root) :
    (after.payloadInclusionListSatisfaction heze)[other]? =
      (store.payloadInclusionListSatisfaction heze)[other]? := by
  rw [recordValidatedInclusionListSatisfaction_eq recorded]
  simp [Std.TreeMap.getElem?_insert, Ne.symm different]

/-- From Heze: a payload that moves from not validated to valid was optimistic.

It then leaves the optimistic set as a valid payload does.

The store of the fork choice records the answer of the execution layer for its block. -/
theorem OptimisticStore.onValidatedPayload_ok {optimistic : OptimisticStore preset fork}
    {store : Store preset fork} {heze : .hegota ≤ fork} {root : Root} {satisfied : Bool}
    {after : OptimisticStore preset fork × Store preset fork}
    (moved : optimistic.onValidatedPayload store heze root satisfied = .ok after) :
    optimistic.isOptimistic root = true ∧ optimistic.onValidPayload root = .ok after.1 ∧
      store.recordValidatedInclusionListSatisfaction heze root satisfied = .ok after.2 := by
  unfold onValidatedPayload at moved
  by_cases held : optimistic.isOptimistic root = true
  · simp only [held, ↓reduceIte, pure, Except.pure, bind_ok_iff, Except.ok.injEq] at moved
    obtain ⟨recorded, record, valid, onValid, rfl⟩ := moved
    exact ⟨held, onValid, record⟩
  · simp [held, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at moved

/-- An optimistic validator may not sign exactly under the seven domain types of the rule.

They are those of a block, an attestation, a selection proof and an aggregate and proof.

They are also those of a sync committee message, its selection proof and a contribution. -/
theorem isOptimisticRestrictedDomain_iff (domainType : DomainType) :
    isOptimisticRestrictedDomain domainType = true ↔
      domainType = DOMAIN_BEACON_PROPOSER ∨ domainType = DOMAIN_BEACON_ATTESTER ∨
        domainType = DOMAIN_SELECTION_PROOF ∨ domainType = DOMAIN_AGGREGATE_AND_PROOF ∨
        domainType = DOMAIN_SYNC_COMMITTEE ∨ domainType = DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF ∨
        domainType = DOMAIN_CONTRIBUTION_AND_PROOF := by
  simp [isOptimisticRestrictedDomain]

end EthLib.Consensus
