module

public import EthLib.Consensus.Proofs.Models.ForkChoice.LmdGhost

/-!
# LMD-GHOST over payload-status nodes

With enshrined proposer-builder separation, a block and its execution payload arrive apart.

The fork choice then votes on nodes: a block with its payload pending, empty or full.

This follows EIP-7732, section "Fork-Choice changes".

A pending node has as children the block without its payload, and the block with it.

A block hangs under the empty or the full node of its parent, as the block itself says.

Suppose every block builds on a full parent, and no vote names an empty node.

Then the rule over nodes picks the head of the rule over blocks, with its payload.
-/

@[expose] public section

namespace EthLib.Consensus.Models.ForkChoice

/-- The payload status of a node: none while pending, then whether the payload is present. -/
abbrev Status := Option Bool

/-- The number that orders statuses in a tie: empty 0, full 1, pending 2. -/
def Status.code : Status → ℕ
  | some false => 0
  | some true => 1
  | none => 2

namespace BlockTree

variable {β : Type*} [DecidableEq β] (T : BlockTree β) (full : β → Bool)

/-- The parent of a node.

An empty or a full node hangs under the pending node of its block.

A pending node hangs under the parent block, with the status that the block builds on. -/
def statusParent : β × Status → β × Status
  | (r, some _) => (r, none)
  | (r, none) => if r = T.genesis then (r, none) else (T.parent r, some (full r))

/-- The height of a node: two levels per block, the pending node below the other two. -/
def statusHeight : β × Status → ℕ
  | (r, none) => 2 * T.height r
  | (r, some _) => 2 * T.height r + 1

/-- The tree of payload-status nodes over a block tree.

The pending node of the genesis block is its root.

The block `r` builds on the full payload of its parent exactly when `full r` holds. -/
def payloadTree : BlockTree (β × Status) where
  genesis := (T.genesis, none)
  parent := statusParent T full
  height := statusHeight T
  parent_genesis := by simp [statusParent]
  height_parent := by
    rintro ⟨r, _ | x⟩ h
    · have hr : r ≠ T.genesis := fun e => h (by rw [e])
      have := T.height_parent r hr
      simp only [statusParent, hr, ↓reduceIte, statusHeight]
      omega
    · simp [statusParent, statusHeight]

variable {T full}

@[simp] theorem payloadTree_genesis : (T.payloadTree full).genesis = (T.genesis, none) := rfl

@[simp] theorem payloadTree_parent_some (r : β) (x : Bool) :
    (T.payloadTree full).parent (r, some x) = (r, none) := rfl

theorem payloadTree_parent_none {r : β} (hr : r ≠ T.genesis) :
    (T.payloadTree full).parent (r, none) = (T.parent r, some (full r)) := by
  simp [payloadTree, statusParent, hr]

/-- The children of a pending node are the empty and the full node of its block. -/
theorem payloadTree_isChild_some {n : β × Status} {r : β} {x : Bool} :
    (T.payloadTree full).IsChild (r, some x) n ↔ n = (r, none) := by
  simp [IsChild, eq_comm]

/-- A pending node is a child of exactly one node: the status of its parent that it builds on. -/
theorem payloadTree_isChild_none {c p : β} {s : Status} :
    (T.payloadTree full).IsChild (c, none) (p, s) ↔
      c ≠ T.genesis ∧ T.parent c = p ∧ s = some (full c) := by
  constructor
  · rintro ⟨hg, hp⟩
    have hc : c ≠ T.genesis := fun e => hg (by rw [e]; rfl)
    rw [payloadTree_parent_none hc, Prod.mk.injEq] at hp
    exact ⟨hc, hp.1, hp.2.symm⟩
  · rintro ⟨hc, rfl, rfl⟩
    refine ⟨fun e => hc (Prod.mk.inj e).1, payloadTree_parent_none hc⟩

/-- A node never hangs under a pending node of another block. -/
theorem not_payloadTree_isChild_none_none {c p : β} :
    ¬(T.payloadTree full).IsChild (c, none) (p, none) := by
  simp [payloadTree_isChild_none]

/-- An ancestor node has an ancestor block. -/
theorem payloadTree_ancestor_fst {a b : β × Status} (h : (T.payloadTree full).Ancestor a b) :
    T.Ancestor a.1 b.1 := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact .refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine Ancestor.trans ?_ ih
    obtain ⟨r, _ | x⟩ := (T.payloadTree full).parent^[n] b
    · by_cases hr : r = T.genesis
      · simp [payloadTree, statusParent, hr, Ancestor.refl]
      · rw [payloadTree_parent_none hr]
        exact ⟨1, rfl⟩
    · exact .refl _

/-- The pending node of every ancestor block is an ancestor node. -/
theorem payloadTree_ancestor_none_of {a : β} {b : β × Status} (h : T.Ancestor a b.1) :
    (T.payloadTree full).Ancestor (a, none) b := by
  obtain ⟨k, hk⟩ := h
  -- Climbing `k` blocks reaches the pending node `k` blocks up.
  have climb : ∀ k, ∃ m, (T.payloadTree full).parent^[m] b = (T.parent^[k] b.1, none) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨r, _ | x⟩ := b
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    | succ k ih =>
      obtain ⟨m, hm⟩ := ih
      rw [Function.iterate_succ_apply']
      by_cases hg : T.parent^[k] b.1 = T.genesis
      · exact ⟨m, by rw [hm, hg, T.parent_genesis]⟩
      · refine ⟨m + 2, ?_⟩
        rw [Nat.add_comm, Function.iterate_add_apply, hm]
        simp [payloadTree_parent_none hg]
  obtain ⟨m, hm⟩ := climb k
  exact ⟨m, hk ▸ hm⟩

/-- A pending node is an ancestor node exactly when its block is an ancestor block. -/
theorem payloadTree_ancestor_none_iff {a : β} {b : β × Status} :
    (T.payloadTree full).Ancestor (a, none) b ↔ T.Ancestor a b.1 :=
  ⟨payloadTree_ancestor_fst, payloadTree_ancestor_none_of⟩

end BlockTree

open BlockTree

variable {ν β ρ : Type*} [DecidableEq β] [LinearOrder ρ]

section Unique

variable {γ : Type*} {T : BlockTree γ} (V : Finset ν) (w : ν → ℕ) (G : View ν γ T)
  {key : γ → ρ}

/-- With distinct roots among the children, the rule picks the child that beats every other. -/
theorem heaviestChild_eq_of_max (hkey : Function.Injective key) {b c : γ}
    (h : (children G b).Nonempty) (hc : c ∈ children G b)
    (hmax : ∀ c' ∈ children G b, toLex (weight V w G c', key c') ≤ toLex (weight V w G c, key c)) :
    heaviestChild V w G key b h = c := by
  obtain ⟨hmem, hle⟩ := heaviestChild_spec V w G key b h
  have heq := le_antisymm (hmax _ hmem) (hle c hc)
  exact hkey (Prod.ext_iff.mp (toLex.injective heq)).2

end Unique

variable {T : BlockTree β} {full : β → Bool} (V : Finset ν) (w : ν → ℕ)

/-- The order of nodes in a tie: by block root, then by status.

In the slot right after a block, EIP-7732 breaks the tie of its empty and full nodes otherwise.

There the payload attestations and the proposer boost decide, which this model leaves out. -/
def nodeKey (root : β → ρ) (n : β × Status) : Lex (ρ × ℕ) :=
  toLex (root n.1, n.2.code)

omit [DecidableEq β] [LinearOrder ρ] in
theorem nodeKey_injective {root : β → ρ} (hroot : Function.Injective root) :
    Function.Injective (nodeKey root) := by
  rintro ⟨r, x⟩ ⟨r', x'⟩ h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp (toLex.injective h)
  obtain rfl := hroot h1
  rcases x with _ | _ | _ <;> rcases x' with _ | _ | _ <;> simp_all [Status.code]

variable {G : View ν β T} {N : View ν (β × Status) (T.payloadTree full)}

/-- A pending node weighs as much as its block, when votes name the same blocks. -/
theorem weight_none (hlatest : ∀ v, G.latest v = (N.latest v).map Prod.fst) (c : β) :
    weight V w N (c, none) = weight V w G c := by
  classical
  unfold weight supporters
  congr 1
  ext v
  simp only [Finset.mem_filter, payloadTree_ancestor_none_iff, hlatest v, Option.map_eq_some_iff]
  constructor
  · rintro ⟨hv, m, hm, ha⟩
    exact ⟨hv, m.1, ⟨m, hm, rfl⟩, ha⟩
  · rintro ⟨hv, _, ⟨m, hm, rfl⟩, ha⟩
    exact ⟨hv, m, hm, ha⟩

/-- No vote supports an empty node when every block builds on a full parent and no vote names
an empty node. -/
theorem weight_empty (hfull : ∀ r, r ≠ T.genesis → full r = true)
    (hvote : ∀ v r, N.latest v ≠ some (r, some false)) (b : β) :
    weight V w N (b, some false) = 0 := by
  classical
  suffices h : supporters V N (b, some false) = ∅ by simp [weight, h, stake]
  refine Finset.filter_false_of_mem fun v _ => ?_
  rintro ⟨m, hm, ha⟩
  by_cases hbm : (b, some false) = m
  · exact hvote v b (hbm ▸ hm)
  obtain ⟨c, hc, -⟩ := ha.exists_child hbm
  obtain ⟨r, _ | x⟩ := c
  · obtain ⟨hr, -, he⟩ := payloadTree_isChild_none.mp hc
    rw [hfull r hr] at he
    exact absurd he (by simp)
  · exact absurd (payloadTree_isChild_some.mp hc) (by simp)

/-- The rule over nodes agrees with the rule over blocks when every payload is present.

The views hold the same pending nodes as blocks, and the full node of each block.

Every block builds on a full parent, no vote names an empty node, and votes name the same blocks.

Then from the pending node of a block, the rule over nodes reaches the full node of the head that
the rule over blocks reaches. -/
theorem ghost_payloadTree {root : β → ρ} (hroot : Function.Injective root)
    (hfull : ∀ r, r ≠ T.genesis → full r = true)
    (hpending : ∀ r, (r, none) ∈ N.blocks ↔ r ∈ G.blocks)
    (hpayload : ∀ r ∈ G.blocks, (r, some true) ∈ N.blocks)
    (hvote : ∀ v r, N.latest v ≠ some (r, some false))
    (hlatest : ∀ v, G.latest v = (N.latest v).map Prod.fst) {b : β} (hb : b ∈ G.blocks) :
    ghost V w N (nodeKey root) (b, none) = (ghost V w G root b, some true) := by
  have hkey := nodeKey_injective hroot
  -- The full node of a block is the heaviest child of its pending node.
  have pend : ∀ r ∈ G.blocks, ghost V w N (nodeKey root) (r, none) =
      ghost V w N (nodeKey root) (r, some true) := by
    intro r hr
    have hmem : (r, some true) ∈ children N (r, none) :=
      mem_children.mpr ⟨hpayload r hr, payloadTree_isChild_some.mpr rfl⟩
    rw [ghost_of_nonempty V w N _ ⟨_, hmem⟩]
    congr 1
    refine heaviestChild_eq_of_max V w N hkey _ hmem fun c hc => ?_
    obtain ⟨-, hc⟩ := mem_children.mp hc
    obtain ⟨r', _ | _ | _⟩ := c
    · exact absurd hc not_payloadTree_isChild_none_none
    · obtain rfl : r = r' := (Prod.mk.inj (payloadTree_isChild_some.mp hc)).1
      rw [weight_empty V w hfull hvote, Prod.Lex.toLex_le_toLex]
      rcases Nat.eq_zero_or_pos (weight V w N (r, some true)) with h0 | h0
      · exact Or.inr ⟨h0.symm, by simp [nodeKey, Status.code, Prod.Lex.toLex_le_toLex]⟩
      · exact Or.inl h0
    · obtain rfl : r = r' := (Prod.mk.inj (payloadTree_isChild_some.mp hc)).1
      exact le_rfl
  -- The children of a full node are the pending nodes of the children of its block.
  have kids : ∀ r c, (c, none) ∈ children N (r, some true) ↔ c ∈ children G r := by
    intro r c
    rw [mem_children, mem_children, hpending, payloadTree_isChild_none]
    constructor
    · rintro ⟨hc, hg, hp, -⟩
      exact ⟨hc, hg, hp⟩
    · rintro ⟨hc, hg, hp⟩
      exact ⟨hc, hg, hp, by rw [hfull c hg]⟩
  have kids_fst : ∀ r c x, (c, x) ∈ children N (r, some true) → x = none := by
    intro r c x hn
    rcases x with _ | x
    · rfl
    · exact absurd (payloadTree_isChild_some.mp (mem_children.mp hn).2) (by simp)
  induction b using ghost.induct V w G root with
  | case1 b h ih =>
    set c := heaviestChild V w G root b h
    obtain ⟨hcmem, hcmax⟩ := heaviestChild_spec V w G root b h
    have hnode : (c, none) ∈ children N (b, some true) := (kids b c).mpr hcmem
    rw [pend b hb, ghost_of_nonempty V w G root h, ghost_of_nonempty V w N _ ⟨_, hnode⟩]
    have hpick : heaviestChild V w N (nodeKey root) (b, some true) ⟨_, hnode⟩ = (c, none) := by
      refine heaviestChild_eq_of_max V w N hkey _ hnode fun ⟨n, x⟩ hn => ?_
      obtain rfl := kids_fst b n x hn
      have hle := hcmax n ((kids b n).mp hn)
      rw [weight_none V w hlatest, weight_none V w hlatest]
      rw [Prod.Lex.toLex_le_toLex] at hle ⊢
      rcases hle with hle | ⟨heq, hle⟩
      · exact Or.inl hle
      · refine Or.inr ⟨heq, ?_⟩
        simp only [nodeKey, Status.code, Prod.Lex.toLex_le_toLex, le_refl, and_true]
        exact le_iff_lt_or_eq.mp hle
    rw [hpick]
    exact ih ((mem_children.mp hcmem).1)
  | case2 b h =>
    rw [pend b hb, ghost_of_not_nonempty V w G root h, ghost_of_not_nonempty V w N]
    rintro ⟨⟨n, x⟩, hn⟩
    obtain rfl := kids_fst b n x hn
    exact h ⟨_, (kids b n).mp hn⟩

/-- The view of nodes in which every block of a view of blocks has its payload.

It holds the pending and the full node of each block, and no empty node. -/
def View.fullView (G : View ν β T) (hfull : ∀ r, r ≠ T.genesis → full r = true)
    (latest : ν → Option (β × Status)) : View ν (β × Status) (T.payloadTree full) where
  blocks := G.blocks.biUnion fun r => {(r, none), (r, some true)}
  parent_mem := by
    intro n hn
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton] at hn ⊢
    obtain ⟨r, hr, rfl | rfl⟩ := hn
    · by_cases hg : r = T.genesis
      · exact ⟨r, hr, Or.inl (by simp [payloadTree, statusParent, hg])⟩
      · rw [payloadTree_parent_none hg, hfull r hg]
        exact ⟨T.parent r, G.parent_mem r hr, Or.inr rfl⟩
    · exact ⟨r, hr, Or.inl rfl⟩
  latest := latest

/-- The rule over the view with every payload picks the head of the rule over blocks, in full.

Every block builds on a full parent, no vote names an empty node, and votes name the same
blocks. -/
theorem ghost_fullView {root : β → ρ} (hroot : Function.Injective root)
    (hfull : ∀ r, r ≠ T.genesis → full r = true) {latest : ν → Option (β × Status)}
    (hvote : ∀ v r, latest v ≠ some (r, some false))
    (hlatest : ∀ v, G.latest v = (latest v).map Prod.fst) {b : β} (hb : b ∈ G.blocks) :
    ghost V w (G.fullView hfull latest) (nodeKey root) (b, none) =
      (ghost V w G root b, some true) := by
  refine ghost_payloadTree V w hroot hfull (fun r => ?_) (fun r hr => ?_) hvote hlatest hb
  · simp [View.fullView]
  · simp only [View.fullView, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨r, hr, Or.inr rfl⟩

end EthLib.Consensus.Models.ForkChoice
