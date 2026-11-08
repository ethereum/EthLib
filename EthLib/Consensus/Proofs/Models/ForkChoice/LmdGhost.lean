module

public import EthLib.Consensus.Proofs.Models.Stake
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Prod.Lex.Basic

/-!
# LMD-GHOST over a block tree

The model follows Gasper §3.2, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

The rule is Algorithm 3.1, and the weight is Definition 3.4.

The rule starts at a block and moves to the heaviest child until it reaches a leaf.

The weight of a block is the stake of the validators with a latest message in its subtree.

Each block has a root, and a tie between two children goes to the greater root.

The order on roots is a parameter.

The beacon chain compares roots as byte strings, lexicographically.

One validator set `V` and one stake function `w` hold throughout.
-/

@[expose] public section

namespace EthLib.Consensus.Models.ForkChoice

/-- A block tree.

Each block other than the genesis block has a parent below it.

The genesis block is its own parent.

A height only has to grow from a parent to its child, so the slot of a block can serve as one. -/
structure BlockTree (β : Type*) where
  /-- The root of the tree. -/
  genesis : β
  /-- The parent of each block. -/
  parent : β → β
  /-- The height of each block. -/
  height : β → ℕ
  /-- The genesis block is its own parent. -/
  parent_genesis : parent genesis = genesis
  /-- Each block other than the genesis block sits above its parent. -/
  height_parent : ∀ b, b ≠ genesis → height (parent b) < height b

namespace BlockTree

variable {β : Type*} (T : BlockTree β)

/-- The block `a` is in the chain of `b`: it is `b` or an ancestor of `b`. -/
def Ancestor (a b : β) : Prop :=
  ∃ n, T.parent^[n] b = a

/-- The block `c` is a child of `b`. -/
def IsChild (c b : β) : Prop :=
  c ≠ T.genesis ∧ T.parent c = b

variable {T}

theorem Ancestor.refl (b : β) : T.Ancestor b b :=
  ⟨0, rfl⟩

theorem Ancestor.trans {a b c : β} (hab : T.Ancestor a b) (hbc : T.Ancestor b c) :
    T.Ancestor a c := by
  obtain ⟨m, rfl⟩ := hab
  obtain ⟨n, rfl⟩ := hbc
  exact ⟨m + n, Function.iterate_add_apply _ _ _ _⟩

theorem IsChild.ancestor {b c : β} (h : T.IsChild c b) : T.Ancestor b c :=
  ⟨1, h.2⟩

theorem IsChild.height_lt {b c : β} (h : T.IsChild c b) : T.height b < T.height c := by
  rw [← h.2]
  exact T.height_parent c h.1

/-- The genesis block is its only ancestor. -/
theorem iterate_genesis (n : ℕ) : T.parent^[n] T.genesis = T.genesis :=
  Function.iterate_fixed T.parent_genesis n

/-- No ancestor is higher than its descendant. -/
theorem height_iterate_le (n : ℕ) (b : β) : T.height (T.parent^[n] b) ≤ T.height b := by
  induction n generalizing b with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    refine (ih _).trans ?_
    by_cases hb : b = T.genesis
    · rw [hb, T.parent_genesis]
    · exact (T.height_parent b hb).le

/-- An ancestor of a block sits at most as high as the block. -/
theorem Ancestor.height_le {a b : β} (h : T.Ancestor a b) : T.height a ≤ T.height b := by
  obtain ⟨n, rfl⟩ := h
  exact height_iterate_le n b

/-- An ancestor other than the block itself sits below it. -/
theorem Ancestor.height_lt {a b : β} (h : T.Ancestor a b) (hne : a ≠ b) :
    T.height a < T.height b := by
  obtain ⟨n, rfl⟩ := h
  cases n with
  | zero => exact absurd rfl hne
  | succ n =>
    -- The genesis block is its own only ancestor, so `b` is not the genesis block.
    have hb : b ≠ T.genesis := by
      rintro rfl
      exact hne (iterate_genesis _)
    rw [Function.iterate_succ_apply]
    exact (height_iterate_le n _).trans_lt (T.height_parent b hb)

/-- Two blocks in the chain of each other are equal. -/
theorem Ancestor.antisymm {a b : β} (hab : T.Ancestor a b) (hba : T.Ancestor b a) : a = b := by
  by_contra hne
  exact absurd (hab.height_lt hne) (Nat.not_lt.mpr hba.height_le)

/-- An ancestor of a block is the block itself or an ancestor of its parent. -/
theorem Ancestor.eq_or_parent {a b : β} (h : T.Ancestor a b) :
    a = b ∨ T.Ancestor a (T.parent b) := by
  obtain ⟨n, rfl⟩ := h
  cases n with
  | zero => exact .inl rfl
  | succ n => exact .inr ⟨n, (Function.iterate_succ_apply _ _ _).symm⟩

/-- Two blocks in the chain of one block are in the chain of each other. -/
theorem Ancestor.total {a b c : β} (ha : T.Ancestor a c) (hb : T.Ancestor b c) :
    T.Ancestor a b ∨ T.Ancestor b a := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  rcases le_total i j with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact .inr ⟨k, by rw [← Function.iterate_add_apply, Nat.add_comm]⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact .inl ⟨k, by rw [← Function.iterate_add_apply, Nat.add_comm]⟩

/-- Two distinct children of one block have no common descendant. -/
theorem IsChild.disjoint {b c c' m : β} (hc : T.IsChild c b) (hc' : T.IsChild c' b)
    (hne : c ≠ c') (hm : T.Ancestor c m) (hm' : T.Ancestor c' m) : False := by
  obtain ⟨i, hi⟩ := hm
  obtain ⟨j, hj⟩ := hm'
  -- A strict ancestor of a child of `b` sits at or below `b`, so it is no child of `b`.
  have key : ∀ {x y : β}, T.IsChild x b → T.IsChild y b → ∀ k, T.parent^[k] x = y → x = y := by
    intro x y hx hy k hk
    cases k with
    | zero => exact hk
    | succ k =>
      rw [Function.iterate_succ_apply, hx.2] at hk
      have := height_iterate_le (T := T) k b
      rw [hk] at this
      exact absurd hy.height_lt (Nat.not_lt.mpr this)
  rcases le_total i j with hij | hij
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.add_comm, Function.iterate_add_apply, hi] at hj
    exact hne (key hc hc' k hj)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.add_comm, Function.iterate_add_apply, hj] at hi
    exact hne (key hc' hc k hi).symm

/-- A strict ancestor of a block has a child in the chain of that block. -/
theorem Ancestor.exists_child {a b : β} (h : T.Ancestor a b) (hne : a ≠ b) :
    ∃ c, T.IsChild c a ∧ T.Ancestor c b := by
  classical
  let n := Nat.find h
  have hn : T.parent^[n] b = a := Nat.find_spec h
  cases hn' : n with
  | zero => rw [hn'] at hn; exact absurd hn.symm hne
  | succ k =>
    have hk : T.parent^[k] b ≠ a := Nat.find_min h (by omega)
    rw [hn', Function.iterate_succ_apply'] at hn
    refine ⟨T.parent^[k] b, ⟨fun hg => hk ?_, hn⟩, k, rfl⟩
    rw [← hn, hg, T.parent_genesis]

/-- Every climb of a block either reaches the genesis block or loses at least one level per step. -/
theorem iterate_eq_genesis_or (n : ℕ) (b : β) :
    T.parent^[n] b = T.genesis ∨ T.height (T.parent^[n] b) + n ≤ T.height b := by
  induction n with
  | zero => exact .inr le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with hg | hle
    · exact .inl (by rw [hg, T.parent_genesis])
    · by_cases hg : T.parent^[n] b = T.genesis
      · exact .inl (by rw [hg, T.parent_genesis])
      · have := T.height_parent _ hg
        exact .inr (by omega)

/-- A climb as long as the height of the block, plus one, reaches the genesis block. -/
theorem iterate_height_succ (b : β) : T.parent^[T.height b + 1] b = T.genesis :=
  (iterate_eq_genesis_or (T.height b + 1) b).resolve_right (by omega)

variable (T) in
open scoped Classical in
/-- The chain of a block: the block and all its ancestors. -/
noncomputable def chain (b : β) : Finset β :=
  (Finset.range (T.height b + 2)).image (T.parent^[·] b)

theorem mem_chain {a b : β} : a ∈ T.chain b ↔ T.Ancestor a b := by
  classical
  simp only [chain, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨n, -, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, rfl⟩
    by_cases hn : n < T.height b + 2
    · exact ⟨n, hn, rfl⟩
    -- A longer climb stays at the genesis block, which the climb of the height already reaches.
    refine ⟨T.height b + 1, by omega, ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hn)
    rw [iterate_height_succ, show T.height b + 2 + k = k + 1 + (T.height b + 1) by omega,
      Function.iterate_add_apply, iterate_height_succ, iterate_genesis]

end BlockTree

/-- A view of the fork choice: the blocks it holds, and the latest message of each validator.

The view holds the parent of each block it holds.

A validator without a message has none as its latest message.

A latest message can name a block outside the view. -/
structure View (ν β : Type*) (T : BlockTree β) where
  /-- The blocks of the view. -/
  blocks : Finset β
  parent_mem : ∀ b ∈ blocks, T.parent b ∈ blocks
  /-- The block of the latest message of each validator. -/
  latest : ν → Option β

variable {ν β : Type*} {T : BlockTree β}

/-- The view holds every block in the chain of a block it holds. -/
theorem View.mem_of_ancestor (G : View ν β T) {a b : β} (hb : b ∈ G.blocks)
    (h : T.Ancestor a b) : a ∈ G.blocks := by
  obtain ⟨n, rfl⟩ := h
  induction n with
  | zero => exact hb
  | succ n ih => rw [Function.iterate_succ_apply']; exact G.parent_mem _ ih

open scoped Classical in
/-- The view of the given blocks and their ancestors, with the given latest messages. -/
noncomputable def View.ofBlocks (S : Finset β) (latest : ν → Option β) : View ν β T where
  blocks := S.biUnion T.chain
  parent_mem b hb := by
    simp only [Finset.mem_biUnion, BlockTree.mem_chain] at hb ⊢
    obtain ⟨s, hs, hbs⟩ := hb
    exact ⟨s, hs, (show T.Ancestor (T.parent b) b from ⟨1, rfl⟩).trans hbs⟩
  latest := latest

theorem View.mem_ofBlocks {S : Finset β} {latest : ν → Option β} {a : β} :
    a ∈ (View.ofBlocks (T := T) S latest).blocks ↔ ∃ b ∈ S, T.Ancestor a b := by
  classical
  simp [View.ofBlocks, BlockTree.mem_chain]

variable (V : Finset ν) (w : ν → ℕ) (G : View ν β T)

open scoped Classical in
/-- The validators of `V` whose latest message is in the subtree of `b`. -/
noncomputable def supporters (b : β) : Finset ν :=
  {v ∈ V | ∃ m, G.latest v = some m ∧ T.Ancestor b m}

/-- The weight of a block: the stake of the validators whose latest message is in its subtree. -/
noncomputable def weight (b : β) : ℕ :=
  stake w (supporters V G b)

open scoped Classical in
/-- The children of a block in the view. -/
noncomputable def children (b : β) : Finset β :=
  {c ∈ G.blocks | T.IsChild c b}

variable {V w G}

theorem mem_children {b c : β} : c ∈ children G b ↔ c ∈ G.blocks ∧ T.IsChild c b := by
  classical
  simp [children]

/-- A block weighs at least as much as each block of its subtree. -/
theorem weight_mono {a b : β} (h : T.Ancestor a b) : weight V w G b ≤ weight V w G a := by
  classical
  refine stake_mono fun v hv => ?_
  simp only [supporters, Finset.mem_filter] at hv ⊢
  obtain ⟨hv, m, hm, hbm⟩ := hv
  exact ⟨hv, m, hm, h.trans hbm⟩

/-- Two distinct children of one block weigh together at most the stake of `V`. -/
theorem weight_add_le {b c c' : β} (hc : T.IsChild c b) (hc' : T.IsChild c' b) (hne : c ≠ c') :
    weight V w G c + weight V w G c' ≤ stake w V := by
  classical
  have hdis : Disjoint (supporters V G c) (supporters V G c') := by
    refine Finset.disjoint_left.mpr fun v hv hv' => ?_
    simp only [supporters, Finset.mem_filter] at hv hv'
    obtain ⟨-, m, hm, hcm⟩ := hv
    obtain ⟨-, m', hm', hcm'⟩ := hv'
    rw [hm, Option.some_inj] at hm'
    subst hm'
    exact hc.disjoint hc' hne hcm hcm'
  rw [weight, weight, stake, stake, ← Finset.sum_union hdis]
  exact stake_mono (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- A child is closer than its parent to the greatest height in the view. -/
theorem height_lt_of_mem_children {b c : β} (hc : c ∈ children G b) :
    G.blocks.sup T.height - T.height c < G.blocks.sup T.height - T.height b := by
  rw [mem_children] at hc
  have h1 := hc.2.height_lt
  have h2 : T.height c ≤ G.blocks.sup T.height := Finset.le_sup hc.1
  omega

variable {ρ : Type*} [LinearOrder ρ] (root : β → ρ) (V w G)

/-- The child that the rule picks: the greatest by weight, then by root.

Two children with one weight and one root leave the choice open. -/
noncomputable def heaviestChild (b : β) (h : (children G b).Nonempty) : β :=
  Classical.choose ((children G b).exists_max_image (fun c => toLex (weight V w G c, root c)) h)

theorem heaviestChild_spec (b : β) (h : (children G b).Nonempty) :
    heaviestChild V w G root b h ∈ children G b ∧ ∀ c ∈ children G b,
      toLex (weight V w G c, root c) ≤
        toLex (weight V w G (heaviestChild V w G root b h),
          root (heaviestChild V w G root b h)) :=
  Classical.choose_spec
    ((children G b).exists_max_image (fun c => toLex (weight V w G c, root c)) h)

variable {V w G root} in
/-- A child above every other child by weight, then by root, is the child that the rule picks.

The roots of the children must differ. -/
theorem heaviestChild_eq {b c : β} (hc : c ∈ children G b)
    (hmax : ∀ c' ∈ children G b, toLex (weight V w G c', root c') ≤ toLex (weight V w G c, root c))
    (hroot : Set.InjOn root (children G b)) :
    heaviestChild V w G root b ⟨c, hc⟩ = c := by
  obtain ⟨hmem, hle⟩ := heaviestChild_spec V w G root b ⟨c, hc⟩
  have key := le_antisymm (hmax _ hmem) (hle c hc)
  exact hroot hmem hc (Prod.ext_iff.mp (toLex.injective key)).2

/-- LMD-GHOST from the block `b`: move to the heaviest child until the block has no child. -/
noncomputable def ghost (b : β) : β :=
  if h : (children G b).Nonempty then ghost (heaviestChild V w G root b h) else b
termination_by G.blocks.sup T.height - T.height b
decreasing_by exact height_lt_of_mem_children (heaviestChild_spec V w G root b h).1

theorem ghost_of_nonempty {b : β} (h : (children G b).Nonempty) :
    ghost V w G root b = ghost V w G root (heaviestChild V w G root b h) := by
  rw [ghost]
  simp only [h, ↓reduceDIte]

theorem ghost_of_not_nonempty {b : β} (h : ¬(children G b).Nonempty) : ghost V w G root b = b := by
  rw [ghost]
  simp only [h, ↓reduceDIte]

/-- The head is a leaf of the view. -/
theorem children_ghost (b : β) : children G (ghost V w G root b) = ∅ := by
  induction b using ghost.induct V w G root with
  | case1 b h ih => rwa [ghost_of_nonempty V w G root h]
  | case2 b h =>
    rw [ghost_of_not_nonempty V w G root h]
    exact Finset.not_nonempty_iff_eq_empty.mp h

/-- The head is in the subtree of the starting block. -/
theorem ancestor_ghost (b : β) : T.Ancestor b (ghost V w G root b) := by
  induction b using ghost.induct V w G root with
  | case1 b h ih =>
    rw [ghost_of_nonempty V w G root h]
    exact ((mem_children.mp (heaviestChild_spec V w G root b h).1).2.ancestor).trans ih
  | case2 b h => rw [ghost_of_not_nonempty V w G root h]; exact .refl b

/-- The head is in the view when the starting block is. -/
theorem ghost_mem {b : β} (hb : b ∈ G.blocks) : ghost V w G root b ∈ G.blocks := by
  induction b using ghost.induct V w G root with
  | case1 b h ih =>
    rw [ghost_of_nonempty V w G root h]
    exact ih (mem_children.mp (heaviestChild_spec V w G root b h).1).1
  | case2 b h => rwa [ghost_of_not_nonempty V w G root h]

/-- The majority lemma.

Take a block `b` of the view.

Suppose that more than half of the stake of `V` has its latest message in the subtree of `b`.

Then LMD-GHOST from any block in the chain of `b` returns a block in the subtree of `b`. -/
theorem ancestor_ghost_of_majority {a b : β} (hb : b ∈ G.blocks) (hab : T.Ancestor a b)
    (hmaj : stake w V < 2 * weight V w G b) : T.Ancestor b (ghost V w G root a) := by
  induction a using ghost.induct V w G root with
  | case1 a h ih =>
    by_cases hba : a = b
    · subst hba
      exact ancestor_ghost V w G root a
    obtain ⟨c, hc, hcb⟩ := hab.exists_child hba
    have hcmem : c ∈ children G a := mem_children.mpr ⟨G.mem_of_ancestor hb hcb, hc⟩
    -- The child towards `b` has more than half of the stake, so it outweighs every other child.
    have hpick : heaviestChild V w G root a h = c := by
      obtain ⟨hmem, hmax⟩ := heaviestChild_spec V w G root a h
      by_contra hne
      have hsum := weight_add_le (V := V) (w := w) (G := G) hc (mem_children.mp hmem).2
        (Ne.symm hne)
      have hcw := weight_mono (V := V) (w := w) (G := G) hcb
      have hle := hmax c hcmem
      rw [Prod.Lex.toLex_le_toLex] at hle
      rcases hle with hle | ⟨hle, -⟩ <;> dsimp only at hle <;> omega
    rw [ghost_of_nonempty V w G root h]
    exact hpick ▸ ih (hpick ▸ hcb)
  | case2 a h =>
    by_cases hba : a = b
    · subst hba
      exact ancestor_ghost V w G root a
    -- A block above `b` has a child in the view, so the rule does not stop there.
    obtain ⟨c, hc, hcb⟩ := hab.exists_child hba
    exact absurd ⟨c, mem_children.mpr ⟨G.mem_of_ancestor hb hcb, hc⟩⟩ h

/-! ## Proposer boost

The boost gives a timely block of the current slot the weight of an attestation of `W_p`.

So the block and each of its ancestors gain `W_p` in weight.

The source is Buterin's [mitigation of balancing attacks][mitigation], "Proposed solution", step 3.

Step 3 sets that weight to `W / 4`, and its section "Analysis" names it `W_p`.

Section 3 of [Three Attacks on Proof-of-Stake Ethereum][attacks] gives the ex ante reorg.

A [post on balancing and reorging attacks][post] gives the limits of the boost.

Its section "Why change?" says that the boost fixes most ex ante reorgs, but not all.

Its section "Boosting does not mitigate all ex ante reorgs" adds the boost to the votes.

There the boost counts in the chain of the boosted block.

The model follows that rule: the boost is one more voter, `none`.

Its latest message is the boosted block, and its stake is the score of the boost.

Without a boosted block, it has no latest message.

[mitigation]: https://notes.ethereum.org/@vbuterin/lmd_ghost_mitigation
[attacks]: https://arxiv.org/abs/2110.10086v1
[post]: https://ethresear.ch/t/change-fork-choice-rule-to-mitigate-balancing-and-reorging-attacks/11127
-/

variable {V w G}

/-- The stakes with the boost: the stake of each validator, and the score of the boost. -/
def boostStake (w : ν → ℕ) (score : ℕ) : Option ν → ℕ
  | none => score
  | some v => w v

/-- The view with the boost: the same blocks, and the boosted block as the message of `none`. -/
def View.withBoost (G : View ν β T) (boosted : Option β) : View (Option ν) β T where
  blocks := G.blocks
  parent_mem := G.parent_mem
  latest
    | none => boosted
    | some v => G.latest v

@[simp] theorem View.withBoost_blocks (boosted : Option β) :
    (G.withBoost boosted).blocks = G.blocks :=
  rfl

/-- The voters and the boost together weigh the stake of the voters plus the score of the boost. -/
theorem stake_boostStake (score : ℕ) :
    stake (boostStake w score) V.insertNone = stake w V + score := by
  rw [stake, Finset.sum_insertNone, stake, Nat.add_comm]
  rfl

open scoped Classical in
/-- With the boost, a block weighs its votes, plus the score.

The score counts exactly when the boosted block is in its subtree. -/
theorem weight_withBoost (boosted : Option β) (score : ℕ) (b : β) :
    weight V.insertNone (boostStake w score) (G.withBoost boosted) b =
      weight V w G b + if ∃ m, boosted = some m ∧ T.Ancestor b m then score else 0 := by
  classical
  simp only [weight, stake, supporters, Finset.sum_filter, Finset.sum_insertNone]
  rw [Nat.add_comm]
  rfl

end EthLib.Consensus.Models.ForkChoice
