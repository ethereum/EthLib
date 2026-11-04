module

public import EthLib.Cryptography.Proofs.Merkle.Binding
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.IdealStatement

/-!
# The model's paths on the shared Merkle tree

A path of the model is the shared climb from its leaf index, over the 16 siblings of the path.

Two paths that reach one root have one leaf and one path, or the shared search finds a collision.

A collision sits at the level of its parent, from 1 to 16, as the shared search records it.
-/

@[expose] public section

namespace XmssSecurity.Merkle

open EthLib.Cryptography.Merkle (Collision climb climb_binding climb_take_succ div_two_div_pow
  climb_siblings findCollision findCollision_valid node node_zero ofFn_take_siblings ordered
  ordered_sibling)

variable {α : Type} (hash : Nat → Nat → α → α → Id α)

/-- The pair a climb from leaf `j` hashes into its node above `level`, the left child first. -/
def pairAt (j : Nat) (path : Fin treeHeight → α) (leaf : α) (level : Fin treeHeight) : α × α :=
  ordered (j / 2 ^ level.val) (climb hash 0 j leaf ((List.ofFn path).take level.val)).run
    (path level)

/-- The search over two climbs from leaf `j` finds a collision whose parent is on `level`. -/
def CollidesAt [DecidableEq α] (j : Nat) (leftPath rightPath : Fin treeHeight → α) (left right : α)
    (level : Nat) : Prop :=
  ∃ c, findCollision hash 0 j left right (List.ofFn leftPath) (List.ofFn rightPath) = some c ∧
    c.level = level

/-- One more level of the climb hashes the pair below it, at the position of the parent. -/
theorem climb_take_succ_run (j : Nat) (path : Fin treeHeight → α) (leaf : α)
    (level : Fin treeHeight) :
    (climb hash 0 j leaf ((List.ofFn path).take (level.val + 1))).run =
      (hash (level.val + 1) (j / 2 ^ (level.val + 1)) (pairAt hash j path leaf level).1
        (pairAt hash j path leaf level).2).run := by
  have hparent : j / 2 ^ (level.val + 1) = j / 2 ^ level.val / 2 := by
    rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
  rw [climb_take_succ hash j leaf _ level.val (by simp), pairAt, hparent]
  unfold ordered
  split <;> simp

section Honest

variable (leaves : Nat → Id α)

/-- The honest path of leaf `j` climbs to the leaf's ancestor on each level.

Its sibling on level `l` is node `floor(j / 2^l) xor 1`. -/
theorem climb_honest (j : Nat) :
    ∀ n, n ≤ treeHeight →
      (climb hash 0 j (leaves j).run ((List.ofFn fun level : Fin treeHeight =>
          (node hash leaves level ((j / 2 ^ level.val) ^^^ 1)).run).take n)).run =
        (node hash leaves n (j / 2 ^ n)).run := fun n hn => by
  -- The honest siblings are the shared tree's siblings, which climb to the ancestor.
  rw [ofFn_take_siblings hash leaves j treeHeight n hn]
  simpa [node_zero] using climb_siblings hash leaves n 0 j

/-- The pair the honest path of leaf `j` hashes above `level` is the next ancestor's children. -/
theorem pairAt_honest (j : Nat) (level : Fin treeHeight) :
    pairAt hash j (fun level => (node hash leaves level ((j / 2 ^ level.val) ^^^ 1)).run)
        (leaves j).run level =
      ((node hash leaves level (2 * (j / 2 ^ (level.val + 1)))).run,
        (node hash leaves level (2 * (j / 2 ^ (level.val + 1)) + 1)).run) := by
  rw [pairAt, climb_honest hash leaves j level.val level.isLt.le,
    ordered_sibling (fun i => (node hash leaves level i).run), Nat.pow_succ,
    ← Nat.div_div_eq_div_mul]

end Honest

/-- A collision found with its parent on level `level + 1` is between the pairs of `level`.

The two pairs differ, and hash to one parent at the parent's position. -/
theorem CollidesAt.pairs [DecidableEq α] {j : Nat} {leftPath rightPath : Fin treeHeight → α}
    {left right : α} {level : Fin treeHeight}
    (hcollision : CollidesAt hash j leftPath rightPath left right (level.val + 1)) :
    pairAt hash j leftPath left level ≠ pairAt hash j rightPath right level ∧
      (hash (level.val + 1) (j / 2 ^ (level.val + 1)) (pairAt hash j leftPath left level).1
          (pairAt hash j leftPath left level).2).run =
        (hash (level.val + 1) (j / 2 ^ (level.val + 1)) (pairAt hash j rightPath right level).1
          (pairAt hash j rightPath right level).2).run := by
  obtain ⟨c, hfound, hlevel⟩ := hcollision
  obtain ⟨⟨hne, heq⟩, k, s, t, hs, ht, hk, hj, hx, hy⟩ :=
    findCollision_valid hash _ _ _ _ _ _ c hfound
  -- The search names the pairs after `k` levels, and `k` is the level below the parent.
  obtain rfl : k = level.val := by omega
  have hs' : s = leftPath level := by simpa using hs.symm
  have ht' : t = rightPath level := by simpa using ht.symm
  have hx' : c.x = pairAt hash j leftPath left level := by rw [hx, hs', pairAt]
  have hy' : c.y = pairAt hash j rightPath right level := by rw [hy, ht', pairAt]
  rw [← hx', ← hy']
  exact ⟨hne, by simpa [Collision.Valid, hlevel, hj] using heq⟩

/-- Two paths of leaf `j` that climb to one root have the same leaf and siblings, or collide.

The collision's parent is on one of the 16 levels from 1 to 16. -/
theorem samePath_or_collidesAt [DecidableEq α] (j : Nat) (leftPath rightPath : Fin treeHeight → α)
    (left right : α)
    (hroot : (climb hash 0 j left (List.ofFn leftPath)).run =
      (climb hash 0 j right (List.ofFn rightPath)).run) :
    (left = right ∧ leftPath = rightPath) ∨
      ∃ level : Fin treeHeight,
        CollidesAt hash j leftPath rightPath left right (level.val + 1) := by
  rcases climb_binding hash _ _ 0 j left right (by simp) hroot with ⟨hleaf, hpath⟩ | hfound
  · exact .inl ⟨hleaf, List.ofFn_injective hpath⟩
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hfound
    obtain ⟨-, k, s, -, hs, -, hlevel, -⟩ := findCollision_valid hash _ _ _ _ _ _ c hc
    have hk : k < treeHeight := by simpa using (List.getElem?_eq_some_iff.mp hs).1
    exact .inr ⟨⟨k, hk⟩, c, hc, by simpa using hlevel⟩

end XmssSecurity.Merkle
