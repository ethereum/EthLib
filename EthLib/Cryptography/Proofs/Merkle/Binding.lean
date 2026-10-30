import EthLib.Cryptography.Proofs.Merkle.Tree

/-!
# Proofs: a path binds its leaf

Two openings of leaf `e` that fold to the same root are equal, or the node hash collides.

The collision has a known position: level `lambda` and index `floor(e / 2^lambda)`.

When the node hash reads an address built from that position, the collision is under that one address.

Against an honest tree, one side of the collision is the tree's own pair of children.

That is a second preimage of an honest node, the property a hash-based signature reduces to.
-/

namespace EthLib.Cryptography.Merkle

variable {α : Type} {height : Nat}
variable {nodeHash : Fin (height + 1) → Nat → α → α → α} {leaves : Nat → α}

/-- A collision of the node hash at one position: two different child pairs, one parent. -/
def Collision (nodeHash : Fin (height + 1) → Nat → α → α → α) (level : Fin (height + 1))
    (j : Nat) (x y : α × α) : Prop :=
  x ≠ y ∧ nodeHash level j x.1 x.2 = nodeHash level j y.1 y.2

/-- The children a climb hashes on `level`: the held node and the path's sibling, in tree order. -/
def climbChildren (nodeHash : Fin (height + 1) → Nat → α → α → α) (e : Nat)
    (pi : Vector α height) (leaf : α) (level : Fin height) : α × α :=
  stepChildren e level (Internal.climbUpto nodeHash e pi leaf level (by omega)) pi[level]

/-! ## Any two openings -/

/-- Two climbs that meet after `levels` levels agree below, or collide at some level below.

The collision's first pair is the first climb's, so a reduction knows which side is which. -/
theorem climbUpto_binding (e : Nat) (pi pi' : Vector α height) (a b : α) :
    ∀ (levels : Nat) (hl : levels ≤ height),
      Internal.climbUpto nodeHash e pi a levels hl = Internal.climbUpto nodeHash e pi' b levels hl →
      (a = b ∧ ∀ l : Fin height, l.val < levels → pi[l] = pi'[l]) ∨
      ∃ l : Fin height, l.val < levels ∧
        Collision nodeHash l.succ (e >>> (l.val + 1))
          (climbChildren nodeHash e pi a l) (climbChildren nodeHash e pi' b l) := by
  intro levels
  induction levels with
  | zero =>
    -- No level climbed: both sides are their leaves.
    intro _ heq
    exact .inl ⟨heq, fun _ hl => absurd hl (Nat.not_lt_zero _)⟩
  | succ k ih =>
    intro hl heq
    let top : Fin height := ⟨k, by omega⟩
    -- The last step hashes one pair of children on each side, at the same position.
    have hstep : nodeHash top.succ (e >>> (k + 1))
          (climbChildren nodeHash e pi a top).1 (climbChildren nodeHash e pi a top).2
        = nodeHash top.succ (e >>> (k + 1))
          (climbChildren nodeHash e pi' b top).1 (climbChildren nodeHash e pi' b top).2 := by
      simp only [Internal.climbUpto, climbStep_eq] at heq
      exact heq
    by_cases hpair : climbChildren nodeHash e pi a top = climbChildren nodeHash e pi' b top
    · -- Equal pairs: the held nodes and the siblings on level `k` agree.
      obtain ⟨hheld, hsib⟩ := stepChildren_inj.mp hpair
      rcases ih (by omega) hheld with ⟨hab, hbelow⟩ | ⟨l, hlk, hcol⟩
      · -- Agreement below `k`, and on `k` by the siblings.
        refine .inl ⟨hab, fun l hlt => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt | heqk
        · exact hbelow l hlt
        · have : l = top := Fin.ext heqk
          subst this
          exact hsib
      · -- A collision below `k` is still below `k + 1`.
        exact .inr ⟨l, by omega, hcol⟩
    · -- Different pairs with one parent: the collision is on level `k + 1`.
      exact .inr ⟨top, Nat.lt_succ_self k, hpair, hstep⟩

/-- Two openings of leaf `e` that fold to one root are equal, or the node hash collides. -/
theorem fold_binding {e : Nat} {pi pi' : Vector α height} {a b : α}
    (heq : fold nodeHash e a pi = fold nodeHash e b pi') :
    (a = b ∧ pi = pi') ∨
      ∃ l : Fin height, Collision nodeHash l.succ (e >>> (l.val + 1))
        (climbChildren nodeHash e pi a l) (climbChildren nodeHash e pi' b l) := by
  rcases climbUpto_binding e pi pi' a b height (Nat.le_refl _) heq with ⟨hab, hpi⟩ | ⟨l, -, hcol⟩
  · -- Every level is below the top, so the paths agree everywhere.
    exact .inl ⟨hab, Vector.ext fun i hi => hpi ⟨i, hi⟩ hi⟩
  · exact .inr ⟨l, hcol⟩

/-- With a node hash injective at every position, a root fixes the leaf and the path. -/
theorem fold_injective
    (hinj : ∀ level j (x y : α × α), nodeHash level j x.1 x.2 = nodeHash level j y.1 y.2 → x = y)
    {e : Nat} {pi pi' : Vector α height} {a b : α}
    (heq : fold nodeHash e a pi = fold nodeHash e b pi') : a = b ∧ pi = pi' := by
  rcases fold_binding heq with h | ⟨_, hne, hcol⟩
  · exact h
  · exact absurd (hinj _ _ _ _ hcol) hne

/-! ## Against an honest tree -/

/-- An honest climb hashes the tree's own children on every level. -/
theorem climbChildren_path (e : Nat) (l : Fin height) :
    climbChildren nodeHash e (path nodeHash leaves e) (leaves e) l
      = (node nodeHash leaves l (by omega) (2 * (e >>> (l.val + 1))),
          node nodeHash leaves l (by omega) (2 * (e >>> (l.val + 1)) + 1)) := by
  unfold climbChildren
  rw [climbUpto_eq_node]
  simp only [path, Fin.getElem_fin, Vector.getElem_ofFn]
  exact stepChildren_siblingIndex (fun j => node nodeHash leaves l (by omega) j) e l

/-- An opening of leaf `e` that reaches its honest ancestor on the top level is honest.

Otherwise some level holds a second preimage: a pair other than the tree's own, hashed to the tree's own parent. -/
theorem fold_eq_node_binding {e : Nat} {b : α} {pi' : Vector α height}
    (heq : fold nodeHash e b pi' = node nodeHash leaves height (Nat.le_refl _) (e >>> height)) :
    (b = leaves e ∧ pi' = path nodeHash leaves e) ∨
      ∃ l : Fin height, Collision nodeHash l.succ (e >>> (l.val + 1))
        (node nodeHash leaves l (by omega) (2 * (e >>> (l.val + 1))),
          node nodeHash leaves l (by omega) (2 * (e >>> (l.val + 1)) + 1))
        (climbChildren nodeHash e pi' b l) := by
  -- The honest opening reaches the same node, so the two openings bind.
  rw [← fold_path] at heq
  rcases fold_binding heq.symm with ⟨hab, hpi⟩ | ⟨l, hcol⟩
  · exact .inl ⟨hab.symm, hpi.symm⟩
  · rw [climbChildren_path] at hcol
    exact .inr ⟨l, hcol⟩

/-- An opening of a leaf `e < 2^height` that reaches the root is honest, or a second preimage exists. -/
theorem fold_eq_root_binding {e : Nat} (he : e < 2 ^ height) {b : α} {pi' : Vector α height}
    (heq : fold nodeHash e b pi' = root nodeHash leaves) :
    (b = leaves e ∧ pi' = path nodeHash leaves e) ∨
      ∃ l : Fin height, Collision nodeHash l.succ (e >>> (l.val + 1))
        (node nodeHash leaves l (by omega) (2 * (e >>> (l.val + 1))),
          node nodeHash leaves l (by omega) (2 * (e >>> (l.val + 1)) + 1))
        (climbChildren nodeHash e pi' b l) := by
  -- Leaf `e` sits below the root, so its top-level ancestor is node 0.
  have htop : e >>> height = 0 := by rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt he]
  exact fold_eq_node_binding (heq.trans (by rw [htop]; rfl))

end EthLib.Cryptography.Merkle
