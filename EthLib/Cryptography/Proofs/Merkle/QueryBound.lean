module

public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic

/-!
# Proofs: how many calls a Merkle tree makes

Each node hash makes at most one oracle query, and each leaf at most `c`.

Then a climb makes at most one query per sibling.

A node makes at most one per leaf query and per hash below it.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

open OracleSpec OracleComp

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α : Type}
  {hash : Position → α → α → OracleComp spec α}

/-- A climb costs one hash per sibling. -/
theorem isQueryBoundP_climb (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (siblings : List α) (q : Position) (current : α),
      IsQueryBoundP (climb hash q current siblings) p siblings.length
  | [], _, _ => isQueryBoundP_pure _ _ _
  | _ :: rest, q, current => by
    rw [climb]
    refine (isQueryBoundP_bind (hhash _ _ _) fun _ _ =>
      isQueryBoundP_climb hhash rest _ _).mono ?_
    simp only [List.length_cons]
    omega

variable {leaves : Nat → OracleComp spec α} {c : Nat}

/-- A node at `level` costs its `2^level` leaves of cost `c` and its `2^level - 1` hashes. -/
theorem isQueryBoundP_node (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ q : Position, IsQueryBoundP (node hash leaves q) p (2 ^ q.level * (c + 1) - 1) := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => exact (hleaves j).mono (by simp)
  | succ level ih =>
    rw [node_succ]
    have h1 : 1 ≤ 2 ^ level * (c + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 2 ^ (level + 1) * (c + 1) = 2 * (2 ^ level * (c + 1)) := by ring
    refine (isQueryBoundP_bind (ih _) fun _ _ =>
      isQueryBoundP_bind (ih _) fun _ _ => hhash _ _ _).mono ?_
    simp only at h1 h2 ⊢
    omega

/-- A build at `level` costs as the node at its position. -/
theorem isQueryBoundP_build (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) (q : Position) :
    IsQueryBoundP (build hash leaves q) p (2 ^ q.level * (c + 1) - 1) :=
  isQueryBoundP_node
    (fun j => (isQueryBoundP_bind (m := 0) (hleaves j) fun _ _ => isQueryBoundP_pure _ _ 0).mono
      (le_of_eq (Nat.add_zero _)))
    (fun _ _ _ => (isQueryBoundP_bind (m := 0) (hhash _ _ _) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (le_of_eq (Nat.add_zero _))) q

/-- The `n` siblings above a node at `level` cost the nodes they are. -/
theorem isQueryBoundP_siblings (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (q : Position) (n : Nat), IsQueryBoundP (siblings hash leaves q n) p
      (2 ^ (q.level + n) * (c + 1) - 2 ^ q.level * (c + 1))
  | q, 0 => by simp [siblings]
  | q, n + 1 => by
    simp only [siblings]
    have h1 : 1 ≤ 2 ^ q.level * (c + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
    have h2 : 2 ^ (q.level + 1) * (c + 1) = 2 * (2 ^ q.level * (c + 1)) := by ring
    have h3 : 2 ^ (q.level + 1) * (c + 1) ≤ 2 ^ (q.level + 1 + n) * (c + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h4 : q.level + (n + 1) = q.level + 1 + n := by omega
    rw [h4]
    refine (isQueryBoundP_bind (isQueryBoundP_node hleaves hhash q.sibling) fun _ _ =>
      isQueryBoundP_bind (isQueryBoundP_siblings hleaves hhash q.parent n)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
    simp only [Position.sibling_level, Position.parent_level]
    omega

end EthLib.Cryptography.Merkle
