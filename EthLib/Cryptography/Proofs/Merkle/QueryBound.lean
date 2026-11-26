module

public import EthLib.Cryptography.Proofs.Merkle.Binding.Collision
public import VCVio.OracleComp.QueryTracking.QueryBound.Simulation

/-!
# Proofs: how many calls a Merkle tree makes

Each node hash is charged at most `h`, and each leaf at most `L`.

Then a climb is charged `h` per sibling, and the collision search `2 h` per level of both climbs.

A node is charged its leaves and the hashes below it.

A count of the queries that a predicate accepts is the charge of one per such query.

A monad morphism, such as answering the queries, maps the search to the search over its hash.
-/

@[expose] public section

namespace EthLib.Cryptography.Merkle

open OracleSpec OracleComp

open PFunctor.FreeM (IsChargeBound isChargeBound_pure)

/-! ## Answering the oracle -/

/-- A monad morphism maps the collision search to the search over its image of the node hash. -/
theorem mmap_findCollision {m n : Type → Type} [Monad m] [Monad n] {α : Type} [DecidableEq α]
    (φ : m →ᵐ n) (hash : Position → α → α → m α) :
    ∀ (s t : List α) (p : Position) (a b : α), φ (findCollision hash p a b s t) =
      findCollision (fun p left right => φ (hash p left right)) p a b s t
  | [], _, _, _, _ => φ.mmap_pure _
  | _ :: _, [], _, _, _ => φ.mmap_pure _
  | _ :: s, _ :: t, _, _, _ => by
    -- The morphism passes through both hash calls and each branch of the test.
    simp only [findCollision, MonadHom.mmap_bind, MonadHom.mmap_ite, MonadHom.mmap_pure,
      mmap_findCollision φ hash s t]

/-! ## Charged calls

Each node hash is charged at most `h`, and each leaf at most `L`.
-/

section Charge

variable {ι : Type} {spec : OracleSpec ι} {c : ι → ℕ} {α : Type}
  {hash : Position → α → α → OracleComp spec α} {h : ℕ}

/-- A climb is charged one hash per sibling. -/
theorem isChargeBound_climb (hhash : ∀ q a b, IsChargeBound (hash q a b) c h) :
    ∀ (siblings : List α) (q : Position) (current : α),
      IsChargeBound (climb hash q current siblings) c (siblings.length * h)
  | [], _, _ => isChargeBound_pure _
  | _ :: rest, q, current => by
    rw [climb]
    refine ((hhash _ _ _).bind fun _ => isChargeBound_climb hhash rest _ _).mono ?_
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- The collision search is charged at most two hashes per level that both climbs reach. -/
theorem isChargeBound_findCollision [DecidableEq α]
    (hhash : ∀ q a b, IsChargeBound (hash q a b) c h) :
    ∀ (s t : List α) (q : Position) (a b : α),
      IsChargeBound (findCollision hash q a b s t) c (2 * min s.length t.length * h)
  | [], _, _, _, _ => isChargeBound_pure _
  | _ :: _, [], _, _, _ => isChargeBound_pure _
  | _ :: s, _ :: t, q, a, b => by
    simp only [findCollision]
    -- Each climb hashes its pair, then the search stops or goes on from the two parents.
    refine ((hhash _ _ _).bind fun _ => (hhash _ _ _).bind (B₂ := 2 * min s.length t.length * h)
      fun _ => ?_).mono (le_of_eq ?_)
    · split
      · exact isChargeBound_pure _
      · exact isChargeBound_findCollision hhash s t _ _ _
    · simp only [List.length_cons, min_add_add_right]
      ring

variable {leaves : Nat → OracleComp spec α} {L : ℕ}

/-- A node at `level` is charged its `2^level` leaves and its `2^level - 1` hashes. -/
theorem isChargeBound_node (hleaves : ∀ j, IsChargeBound (leaves j) c L)
    (hhash : ∀ q a b, IsChargeBound (hash q a b) c h) :
    ∀ q : Position,
      IsChargeBound (node hash leaves q) c (2 ^ q.level * L + (2 ^ q.level - 1) * h) := by
  rintro ⟨level, j⟩
  induction level generalizing j with
  | zero => exact (hleaves j).mono (by simp)
  | succ level ih =>
    rw [node_succ]
    refine ((ih _).bind fun _ => (ih _).bind fun _ => hhash _ _ _).mono (le_of_eq ?_)
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ level = k + 1 :=
      ⟨2 ^ level - 1, by have := Nat.one_le_two_pow (n := level); omega⟩
    simp only [Nat.pow_succ, hk, Nat.add_sub_cancel]
    rw [show (k + 1) * 2 - 1 = 2 * k + 1 by omega]
    ring

/-- A build at `level` is charged as the node at its position. -/
theorem isChargeBound_build (hleaves : ∀ j, IsChargeBound (leaves j) c L)
    (hhash : ∀ q a b, IsChargeBound (hash q a b) c h) (q : Position) :
    IsChargeBound (build hash leaves q) c (2 ^ q.level * L + (2 ^ q.level - 1) * h) :=
  isChargeBound_node
    (fun j => ((hleaves j).bind fun _ => isChargeBound_pure (B := 0) _).mono le_rfl)
    (fun _ _ _ => ((hhash _ _ _).bind fun _ => isChargeBound_pure (B := 0) _).mono le_rfl) q

/-- The `n` siblings above a node at `level` are charged as the `n` nodes they are. -/
theorem isChargeBound_siblings (hleaves : ∀ j, IsChargeBound (leaves j) c L)
    (hhash : ∀ q a b, IsChargeBound (hash q a b) c h) :
    ∀ (q : Position) (n : Nat), IsChargeBound (siblings hash leaves q n) c
      ((2 ^ (q.level + n) - 2 ^ q.level) * (L + h))
  | q, 0 => by simp [siblings]
  | q, n + 1 => by
    simp only [siblings]
    refine ((isChargeBound_node hleaves hhash q.sibling).bind fun _ =>
      (isChargeBound_siblings hleaves hhash q.parent n).bind
        fun _ => isChargeBound_pure (B := 0) _).mono ?_
    simp only [Position.sibling_level, Position.parent_level, Nat.add_zero]
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ q.level = k + 1 :=
      ⟨2 ^ q.level - 1, by have := Nat.one_le_two_pow (n := q.level); omega⟩
    obtain ⟨d, hd⟩ : ∃ d, 2 ^ (q.level + 1 + n) = 2 * (k + 1) + d :=
      ⟨2 ^ (q.level + 1 + n) - 2 * (k + 1), by
        have : 2 ^ (q.level + 1) ≤ 2 ^ (q.level + 1 + n) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [Nat.pow_succ] at this
        omega⟩
    rw [show q.level + (n + 1) = q.level + 1 + n by omega, hd, hk, Nat.pow_succ, hk,
      Nat.add_sub_cancel, show 2 * (k + 1) + d - (k + 1) = k + 1 + d by omega,
      show 2 * (k + 1) + d - (k + 1) * 2 = d by omega]
    nlinarith

end Charge

/-! ## Counted queries

A count of the queries that `p` accepts charges one per such query.
-/

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p] {α : Type}
  {hash : Position → α → α → OracleComp spec α}

/-- A climb costs one hash per sibling. -/
theorem isQueryBoundP_climb (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (siblings : List α) (q : Position) (current : α),
      IsQueryBoundP (climb hash q current siblings) p siblings.length := fun siblings q current =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_climb
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) siblings q
      current).mono (le_of_eq (Nat.mul_one _))

/-- A climb makes no query that `p` accepts when no node hash makes one. -/
theorem isQueryBoundP_climb_zero (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 0) :
    ∀ (siblings : List α) (q : Position) (current : α),
      IsQueryBoundP (climb hash q current siblings) p 0 := fun siblings q current =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_climb
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) siblings q
      current).mono (le_of_eq (Nat.mul_zero _))

/-- A climb costs at most one query per sibling in all, when each node hash costs at most one. -/
theorem isTotalQueryBound_climb (hhash : ∀ q a b, IsTotalQueryBound (hash q a b) 1)
    (siblings : List α) (q : Position) (current : α) :
    IsTotalQueryBound (climb hash q current siblings) siblings.length :=
  -- A total count is the count of the queries that the always-true predicate accepts.
  (isQueryBoundP_true_iff _ _).mp <| isQueryBoundP_climb
    (fun q a b => (isQueryBoundP_true_iff _ _).mpr (hhash q a b)) siblings q current

/-- The collision search costs at most two hashes per level that both climbs reach. -/
theorem isQueryBoundP_findCollision [DecidableEq α]
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (s t : List α) (q : Position) (a b : α),
      IsQueryBoundP (findCollision hash q a b s t) p (2 * min s.length t.length) :=
  fun s t q a b => (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_findCollision
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) s t q a b).mono
      (le_of_eq (Nat.mul_one _))

/-- The collision search costs at most two queries in all per level that both climbs reach.

It holds when each node hash costs at most one query in all. -/
theorem isTotalQueryBound_findCollision [DecidableEq α]
    (hhash : ∀ q a b, IsTotalQueryBound (hash q a b) 1) (s t : List α) (q : Position) (a b : α) :
    IsTotalQueryBound (findCollision hash q a b s t) (2 * min s.length t.length) :=
  -- A total count is the count of the queries that the always-true predicate accepts.
  (isQueryBoundP_true_iff _ _).mp <| isQueryBoundP_findCollision
    (fun q a b => (isQueryBoundP_true_iff _ _).mpr (hhash q a b)) s t q a b

variable {leaves : Nat → OracleComp spec α} {c : Nat}

/-- A node at `level` costs its `2^level` leaves of cost `c` and its `2^level - 1` hashes. -/
theorem isQueryBoundP_node (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ q : Position, IsQueryBoundP (node hash leaves q) p (2 ^ q.level * (c + 1) - 1) := by
  intro q
  refine (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_node
    (fun j => (isQueryBoundP_iff_isChargeBound p _ _).1 (hleaves j))
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) q).mono ?_
  have := Nat.one_le_two_pow (n := q.level)
  rw [Nat.mul_one, Nat.mul_succ]
  omega

/-- A build at `level` costs as the node at its position. -/
theorem isQueryBoundP_build (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) (q : Position) :
    IsQueryBoundP (build hash leaves q) p (2 ^ q.level * (c + 1) - 1) := by
  refine (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_build
    (fun j => (isQueryBoundP_iff_isChargeBound p _ _).1 (hleaves j))
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) q).mono ?_
  have := Nat.one_le_two_pow (n := q.level)
  rw [Nat.mul_one, Nat.mul_succ]
  omega

/-- The `n` siblings above a node at `level` cost the nodes they are. -/
theorem isQueryBoundP_siblings (hleaves : ∀ j, IsQueryBoundP (leaves j) p c)
    (hhash : ∀ q a b, IsQueryBoundP (hash q a b) p 1) :
    ∀ (q : Position) (n : Nat), IsQueryBoundP (siblings hash leaves q n) p
      (2 ^ (q.level + n) * (c + 1) - 2 ^ q.level * (c + 1)) := fun q n =>
  (isQueryBoundP_iff_isChargeBound p _ _).2 <| (isChargeBound_siblings
    (fun j => (isQueryBoundP_iff_isChargeBound p _ _).1 (hleaves j))
    (fun q a b => (isQueryBoundP_iff_isChargeBound p _ _).1 (hhash q a b)) q n).mono
      (le_of_eq (Nat.sub_mul _ _ _))

end EthLib.Cryptography.Merkle
