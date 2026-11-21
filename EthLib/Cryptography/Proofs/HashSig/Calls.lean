module

public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Merkle.Build
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# Proofs: the hash calls of a computation under fixed answers

When a fixed function answers every query, a computation queries a list of inputs in order.

Its length is the number of calls, and the calls of the shared loops add up as follows.

- A vector computed in order makes the calls of its entries.
- A chain walk of `s` steps makes `s` calls, when each step makes one.
- A climb makes one call per sibling, when each node hash makes one.
- A Merkle node of height `l` makes `(c + 1) * 2^l - 1` calls, when each leaf makes `c`.
- A build queries the inputs of the node at its position, in the same order.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleSpec OracleComp

/-! ## The inputs a computation queries -/

section Queries

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- The inputs a computation queries when `f` answers every query, in the order of the queries. -/
def queriesWith (f : QueryImpl spec Id) (oa : OracleComp spec α) : List spec.Domain :=
  OracleComp.construct (C := fun _ => List spec.Domain) (fun _ => [])
    (fun t _ rest => t :: rest (f t)) oa

/-- A computation that returns at once queries nothing. -/
@[simp] theorem queriesWith_pure (f : QueryImpl spec Id) (a : α) :
    queriesWith f (pure a : OracleComp spec α) = [] :=
  rfl

/-- A computation that starts with a query queries that input, then what the rest queries. -/
@[simp] theorem queriesWith_query_bind (f : QueryImpl spec Id) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    queriesWith f ((query t : OracleComp spec (spec.Range t)) >>= k)
      = t :: queriesWith f (k (f t)) :=
  rfl

/-- A computation with at most `n` queries on every path queries at most `n` inputs. -/
theorem length_queriesWith_le (f : QueryImpl spec Id) {oa : OracleComp spec α} {n : ℕ}
    (h : IsTotalQueryBound oa n) : (queriesWith f oa).length ≤ n := by
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind t k ih =>
    rw [isTotalQueryBound_query_bind_iff] at h
    have := ih (f t) (h.2 (f t))
    change (t :: queriesWith f (k (f t))).length ≤ n
    rw [List.length_cons]
    omega

/-- Two answer functions that agree on the inputs queried under the first give the same result.

The queries are then the same too. -/
theorem evalWithAnswerFn_congr (f g : QueryImpl spec Id) {oa : OracleComp spec α}
    (h : ∀ t ∈ queriesWith f oa, f t = g t) :
    evalWithAnswerFn f oa = evalWithAnswerFn g oa ∧ queriesWith f oa = queriesWith g oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    change ∀ t' ∈ t :: queriesWith f (k (f t)), f t' = g t' at h
    simp only [List.mem_cons, forall_eq_or_imp] at h
    obtain ⟨hk₁, hk₂⟩ := ih (f t) h.2
    change evalWithAnswerFn f (k (f t)) = evalWithAnswerFn g (k (g t)) ∧
      t :: queriesWith f (k (f t)) = t :: queriesWith g (k (g t))
    rw [← h.1]
    exact ⟨hk₁, congrArg _ hk₂⟩

end Queries

/-! ## The calls of the shared loops -/

section Loops

variable {ι : Type} {spec : OracleSpec ι} (F : QueryImpl spec Id)

/-- A bind queries what its first part queries, then what the rest queries after that answer. -/
theorem queriesWith_bind {α β : Type} (oa : OracleComp spec α) (k : α → OracleComp spec β) :
    queriesWith F (oa >>= k)
      = queriesWith F oa ++ queriesWith F (k (evalWithAnswerFn F oa)) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k' ih =>
    rw [bind_assoc]
    change t :: queriesWith F (k' (F t) >>= k) = (t :: queriesWith F (k' (F t))) ++ _
    rw [ih, evalWithAnswerFn_bind, List.cons_append]
    rfl

/-- A map queries what the computation queries. -/
theorem queriesWith_map {α β : Type} (g : α → β) (oa : OracleComp spec α) :
    queriesWith F (g <$> oa) = queriesWith F oa := by
  rw [map_eq_bind_pure_comp, queriesWith_bind]
  simp

/-- Computing a vector in order queries the inputs of its entries, entry 0 first. -/
theorem length_queriesWith_ofFnInOrder {α : Type} :
    ∀ (k : Nat) (f : Fin k → OracleComp spec α),
      (queriesWith F (HashSig.ofFnInOrder k f)).length = ∑ i, (queriesWith F (f i)).length
  | 0, _ => rfl
  | k + 1, f => by
    rw [HashSig.ofFnInOrder_succ, Fin.sum_univ_succ, queriesWith_bind, List.length_append,
      queriesWith_bind, List.length_append, length_queriesWith_ofFnInOrder k]
    simp

/-- A walk of `steps` steps queries `steps` inputs, when each step queries one. -/
theorem length_queriesWith_chain {α : Type} {k : Nat} (step : Fin k → α → OracleComp spec α)
    (hstep : ∀ i v, (queriesWith F (step i v)).length = 1) (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ k) (value : α),
      (queriesWith F (Wots.chain step start steps h value)).length = steps
  | 0, _, _ => rfl
  | s + 1, h, value => by
    rw [Wots.chain_succ, queriesWith_bind, List.length_append,
      length_queriesWith_chain step hstep start s _ value, hstep]

/-- A climb queries one input per sibling, when each node hash queries one. -/
theorem length_queriesWith_climb {α : Type} (hash : Merkle.Position → α → α → OracleComp spec α)
    (hhash : ∀ p left right, (queriesWith F (hash p left right)).length = 1) :
    ∀ (siblings : List α) (p : Merkle.Position) (current : α),
      (queriesWith F (Merkle.climb hash p current siblings)).length = siblings.length
  | [], _, _ => rfl
  | _ :: rest, p, current => by
    rw [Merkle.climb, queriesWith_bind, List.length_append, hhash,
      length_queriesWith_climb hash hhash rest, List.length_cons]
    omega

/-- A vector computed in order makes `n * c` calls, when each of its `n` entries makes `c`. -/
theorem length_queriesWith_ofFnInOrder_const {α : Type} (n c : Nat) (g : Fin n → OracleComp spec α)
    (hg : ∀ i, (queriesWith F (g i)).length = c) :
    (queriesWith F (ofFnInOrder n g)).length = n * c := by
  simp only [length_queriesWith_ofFnInOrder, hg, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

/-- A node of height `level` makes `(c + 1) * 2^level - 1` calls, when each leaf makes `c`.

That is `c` calls for each of its `2^level` leaves and one for each of its `2^level - 1` hashes. -/
theorem length_queriesWith_node {α : Type} (hash : Merkle.Position → α → α → OracleComp spec α)
    (leaves : Nat → OracleComp spec α) (c : Nat)
    (hhash : ∀ q left right, (queriesWith F (hash q left right)).length = 1)
    (hleaf : ∀ j, (queriesWith F (leaves j)).length = c) :
    ∀ level j, (queriesWith F (Merkle.node hash leaves ⟨level, j⟩)).length =
      (c + 1) * 2 ^ level - 1
  | 0, j => by
    rw [Merkle.node_zero, hleaf, Nat.pow_zero, Nat.mul_one, Nat.add_sub_cancel]
  | level + 1, j => by
    rw [Merkle.node_succ, queriesWith_bind, List.length_append, queriesWith_bind,
      List.length_append, hhash, length_queriesWith_node hash leaves c hhash hleaf level,
      length_queriesWith_node hash leaves c hhash hleaf level, Nat.pow_succ, ← Nat.mul_assoc]
    have hpos : 1 ≤ (c + 1) * 2 ^ level := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega

/-- A build queries the inputs of the node at its position, in the same order. -/
theorem queriesWith_build {α : Type} (hash : Merkle.Position → α → α → OracleComp spec α)
    (leaves : Nat → OracleComp spec α) (p : Merkle.Position) :
    queriesWith F (Merkle.build hash leaves p) = queriesWith F (Merkle.node hash leaves p) := by
  rw [← Merkle.value_build, queriesWith_map]

end Loops

end EthLib.Cryptography.HashSig
