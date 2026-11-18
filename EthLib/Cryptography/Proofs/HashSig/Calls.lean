module

public import EthLib.Cryptography.Proofs.HashSig
public import EthLib.Cryptography.Proofs.Wots
public import EthLib.Cryptography.Proofs.Merkle.Completeness
public import VCVio.OracleComp.QueryTracking.LoggingOracle.Core

/-!
# Proofs: the hash calls of a computation under fixed answers

When a fixed function answers every query, the logging oracle lists the queries in order.

Its length is the number of calls, and the calls of the shared loops add up as follows.

- A vector computed in order makes the calls of its entries.
- A chain walk of `s` steps makes `s` calls, when each step makes one.
- A Merkle node of height `l` makes `(c + 1) * 2^l - 1` calls, when each leaf makes `c`.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleComp OracleSpec

variable {ι : Type} {spec : OracleSpec ι} (f : QueryImpl spec Id)

/-- A computation that returns at once makes no call. -/
@[simp] theorem log_pure {α : Type} (x : α) :
    ((simulateQ f.withLogging (pure x : OracleComp spec α)).run).2 = [] :=
  rfl

/-- A computation that starts with a query logs it, then what the rest logs after its answer. -/
theorem log_query_bind {α : Type} (t : spec.Domain) (next : spec.Range t → OracleComp spec α) :
    ((simulateQ f.withLogging (liftM (spec.query t) >>= next)).run).2 =
      ⟨t, f t⟩ :: ((simulateQ f.withLogging (next (f t))).run).2 := by
  simp [QueryImpl.withLogging_apply, WriterT.run_bind, WriterT.run_tell]
  rfl

/-- A bind logs its first part, then the rest after the first part's answer. -/
theorem log_bind {α β : Type} (oa : OracleComp spec α) (next : α → OracleComp spec β) :
    ((simulateQ f.withLogging (oa >>= next)).run).2 =
      ((simulateQ f.withLogging oa).run).2 ++
        ((simulateQ f.withLogging (next (evalWithAnswerFn f oa))).run).2 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp only [pure_bind, log_pure, List.nil_append, evalWithAnswerFn_pure]
  | query_bind t rest ih =>
    rw [bind_assoc, log_query_bind, log_query_bind, ih, evalWithAnswerFn_bind,
      show evalWithAnswerFn f (liftM (spec.query t)) = f t from simulateQ_spec_query f t,
      List.cons_append]

/-- A bind makes the calls of its first part, then those of the rest. -/
theorem length_log_bind {α β : Type} (oa : OracleComp spec α) (next : α → OracleComp spec β) :
    ((simulateQ f.withLogging (oa >>= next)).run).2.length =
      ((simulateQ f.withLogging oa).run).2.length +
        ((simulateQ f.withLogging (next (evalWithAnswerFn f oa))).run).2.length := by
  rw [log_bind, List.length_append]

/-- A vector computed in order makes `n * c` calls, when each of its `n` entries makes `c`. -/
theorem length_log_ofFnInOrder {α : Type} (c : Nat) :
    ∀ (n : Nat) (g : Fin n → OracleComp spec α),
      (∀ i, ((simulateQ f.withLogging (g i)).run).2.length = c) →
        ((simulateQ f.withLogging (ofFnInOrder n g)).run).2.length = n * c
  | 0, _, _ => by
    rw [ofFnInOrder, log_pure, List.length_nil, Nat.zero_mul]
  | n + 1, g, hg => by
    rw [ofFnInOrder, length_log_bind, hg, length_log_bind,
      length_log_ofFnInOrder c n _ fun i => hg i.succ, log_pure, List.length_nil, Nat.succ_mul]
    omega

/-- A chain walk of `steps` steps makes `steps` calls, when each step makes one. -/
theorem length_log_chain {β : Type} {n : Nat} (step : Fin n → β → OracleComp spec β)
    (hstep : ∀ k value, ((simulateQ f.withLogging (step k value)).run).2.length = 1)
    (start : Nat) :
    ∀ (steps : Nat) (h : start + steps ≤ n) (value : β),
      ((simulateQ f.withLogging (Wots.chain step start steps h value)).run).2.length = steps
  | 0, _, _ => rfl
  | s + 1, h, value => by
    rw [Wots.chain_succ, length_log_bind, length_log_chain step hstep start s, hstep]

/-- A node of height `level` makes `(c + 1) * 2^level - 1` calls, when each leaf makes `c`.

That is `c` calls for each of its `2^level` leaves and one for each of its `2^level - 1` hashes. -/
theorem length_log_node {α : Type} (hash : Merkle.Position → α → α → OracleComp spec α)
    (leaves : Nat → OracleComp spec α) (c : Nat)
    (hhash : ∀ q left right, ((simulateQ f.withLogging (hash q left right)).run).2.length = 1)
    (hleaf : ∀ j, ((simulateQ f.withLogging (leaves j)).run).2.length = c) :
    ∀ level j, ((simulateQ f.withLogging (Merkle.node hash leaves ⟨level, j⟩)).run).2.length =
      (c + 1) * 2 ^ level - 1
  | 0, j => by
    rw [Merkle.node_zero, hleaf, Nat.pow_zero, Nat.mul_one, Nat.add_sub_cancel]
  | level + 1, j => by
    rw [Merkle.node_succ, length_log_bind, length_log_bind, hhash,
      length_log_node hash leaves c hhash hleaf level,
      length_log_node hash leaves c hhash hleaf level, Nat.pow_succ, ← Nat.mul_assoc]
    have hpos : 1 ≤ (c + 1) * 2 ^ level := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega

end EthLib.Cryptography.HashSig
