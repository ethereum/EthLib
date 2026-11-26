module

public import VCVio.OracleComp.QueryTracking.WriterCost
public import VCVio.OracleComp.QueryTracking.QueryBound
public import EthLib.Cryptography.Proofs.SufCma

/-!
# Proofs: counting the queries of a computation

A computation, paired with the number of its queries that a predicate selects.

The leanXMSS and leanSPHINCS security proofs count their hash calls with it.

Over coins and a hash oracle, the count of hash calls answers like the oracle charged one per call.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleComp OracleSpec

variable {Index : Type} {spec : OracleSpec Index} {Result Next : Type}
  (selected : Index → Prop) [DecidablePred selected]

/-- The computation, paired with the number of its queries that satisfy the predicate. -/
noncomputable def counted (computation : OracleComp spec Result) :
    OracleComp spec (Result × Nat) :=
  OracleComp.construct (fun result => pure (result, 0))
    (fun input _ next => do
      let answer ← liftM (spec.query input)
      let result ← next answer
      pure (result.1, (if selected input then 1 else 0) + result.2)) computation

/-- A computation that makes no query counts none. -/
theorem counted_pure (result : Result) :
    counted selected (pure result : OracleComp spec Result) = pure (result, 0) := rfl

/-- A query adds one to the count of the rest when the predicate selects it. -/
theorem counted_query_bind (input : spec.Domain)
    (next : spec.Range input → OracleComp spec Result) :
    counted selected (liftM (spec.query input) >>= next) = (do
      let answer ← liftM (spec.query input)
      let result ← counted selected (next answer)
      pure (result.1, (if selected input then 1 else 0) + result.2)) := rfl

/-- One query counts one when the predicate selects it, and none otherwise. -/
theorem counted_query (input : spec.Domain) :
    counted selected (liftM (spec.query input)) =
      (fun answer => (answer, if selected input then 1 else 0)) <$>
        (liftM (spec.query input) : OracleComp spec _) := by
  change (do
    let answer ← liftM (spec.query input)
    pure (answer, (if selected input then 1 else 0) + 0)) = _
  simp only [Nat.add_zero, pure_bind, bind_pure_comp]

/-- Answering a counted computation is answering it at a cost of one per selected query. -/
theorem simulate_withCost {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl spec m) (computation : OracleComp spec α) :
    simulateQ impl (counted selected computation) =
      (simulateQ (impl.withAddCost (fun input => if selected input then 1 else (0 : Nat)))
        computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      simp only [counted_query_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, ih,
        WriterT.run_bind]
      simp [QueryImpl.withAddCost, QueryImpl.withCost,
        WriterT.run_bind, WriterT.run_liftM, WriterT.run_tell, map_eq_bind_pure_comp, bind_assoc]
      rfl

/-- Forgetting the count gives the computation back. -/
theorem counted_forget (computation : OracleComp spec Result) :
    Prod.fst <$> counted selected computation = computation := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [counted_pure, map_pure]
  | query_bind input next ih =>
      simp only [counted_query_bind, map_bind, bind_pure_comp, Functor.map_map, ih]

/-- The count of a sequence is the sum of the counts of its two parts. -/
theorem counted_bind (computation : OracleComp spec Result)
    (next : Result → OracleComp spec Next) :
    counted selected (computation >>= next) = (do
      let first ← counted selected computation
      let second ← counted selected (next first.1)
      pure (second.1, first.2 + second.2)) := by
  induction computation using OracleComp.inductionOn with
  | pure result => simp only [pure_bind, counted_pure, zero_add, Prod.mk.eta, bind_pure]
  | query_bind input continuation ih =>
      simp only [bind_assoc, counted_query_bind, ih, pure_bind, Nat.add_assoc]

/-- Mapping the result keeps the count. -/
theorem counted_map (computation : OracleComp spec Result) (f : Result → Next) :
    counted selected (f <$> computation) =
      (fun result => (f result.1, result.2)) <$> counted selected computation := by
  rw [show f <$> computation = computation >>= fun result => pure (f result) from
      (bind_pure_comp f computation).symm,
    counted_bind]
  simp only [counted_pure, Nat.add_zero, bind_pure_comp, map_pure]

/-! ## The hash calls of a computation over coins and a hash oracle -/

section HashCalls

variable {ι : Type} {hs : OracleSpec ι} {α β : Type}

/-- The computation, paired with the number of its hash calls. -/
noncomputable def countHashQueries (oa : OracleComp (unifSpec + hs) α) :
    OracleComp (unifSpec + hs) (α × ℕ) :=
  counted (SufCma.IsHashCall hs) oa

/-- A computation without a query counts none. -/
theorem countHashQueries_pure (a : α) :
    countHashQueries (pure a : OracleComp (unifSpec + hs) α) = pure (a, 0) := rfl

/-- A query adds one to the count of the rest when it is a hash call. -/
theorem countHashQueries_query_bind (t : (unifSpec + hs).Domain)
    (next : (unifSpec + hs).Range t → OracleComp (unifSpec + hs) α) :
    countHashQueries (liftM ((unifSpec + hs).query t) >>= next) = (do
      let answer ← liftM ((unifSpec + hs).query t)
      let result ← countHashQueries (next answer)
      pure (result.1, (if SufCma.IsHashCall hs t then 1 else 0) + result.2)) := rfl

/-- The count of a sequence is the sum of the counts of its two parts. -/
theorem countHashQueries_bind (oa : OracleComp (unifSpec + hs) α)
    (next : α → OracleComp (unifSpec + hs) β) :
    countHashQueries (oa >>= next) = (do
      let first ← countHashQueries oa
      let second ← countHashQueries (next first.1)
      pure (second.1, first.2 + second.2)) :=
  counted_bind _ oa next

/-- Mapping the result keeps the count. -/
theorem countHashQueries_map (oa : OracleComp (unifSpec + hs) α) (f : α → β) :
    countHashQueries (f <$> oa) = (fun result => (f result.1, result.2)) <$> countHashQueries oa :=
  counted_map _ oa f

/-- Forgetting the count gives the computation back. -/
theorem countHashQueries_forget (oa : OracleComp (unifSpec + hs) α) :
    Prod.fst <$> countHashQueries oa = oa :=
  counted_forget _ oa

/-- A computation over coins alone makes no hash call. -/
theorem countHashQueries_liftM (oa : ProbComp α) :
    countHashQueries (liftM oa : OracleComp (unifSpec + hs) α) =
      (fun a => (a, 0)) <$> (liftM oa : OracleComp (unifSpec + hs) α) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp only [liftM_pure, countHashQueries_pure, map_pure]
  | query_bind n next ih =>
      rw [liftM_bind]
      change countHashQueries (liftM ((unifSpec + hs).query (.inl n)) >>= _) = _
      simp only [countHashQueries_query_bind, ih, SufCma.not_isHashCall_inl, ite_false,
        Nat.zero_add, map_bind, bind_pure_comp, Functor.map_map]
      rfl

/-- Coins drawn first add nothing to the count of the rest. -/
theorem countHashQueries_liftM_bind (oa : ProbComp α)
    (next : α → OracleComp (unifSpec + hs) β) :
    countHashQueries ((liftM oa : OracleComp (unifSpec + hs) α) >>= next) =
      (liftM oa : OracleComp (unifSpec + hs) α) >>= fun a => countHashQueries (next a) := by
  rw [countHashQueries_bind, countHashQueries_liftM, bind_map_left]
  simp only [Nat.zero_add, Prod.mk.eta, bind_pure]

/-- Answering the counted computation is answering it at a cost of one per hash call. -/
theorem simulateQ_countHashQueries {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl (unifSpec + hs) m) (oa : OracleComp (unifSpec + hs) α) :
    simulateQ impl (countHashQueries oa) =
      (simulateQ (impl.withAddCost SufCma.hashCost) oa).run := by
  rw [countHashQueries, simulate_withCost,
    show (fun t => if SufCma.IsHashCall hs t then 1 else 0) = SufCma.hashCost from
      funext fun t => (SufCma.hashCost_eq_ite t).symm]

end HashCalls

end EthLib.Cryptography.HashSig
