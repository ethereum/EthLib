module

public import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Computations with errors, run against a full answer table

A computation with errors over oracle calls can run with every call answered by a fixed table.

Each step then runs as the plain step with errors, with the answers of the table.

So a proof in the random oracle model can read a replayed run as a plain computation.
-/

@[expose] public section

namespace EthLib.Cryptography

open OracleComp OracleSpec

variable {ι : Type} {spec : OracleSpec ι} (f : QueryImpl spec Id) {ε ε' α β : Type}

/-- A step with errors, run against a table, is the step with errors of the two runs. -/
theorem evalWithAnswerFn_exceptT_bind (x : ExceptT ε (OracleComp spec) α)
    (k : α → ExceptT ε (OracleComp spec) β) :
    evalWithAnswerFn f (x >>= k).run =
      (evalWithAnswerFn f x.run).bind fun a => evalWithAnswerFn f (k a).run := by
  rw [ExceptT.run_bind, evalWithAnswerFn_bind]
  cases evalWithAnswerFn f x.run <;> rfl

/-- A value with errors, run against a table, is the value. -/
theorem evalWithAnswerFn_exceptT_pure (a : α) :
    evalWithAnswerFn f (pure a : ExceptT ε (OracleComp spec) α).run = .ok a := rfl

/-- An error, run against a table, is the error. -/
theorem evalWithAnswerFn_exceptT_throw (e : ε) :
    evalWithAnswerFn f (throw e : ExceptT ε (OracleComp spec) α).run = .error e := rfl

/-- A lifted computation, run against a table, never fails. -/
theorem evalWithAnswerFn_exceptT_lift (x : OracleComp spec α) :
    evalWithAnswerFn f (ExceptT.lift x : ExceptT ε (OracleComp spec) α).run =
      .ok (evalWithAnswerFn f x) := by
  rw [ExceptT.run_lift, evalWithAnswerFn_map]

/-- A lifted computation with errors, run against a table, is itself. -/
theorem evalWithAnswerFn_exceptT_liftExcept (x : Except ε α) :
    evalWithAnswerFn f (liftM x : ExceptT ε (OracleComp spec) α).run = x := rfl

/-- Renamed errors, run against a table, are the renamed errors of the run. -/
theorem evalWithAnswerFn_exceptT_adapt (g : ε → ε') (x : ExceptT ε (OracleComp spec) α) :
    evalWithAnswerFn f (ExceptT.adapt g x).run = (evalWithAnswerFn f x.run).mapError g := by
  rw [ExceptT.run_adapt, evalWithAnswerFn_map]

/-- A list map with errors, run against a full answer table, maps the runs. -/
theorem evalWithAnswerFn_exceptT_mapM (g : α → ExceptT ε (OracleComp spec) β) :
    (xs : List α) → evalWithAnswerFn f (xs.mapM g).run =
      xs.mapM (fun x => evalWithAnswerFn f (g x).run)
  | [] => rfl
  | x :: rest => by
    simp only [List.mapM_cons, evalWithAnswerFn_exceptT_bind,
      evalWithAnswerFn_exceptT_mapM g rest, evalWithAnswerFn_exceptT_pure]
    rfl

end EthLib.Cryptography
