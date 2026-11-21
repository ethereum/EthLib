module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.ConcreteStatement
public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Hash costs in the leanXMSS security game

The cost writer records one unit for each hash call.

Forgetting its sum preserves the output from the same random oracle.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability
open OracleComp OracleSpec
open XmssSecurity (HashSpec OracleWorld)

/-- Forgetting the hash count preserves every event on the game output. -/
theorem prEvent_forgetHashCost {α : Type} (game : OracleComp OracleWorld α) (P : α → Prop) :
    Pr{let result ← (simulateQ countedOracle game).run.run' ∅}[P result.1]
      = Pr{let x ← (simulateQ HashSpec.romImpl game).run' ∅}[P x] := by
  let fee : OracleWorld.Domain → Nat := fun | .inl _ => 0 | .inr _ => 1
  have h := congrArg (fun c : StateT (QueryCache HashSpec) ProbComp α => c.run' ∅)
    (QueryImpl.fst_map_run_simulateQ_withAddCost HashSpec.romImpl fee game)
  rw [StateT.run'_map'] at h
  rw [← h, prEvent_map]
  rfl
end EthLib.Cryptography.Xmss.Unforgeability
