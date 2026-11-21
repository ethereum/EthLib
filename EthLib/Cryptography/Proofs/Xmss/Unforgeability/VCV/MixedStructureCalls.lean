module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedFree
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedSignerProgram
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedStructure
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SelectedStructure

/-!
# Internal graph operations inside the selected budget

The emitted structural program uses only zero-cost internal operations.

Expansion recovers the complete original graph program for every response.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig TwoLayerGraph Honest OracleComp OracleSpec
open CanonicalGraph.PairedQueries

/-- A structural lookup preserves its original row, local state and remaining quota. -/
theorem structural_call {α : Type} (pp : PublicParam) {op : OracleComp SharedSpec α}
    (valid : StructuralSchedule op) :
    SameMixed pp (liftM op) (emitted emitStructure pp op) := by
  have pre := valid.2
  have free (r : ResidualCache pp) :
      ((emitted emitStructure pp op).run r).AllQueriesSatisfy
        (fun t => mixedCost (H := ChainGraph.Word) (F := HashOutput) (fun _ => 0) t = 0) := by
    simp only [emitted, StateT.run_monadLift, monadLift_self]
    exact allQueriesSatisfy_bind pre fun _ => allQueriesSatisfy_pure _ _
  have matched := mixed_free pp (liftM op) (emitted emitStructure pp op) free (fun r => by
    simp only [emitted, StateT.run_monadLift, monadLift_self, simulateQ_bind,
      simulateQ_pure, valid.1])
  simpa only [lift_twice] using matched

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
