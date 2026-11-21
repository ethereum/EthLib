module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphBound

/-!
# Replay a completed capped path inside the same graph

The cap tests the original full query before converting it into two row queries.

Replaying a returned value keeps both residual tables and the entire graph state.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open OracleComp OracleSpec HashSig SecretEncoding.Residual
open Classical

abbrev GraphState := RelabelState PairedHashWord.HalfSpec StartKey TwoLayerGraph.Row
    (BitVec digestBits)

variable {K α β : Type} (pp : PublicParam)
  (graph : CanonicalGraph PairedHashWord.HalfSpec StartKey K (BitVec digestBits))

theorem evaluate_pure (a : α) (extra : ResidualCache pp) (st) :
    evaluate pp graph (pure a) extra st = pure ((a, extra), st) := by
  simp [evaluate, residualProgram, keyedProgram, liftComp]

theorem evaluate_bind (body : OracleComp Source α) (next : α → OracleComp Source β)
    (extra : ResidualCache pp) (st) :
    evaluate pp graph (body >>= next) extra st = (do
      let ((value, localTables), graphTables) ← evaluate pp graph body extra st
      evaluate pp graph (next value) localTables graphTables) := by
  simp only [evaluate, residualProgram, keyedProgram, simulateQ_bind, StateT.run_bind, liftComp]

/-- Forget the operational cap on a completed graph path and preserve all its final state. -/
theorem evaluate_cap_some (body : OracleComp Source α) (left : Nat) (extra : ResidualCache pp)
    (st) (a : α) (extra' : ResidualCache pp) (st')
    (actual : ((some a, extra'), st') ∈ support
      (evaluate pp graph (WeightedCap.capCompOpt paidFee left body) extra st)) :
    ((a, extra'), st') ∈ support (evaluate pp graph body extra st) := by
  induction body using OracleComp.inductionOn generalizing left extra st with
  | pure b =>
    rw [WeightedCap.capCompOpt_pure, evaluate_pure, mem_support_pure_iff] at actual
    cases actual
    simp [evaluate_pure]
  | query_bind t next ih =>
    rw [WeightedCap.capCompOpt_query_bind] at actual
    split_ifs at actual with affordable
    · rw [evaluate_bind, mem_support_bind_iff] at actual ⊢
      obtain ⟨⟨⟨answer, localTables⟩, graphTables⟩, head, tail⟩ := actual
      exact ⟨((answer, localTables), graphTables), head, ih answer _ _ _ tail⟩
    · rw [evaluate_pure, mem_support_pure_iff] at actual
      cases actual

attribute [local irreducible] continuation

/-- The uncapped callbacks reproduce the signer and verifier on a completed graph path.

This holds even when the path contains an unrelated conflict.
-/
theorem graphRun_some (A : Adversary) (left : Nat) (w : HashOutput)
    (a : Outcome) (extra : ResidualCache (parameterOfWord w)) (st : GraphState)
    (actual : ((some a, extra), st) ∈ support (graphRun A left w)) :
    ((a, extra), st) ∈ support (runGraph (parameterOfWord w) (TwoLayerGraph.graph
      (parameterOfWord w))
      (continuation A (parameterOfWord w)) (afterWord w)) :=
  evaluate_cap_some (parameterOfWord w) (TwoLayerGraph.graph (parameterOfWord w))
    (continuation A (parameterOfWord w)) left _ _ a extra st actual

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
