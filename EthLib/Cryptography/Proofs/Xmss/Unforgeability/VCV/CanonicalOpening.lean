module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerConflict
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierConflict
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel.Match
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierConflict

/-!
# Recovering the inputs of a verified hash

The leanXMSS draft uses the low half of a hash for a tree or chain node.

See "Hashing and parameters" and "The scheme".

Outside the target collision event, a matching low half identifies the stored children.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word Public digestEquiv)

/-- A matching verifier query at a node with a drawn label recovers every input in order. -/
theorem matched_children (pp : PublicParam) (st : Honest.SharedState) (r : TwoLayerGraph.Role)
    (vs : List Word) (v : Word) (safe : ¬(keys pp).TCHazard ((subgraph pp).project st))
    (width : vs.length = LayerGraph.arity r.2) (label : st.2 (.inr (.inl r)) = some v)
    (physical : (graph pp).merge st (.inl (input pp r vs)) = some v) :
    (graph pp).childVals st (.inl r) = some vs := by
  by_contra different
  have size : vs.length = ((graph pp).ch (.inl r)).length := by
    simpa [graph, children] using width
  have ordinary := (graph pp).merge_pt_of_childVals_ne size different
  exact safe ⟨.inl (input pp r vs), r, v, decode_input pp r vs width, label,
    ordinary.symm.trans physical⟩

/-- The digest used by the verifier is precisely the low physical row of its public query. -/
theorem low_of_hashAt (pp : PublicParam) (st : Honest.SharedState) (b : ByteArray)
    (w : Vector UInt8 32) (read : hashAt pp st b = some w) :
    (graph pp).merge st (.inl b.data.toList) = some (digestEquiv (halfOf 0 w)) := by
  simp only [hashAt, halvesHash, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    QueryCache.toPartialImpl_apply] at read
  cases low : (graph pp).merge st (.inl b.data.toList) with
  | none => rw [low] at read; contradiction
  | some x =>
    rw [low] at read
    cases high : (graph pp).merge st (.inr b.data.toList) with
    | none => rw [high] at read; contradiction
    | some y =>
      rw [high] at read
      have bytes : ofOutput (PairedHashWord.halves.symm (x, y)) = w := Option.some.inj read
      rw [← bytes, PairedHashWord.first_half_bytes, Equiv.apply_symm_apply]
      exact congrArg some (digestEquiv.apply_symm_apply x).symm

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
