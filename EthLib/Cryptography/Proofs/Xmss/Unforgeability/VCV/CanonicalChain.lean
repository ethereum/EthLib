module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalOpening
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphLeaf

/-!
# Recovering a verified WOTS+C suffix

The leanXMSS draft, section "WOTS+C", hashes each submitted chain value up to its terminal position.

The leaf hashes all the resulting chain ends in index order.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word digestEquiv)

private theorem physical_th (pp : PublicParam) (st : Honest.SharedState) (addr : Address)
    (payload : ByteArray) (d : Digest) (read : th (hashAt pp st) pp addr payload = some d) :
    (graph pp).merge st (.inl (thInput pp addr payload).data.toList) = some (digestEquiv d) := by
  obtain ⟨w, raw, eqn⟩ := Option.bind_eq_some_iff.mp read
  exact (low_of_hashAt _ _ _ _ raw).trans (congrArg (some ∘ digestEquiv) (Option.some.inj eqn))

/-- A matching leaf hash fixes each of its 58 ordered chain ends. -/
theorem leaf_ends (pp : PublicParam) (st : Honest.SharedState) (l : Layer) (e : UInt32)
    (ends : Vector Digest V) (d : Digest) (safe : ¬(keys pp).TCHazard ((subgraph pp).project st))
    (label : st.2 (.inr (.inl (l, .leaf e))) = some (digestEquiv d))
    (read : otsLeafHash (hashAt pp st) pp l e ends = some d) (i : Fin V) :
    st.2 (inLayer l (LayerGraph.position e i (CHAIN_LENGTH - 1))) = some (digestEquiv ends[i]) := by
  have raw := physical_th pp st (addrLeaf l e) (packDigests ends) d read
  have stored := matched_children pp st (l, .leaf e) (LayerGraph.endWords ends) (digestEquiv d)
    safe (by simp [LayerGraph.endWords, LayerGraph.arity]) label (by
      change (graph pp).merge st (.inl (thInput pp _ (packDigests
        (LeafGraph.digests V (LayerGraph.endWords ends)))).data.toList) = _
      rwa [LayerGraph.endWords_digests])
  have rows := (graph pp).childVals_eq_some_iff.mp stored
  have length := (show i.val < ((graph pp).ch (.inl (l, .leaf e))).length by
    simp [graph, children, LayerGraph.children])
  have whereAt : ((graph pp).ch (.inl (l, .leaf e)))[i.val]'length =
      inLayer l (LayerGraph.position e i (CHAIN_LENGTH - 1)) := by
    let role (k : Fin V) : LayerGraph.Cell :=
      .inr (.inl (.chain e k ⟨CHAIN_LENGTH - 2, by decide⟩))
    have mapped := List.getElem_map (inLayer l) (l := List.ofFn role) (i := i.val)
      (h := by simp)
    have slot := List.getElem_ofFn (f := role) (i := i.val) (by simp)
    exact mapped.trans (congrArg (inLayer l) slot)
  have member := rows.get (i := i.val) length (by simp [LayerGraph.endWords])
  rw [List.get_eq_getElem, whereAt] at member
  simpa [LayerGraph.endWords, List.get_eq_getElem] using member

/-- Any verified suffix ending at a recorded chain cell fixes its submitted starting value. -/
theorem chain_opening (pp : PublicParam) (st : Honest.SharedState) (l : Layer)
    (e : UInt32) (i : Fin V) (safe : ¬(keys pp).TCHazard ((subgraph pp).project st))
    (start steps : Nat) (bound : start + steps ≤ CHAIN_LENGTH - 1) (a b : Digest)
    (walk : Wots.chain (chainStep (hashAt pp st) pp l e i) start steps bound a = some b)
    (last : st.2 (inLayer l (LayerGraph.position e i (start + steps))) = some (digestEquiv b)) :
    st.2 (inLayer l (LayerGraph.position e i start)) = some (digestEquiv a) := by
  induction steps generalizing b with
  | zero =>
    have same : a = b := Option.some.inj walk
    simpa [same] using last
  | succ n ih =>
    rw [Wots.chain] at walk
    obtain ⟨previous, walked, step⟩ := Option.bind_eq_some_iff.mp walk
    let j : Fin (CHAIN_LENGTH - 1) := ⟨start + n, by omega⟩
    have next := (LayerGraph.schedule pp l e i).next j
    have label : st.2 (.inr (.inl (l, .chain e i j))) = some (digestEquiv b) := by
      change LayerGraph.position e i (j.val + 1) = _ at next
      change st.2 (inLayer l (LayerGraph.position e i (j.val + 1))) = _ at last
      rwa [next] at last
    have raw := physical_th pp st (addrChain l e j)
      (packBytes previous ++ packBytes (uintToBytes 16 i.val)) b step
    have stored := matched_children pp st (l, .chain e i j) [digestEquiv previous] (digestEquiv b)
      safe rfl label (by
        change (graph pp).merge st (.inl (thInput pp _ (packBytes (ofBV 16 (digestEquiv previous))
          ++ packBytes (uintToBytes 16 i.val))).data.toList) = _
        rwa [show ofBV 16 (digestEquiv previous) = previous from digestEquiv.symm_apply_apply _])
    have rows := (graph pp).childVals_eq_some_iff.mp stored
    change List.Forall₂ _ [inLayer l (LayerGraph.chainCell e i j)] [digestEquiv previous] at rows
    rw [LayerGraph.chainCell_eq] at rows
    have atStart := rows.get (i := 0) (by change 0 < 1; decide) (by change 0 < 1; decide)
    exact ih (by omega) _ walked atStart

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
