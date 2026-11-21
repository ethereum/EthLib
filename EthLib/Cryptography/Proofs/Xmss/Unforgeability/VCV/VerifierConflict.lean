module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierProbe
public import VCVio.OracleComp.QueryTracking.RandomOracle.PublicReplay
import all VCVio.OracleComp.QueryTracking.RandomOracle.PublicReplay
public import VCVio.OracleComp.QueryTracking.RandomOracle.Undisclosed
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifierProbe
import EthLib.Cryptography.Proofs.Xmss.MapMonad

/-!
# An undisclosed predecessor tested by the real verifier

The verifier makes its full-word queries before pending graph labels are sampled.

Suppose the later canonical predecessor equals the submitted value.

The ordinary query witnesses a conflict unless its predecessor was already drawn.

See the leanXMSS draft, sections "WOTS+C" and "The scheme".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe

open EthLib.Cryptography OracleSpec OracleComp Constants HashSig TwoLayerGraph
open ChainGraph (Word Public digestEquiv)

/-- One full-word verifier call over just the two public halves. -/
def halvesHash (b : ByteArray) : OracleComp Public (Vector UInt8 32) := do
  let lo ← query (spec := Public) (.inl b.data.toList)
  let hi ← query (spec := Public) (.inr b.data.toList)
  return ofOutput (PairedHashWord.halves.symm (lo, hi))

/-- Read both halves from the merged public table before completing the hidden cells. -/
noncomputable def hashAt (pp : PublicParam) (st : Honest.SharedState) (b : ByteArray) :
    Option (Vector UInt8 32) :=
  simulateQ ((graph pp).merge st).toPartialImpl (halvesHash b)

local notation "requests" => CanonicalGraph.publicRequests
    (X := Start) (K := Row) (R := Word) (pub := Public)

/-- Lift a raw public full-word call into the shared graph. -/
theorem public_image (b : ByteArray) : simulateQ requests (halvesHash b) = Honest.hash b := by
  simp only [halvesHash, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure]
  rfl

private theorem verifier_image (pp : PublicParam) (l : Layer) (e : Nat) (m : ByteArray)
    (sig : LayerSignature) :
    simulateQ requests (layerRoot halvesHash pp l e m sig)
      = layerRoot Honest.hash pp l e m sig := by
  rw [layerRoot_map_monad (simulateQ requests) (simulateQ_pure _) (simulateQ_bind _)]
  simp only [public_image]

private theorem low_read {pp : PublicParam} {st : Honest.SharedState} {b : ByteArray}
    (read : (hashAt pp st b).isSome) : ((graph pp).merge st (.inl b.data.toList)).isSome := by
  simp only [hashAt, halvesHash, simulateQ_bind, simulateQ_HasQuery_query, simulateQ_pure,
    QueryCache.toPartialImpl_apply] at read
  cases low : (graph pp).merge st (.inl b.data.toList) with
  | none => rw [low] at read; contradiction
  | some x => rfl

/-- A supported verifier layer replays in any clean extension.

This includes its own endpoint before the hidden cells are filled.
-/
theorem layer_replay (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature)
    {s : Honest.SharedState × List Cell} {z : Option Digest × Honest.SharedState × List Cell}
      {before : Honest.SharedState}
    (run : z ∈ support ((simulateQ (graph pp).deferredImpl
      (layerRoot Honest.hash pp l e msg sig)).run s))
    (later : z.2.1 ≤ before) (clean : ¬(graph pp).Conflict before) :
    layerRoot (hashAt pp before) pp l e msg sig = some z.1 := by
  rw [← verifier_image] at run
  have replay := (graph pp).deferred_public_replay
      (layerRoot halvesHash pp l e msg sig) run later clean
  rw [layerRoot_map_monad (simulateQ _) (simulateQ_pure _) (simulateQ_bind _)] at replay
  exact replay

/-- The real grinding loop can replay all the tested randomizers using the same public words.

It suffices to replay any conflict-free extension of the end of that loop.
-/
theorem finder_replay (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (base : Randomizer) (counter fuel : Nat) {initial : Honest.SharedState × List Cell} {z}
    (run : z ∈ support ((simulateQ (graph pp).deferredImpl
      (Xmss.Internal.findCodeword Honest.hash pp l e msg base counter fuel)).run initial))
    {later : Honest.SharedState} (extended : z.2.1 ≤ later) (clean : ¬ (graph pp).Conflict later) :
    Xmss.Internal.findCodeword (hashAt pp later) pp l e msg base counter fuel = some z.1 := by
  let raw := Xmss.Internal.findCodeword halvesHash pp l e msg base counter fuel
  have image : simulateQ requests raw
      = Xmss.Internal.findCodeword Honest.hash pp l e msg base counter fuel := by
    rw [show raw = _ from rfl, findCodeword_map_monad (simulateQ requests) (simulateQ_pure _)
      (simulateQ_bind _)]
    simp only [public_image]
  rw [← image] at run
  have replay := (graph pp).deferred_public_replay raw run extended clean
  rw [show raw = _ from rfl, findCodeword_map_monad (simulateQ _) (simulateQ_pure _)
      (simulateQ_bind _)] at replay
  exact replay

/-- Suppose the candidate matches after the fill.

Its public probe found a drawn predecessor or caused an ordinary-to-canonical graph conflict.
-/
theorem conflict_or_drawn (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) (root : Digest) (digits : Vector (Fin CHAIN_LENGTH) V)
    (before final : Honest.SharedState) (later : before ≤ final)
    (verified : layerRoot (hashAt pp before) pp l e msg sig = some (some root))
    (decoded : (messageDigest (hashAt pp before) pp l
      (UInt32.ofNat e) msg sig.randomizer).bind codeword? = some digits)
    (i : Fin V) (nonterminal : digits[i].val < CHAIN_LENGTH - 1)
    (matched : final.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)) =
      some (digestEquiv sig.chainValues[i])) :
    (graph pp).Conflict final ∨
      before.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val))
        = some (digestEquiv sig.chainValues[i]) := by
  let j : Fin (CHAIN_LENGTH - 1) := ⟨digits[i].val, nonterminal⟩
  let k : Row := .inl (l, .chain (UInt32.ofNat e) i j)
  let v := digestEquiv sig.chainValues[i]
  have childrenEq : (graph pp).ch k = [inLayer l (LayerGraph.position
      (UInt32.ofNat e) i j.val)] := by
    change [inLayer l (LayerGraph.chainCell _ _ _)] = _
    rw [LayerGraph.chainCell_eq]
  have ready (st : Honest.SharedState) : (graph pp).childVals st k = some [v] ↔
      st.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i j.val)) = some v := by
    rw [(graph pp).childVals_eq_some_iff, childrenEq]
    simp
  by_cases already : (graph pp).childVals before k = some [v]
  · exact Or.inr ((ready before).mp already)
  · apply Or.inl
    apply (graph pp).conflict_of_merged_before_ready later already _ ((ready final).mpr matched)
    have raw := low_read (first_probe _ pp l e msg sig root digits decoded verified i nonterminal)
    change ((graph pp).merge before (.inl (input pp (l, .chain (UInt32.ofNat e) i j) [v]))).isSome
    change ((graph pp).merge before (.inl (thInput pp _
      (packBytes (ofBV 16 v) ++ packBytes (uintToBytes 16 i.val))).data.toList)).isSome
    rw [show ofBV 16 v = sig.chainValues[i] from digestEquiv.symm_apply_apply _]
    exact raw

attribute [local irreducible] Xmss.layerRoot Xmss.otsLeaf Xmss.messageDigest Xmss.codeword?

-- Even a rejecting OTS codeword must first read the message digest.
private theorem message_read (H : ByteArray → Option (Vector UInt8 32)) (pp : PublicParam)
    (l : Layer) (e : Nat) (msg : ByteArray) (sig : LayerSignature) {root : Option Digest}
    (verifies : layerRoot H pp l e msg sig = some root) :
    ∃ digest, messageDigest H pp l (UInt32.ofNat e) msg sig.randomizer = some digest := by
  rw [layerRoot] at verifies
  obtain ⟨leaf, evaluated, _⟩ := Option.bind_eq_some_iff.mp verifies
  rw [otsLeaf] at evaluated
  obtain ⟨digest, read, _⟩ := Option.bind_eq_some_iff.mp evaluated
  exact ⟨digest, read⟩

/-- A genuine supported verifier tested this submitted nonterminal value before the fill.

A missing child whose opening matches later is charged to the original conflict.
-/
theorem conflict_of_supported_opening (pp : PublicParam) (l : Layer) (e : Nat) (msg : ByteArray)
    (sig : LayerSignature) (root : Digest) (digits : Vector (Fin CHAIN_LENGTH) V)
    (initial finish : Honest.SharedState × List Cell) (before final : Honest.SharedState)
    (run : (some root, finish) ∈ support ((simulateQ (graph pp).deferredImpl
      (layerRoot Honest.hash pp l e msg sig)).run initial))
    (beforeFill : finish.1 ≤ before) (later : before ≤ final)
    (decoded : (messageDigest (hashAt pp final) pp l
      (UInt32.ofNat e) msg sig.randomizer).bind codeword? = some digits)
    (i : Fin V) (nonterminal : digits[i].val < CHAIN_LENGTH - 1)
    (missing : before.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)) = none)
    (matched : final.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i digits[i].val)) =
      some (digestEquiv sig.chainValues[i])) : (graph pp).Conflict final := by
  by_contra clean
  have verified := layer_replay pp l e msg sig run beforeFill (fun h =>
      clean (CanonicalGraph.Conflict.mono (graph pp) later h))
  obtain ⟨d, early⟩ := message_read _ pp l e msg sig verified
  obtain ⟨d', late, parsed⟩ := Option.bind_eq_some_iff.mp decoded
  rw [messageDigest, th] at early
  obtain ⟨w, raw, proj⟩ := Option.bind_eq_some_iff.mp early
  have kept := QueryCache.simulateQ_toPartialImpl_mono ((graph pp).merge_le_merge later clean)
    (halvesHash _) raw
  change hashAt pp final (thInput pp (addrMsg l (UInt32.ofNat e)) (msg ++ packBytes sig.randomizer))
      = some w at kept
  rw [messageDigest, th] at late
  rw [kept] at late
  have same : d = d' := (Option.some.inj proj).symm.trans (Option.some.inj late)
  have decodedBefore : (messageDigest (hashAt pp before) pp l
      (UInt32.ofNat e) msg sig.randomizer).bind
      codeword? = some digits := by
    apply Option.bind_eq_some_iff.mpr
    refine ⟨d, ?_, same ▸ parsed⟩
    rw [messageDigest, th]
    exact Option.bind_eq_some_iff.mpr ⟨w, raw, proj⟩
  have drawn := (conflict_or_drawn pp l e msg sig root digits before final later verified
      decodedBefore
    i nonterminal matched).resolve_left clean
  rw [missing] at drawn
  contradiction

end EthLib.Cryptography.Xmss.Unforgeability.VCV.VerifierProbe
