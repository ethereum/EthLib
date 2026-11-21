module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.AcceptedOpening
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SignedHistory
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealClient

/-!
# One authenticated signing word for every opened chain

Log validity fixes the lower signing request at its leaf.

Different lower requests can share an upper key.

They sign the same stored root and return the same upper signature.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest VerifierProbe
open ChainGraph (digestEquiv)

private theorem same_entry {raw : RawLog} (valid : Valid (eraseLog raw))
    {a b : SignRequest} {sa sb : Signature} (left : (a,.ok sa) ∈ raw)
    (right : (b,.ok sb) ∈ raw) (same : a.leafIndex = b.leafIndex) : a = b ∧ sa = sb := by
  have unique : (raw.map fun p => p.1.leafIndex).Nodup := by
    simpa [Valid, eraseLog, List.map_map, Function.comp_def] using valid
  have eq := List.inj_on_of_nodup_map unique left right same
  exact ⟨(Prod.mk.inj eq).1, Except.ok.inj (Prod.mk.inj eq).2⟩

/-- The returned signing digits decode from the exact stored message and randomizer. -/
theorem LayerFact.decoded {pp l e msg sig x r s}
    (fact : LayerFact pp l e msg sig x r s) (clean : ¬ (graph pp).Conflict s) :
    (messageDigest (hashAt pp s) pp l (UInt32.ofNat e) msg sig.randomizer).bind codeword? =
      some x := by
  obtain ⟨_,_,replay⟩ := fact.find
  exact decode_finder (replay s le_rfl clean)

private theorem bottom_release {pp s raw idx i d}
    (h : ReleasedBefore pp s raw .bottom idx i d) :
    ∃ req sig x, (req,.ok sig) ∈ raw ∧ req.leafIndex = idx ∧
      Trial pp .bottom (UInt32.ofNat req.leafIndex.toNat) (packBytes req.message)
        sig.bottom.randomizer x s ∧ x[i] ≤ d := by
  obtain ⟨req,sig,log,_,_,x,_,_,trial,_,alt⟩ := h
  rcases alt with ⟨_,eq,le⟩ | ⟨bad,_⟩
  · exact ⟨req,sig,x,log,by simpa using eq.symm,trial,le⟩
  · cases bad

private theorem tree_word (idx : LeafIndex) :
    (UInt32.ofNat (bottomTree idx)).toNat = bottomTree idx := by
  apply UInt32.toNat_ofNat_of_lt'
  exact Nat.lt_of_le_of_lt (Nat.div_le_self idx.toNat _) idx.toNat_lt_size

private theorem top_release {pp s raw idx i d}
    (h : ReleasedBefore pp s raw .top (UInt32.ofNat (bottomTree idx)) i d) :
    ∃ req sig root y, (req,.ok sig) ∈ raw ∧ bottomTree req.leafIndex = bottomTree idx ∧
      s.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
        some (digestEquiv root) ∧
      Trial pp .top (UInt32.ofNat (bottomTree idx)) (packBytes root) sig.top.randomizer y s ∧
      y[i] ≤ d := by
  obtain ⟨req,sig,log,_,root,_,y,row,_,trial,alt⟩ := h
  rcases alt with ⟨bad,_⟩ | ⟨_,eq,le⟩
  · cases bad
  · have key := congrArg UInt32.toNat eq.symm
    rw [tree_word,tree_word] at key
    rw [key] at row trial
    exact ⟨req,sig,root,y,log,key,row,trial,le⟩

private theorem terminal_le (x d : Fin CHAIN_LENGTH)
    (h : ¬ d.val < CHAIN_LENGTH - 1) : x ≤ d := by
  have := x.isLt
  change x.val ≤ d.val
  omega

/-- All canonical openings on a lower key are authorized by one successful signed word. -/
theorem bottom_word {pp s last raw out} {idx : LeafIndex} {msg sig digits}
    (facts : LogFacts pp raw out last) (valid : Valid (eraseLog raw)) (later : s ≤ last)
    (clean : ¬ (graph pp).Conflict last)
    (opens : SignedOpenings pp s last raw .bottom idx.toNat msg sig)
    (decoded : (messageDigest (hashAt pp last) pp .bottom (UInt32.ofNat idx.toNat)
      msg sig.randomizer).bind codeword? = some digits)
    (cells : ∀ i : Fin V, digits[i].val < CHAIN_LENGTH - 1 →
      last.2 (inLayer .bottom (LayerGraph.position (UInt32.ofNat idx.toNat) i digits[i].val)) =
        some (digestEquiv sig.chainValues[i]))
    (short : ∃ i : Fin V, digits[i].val < CHAIN_LENGTH - 1) :
    ∃ req signed x, (req,.ok signed) ∈ raw ∧ req.leafIndex = idx ∧
      LayerFact pp .bottom req.leafIndex.toNat (packBytes req.message) signed.bottom x out last ∧
      ∀ i : Fin V, x[i] ≤ digits[i] := by
  have release (i : Fin V) (h : digits[i].val < CHAIN_LENGTH - 1) :
      ReleasedBefore pp s raw .bottom idx i digits[i] := by
    simpa using opens digits decoded i h (cells i h)
  obtain ⟨i,hi⟩ := short
  obtain ⟨req,signed,_,mem,key,_,_⟩ := bottom_release (release i hi)
  obtain ⟨_,_,x,_,_,record,_⟩ := facts req signed mem
  refine ⟨req,signed,x,mem,key,record,?_⟩
  intro j
  by_cases hj : digits[j].val < CHAIN_LENGTH - 1
  · obtain ⟨other,reply,z,entry,otherKey,trial,le⟩ := bottom_release (release j hj)
    obtain ⟨rfl,rfl⟩ := same_entry valid mem entry (key.trans otherKey.symm)
    obtain rfl := Option.some.inj ((record.decoded clean).symm.trans (trial.decoded later clean))
    exact le
  · exact terminal_le _ _ hj

/-- All canonical openings on an upper key use one signing word even across different lower leaves.
-/
theorem top_word {pp s last raw out} (idx : LeafIndex) {msg sig digits}
    (facts : LogFacts pp raw out last) (later : s ≤ last) (clean : ¬ (graph pp).Conflict last)
    (opens : SignedOpenings pp s last raw .top (bottomTree idx) msg sig)
    (decoded : (messageDigest (hashAt pp last) pp .top (UInt32.ofNat (bottomTree idx))
      msg sig.randomizer).bind codeword? = some digits)
    (cells : ∀ i : Fin V, digits[i].val < CHAIN_LENGTH - 1 →
      last.2 (inLayer .top (LayerGraph.position (UInt32.ofNat (bottomTree idx)) i digits[i].val)) =
        some (digestEquiv sig.chainValues[i]))
    (short : ∃ i : Fin V, digits[i].val < CHAIN_LENGTH - 1) :
    ∃ req signed root y, (req,.ok signed) ∈ raw ∧ bottomTree req.leafIndex = bottomTree idx ∧
      last.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT (bottomTree idx)))) =
        some (digestEquiv root) ∧
      LayerFact pp .top (bottomTree idx) (packBytes root) signed.top y out last ∧
      ∀ i : Fin V, y[i] ≤ digits[i] := by
  have release (i : Fin V) (h : digits[i].val < CHAIN_LENGTH - 1) :=
    top_release (opens digits decoded i h (cells i h))
  obtain ⟨i,hi⟩ := short
  obtain ⟨req,signed,_,_,mem,key,_,_,_⟩ := release i hi
  have anchor := facts req signed mem
  obtain ⟨_,root,_,y,row,_,record⟩ := anchor
  rw [key] at row record
  refine ⟨req,signed,root,y,mem,key,row,record,?_⟩
  intro j
  by_cases hj : digits[j].val < CHAIN_LENGTH - 1
  · obtain ⟨other,reply,w,z,entry,otherKey,old,trial,le⟩ := release j hj
    have topEq := ((facts req signed mem).same_top (facts other reply entry)
      (key.trans otherKey.symm) clean).1
    have rootEq := digestEquiv.injective (Option.some.inj (row.symm.trans (later.2 old)))
    rw [← topEq, ← rootEq] at trial
    obtain rfl := Option.some.inj ((record.decoded clean).symm.trans (trial.decoded later clean))
    exact le
  · exact terminal_le _ _ hj

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
