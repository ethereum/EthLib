module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderRegisteredKeys
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CollisionTiming
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptRows
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerComparison
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainGraphWalk

/-!
# Matching a pair of physical reads to the signer's exact digits

Both descriptions use the same 256-bit answer at the signed input.

Reading its low half and decoding it determines all 58 returned digits.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open CachedCodeword TrialGraphWatch VerifierProbe PostSigning
open ChainGraph (digestEquiv)

/-- The first signed read decodes to the vector returned on its physical input. -/
theorem FirstPair.digits_of_read {pp s l m n a b y} {e : Nat} {last : SharedState}
    (pair : FirstPair pp s l (UInt32.ofNat e) m n a b y) (origin : Origin pp s)
    (order : Ordered s.2 (live s.1) (targets s.1))
    (fill : last ∈ support (RelabelState.endFill (physical s.1)))
    {x} (digit : (messageDigest (hashAt pp last) pp l (UInt32.ofNat e) n b.randomizer >>=
      codeword?) = some x) :
    y = x := by
  obtain ⟨d, read, decoded⟩ := Option.bind_eq_some_iff.mp digit
  obtain ⟨_,_,u,_,issued,_,signed,_,_,accepted,_,low,_⟩ := pair
  have row := ordinary_digest pp last l e n b d read
  obtain ⟨w,prior, logged,_,half,_⟩ := origin.filled_low
    (trialInput pp l (UInt32.ofNat e) n b.randomizer)
    ⟨l,_,n,b.randomizer,rfl⟩ fill row
  have eq : u = w := Option.some.inj ((order.saved signed).symm.trans (order.saved logged))
  rw [eq] at low
  have bytes : halfOf 0 (ofOutput w) = d := by
    rw [PairedHashWord.first_half_bytes, half]
    exact digestEquiv.symm_apply_apply d
  rw [low.symm.trans bytes] at accepted
  exact Option.some.inj (accepted.symm.trans decoded)

/-- Replay the complete lower finder at its actual logged input. -/
theorem Receipt.lower_digits {pp q idx msg sig} (c : Receipt pp q idx msg sig) {last}
    (later : (physical c.lowerPrior).1 ≤ last) (clean : ¬ (graph pp).Conflict last) :
    (messageDigest (hashAt pp last) pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg)
      sig.bottom.randomizer >>= codeword?) = some c.x := by
  obtain ⟨_,_,_,_,find,ext⟩ := c.lower
  exact (trial_of_find find).decoded (ext.trans later) clean

/-- Replay the complete upper finder at the root produced by the signed lower tree. -/
theorem Receipt.upper_digits {pp q idx msg sig} (c : Receipt pp q idx msg sig) {last}
    (later : (physical c.upperPrior).1 ≤ last) (clean : ¬ (graph pp).Conflict last) :
    (messageDigest (hashAt pp last) pp .top (UInt32.ofNat (bottomTree idx)) (packBytes c.root)
      sig.top.randomizer >>= codeword?) = some c.y := by
  obtain ⟨_,_,_,_,find,ext⟩ := c.upper
  exact (trial_of_find find).decoded (ext.trans later) clean

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
