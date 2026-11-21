module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticePost
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ForgeryCollision
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerComparison
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ForgeryCollision
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainGraphWalk

/-!
# First physical observations of the two colliding message words

The candidate and the signer use distinct public inputs at the same key.

Their 256-bit answers can differ in the high half.

The common low half decodes to the digits actually selected by the signer.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph Honest
open CachedCodeword PostSigning TrialGraphWatch VerifierProbe
open ChainGraph (digestEquiv)

@[expose] def FirstPair (pp : PublicParam) (s : JointState × List Arrival)
    (l : Layer) (e : UInt32) (m n : ByteArray) (a b : LayerSignature)
    (y : Vector (Fin CHAIN_LENGTH) V) : Prop :=
  let left := trialInput pp l e m a.randomizer
  let right := trialInput pp l e n b.randomizer
  left ≠ right ∧ ∃ w u first sign,
    Arrival.word left w first ∈ s.2 ∧ Arrival.word right u sign ∈ s.2 ∧
    cold pp left first.1.1.1.1.1 = true ∧ cold pp right sign.1.1.1.1.1 = true ∧
    codeword? (selectedDigest y) = some y ∧
    halfOf 0 (ofOutput w) = selectedDigest y ∧ halfOf 0 (ofOutput u) = selectedDigest y ∧
    (s.1.2 = true ∨ first.1.1.1.1.2 (l,e) ≠ some (selectedDigest y))

private theorem pair_at {pp : PublicParam} {state : JointState × List Arrival}
    {r : ResidualCache pp} {last : SharedState} (origin : Origin pp state)
      (post : SeenPost pp state)
    (fill : last ∈ support (RelabelState.endFill state.1.1.1.1.1.1))
    (clean : ¬ (graph pp).Conflict last) (l : Layer) (e : Nat) (m n : ByteArray)
    (a b : LayerSignature) (y : Vector (Fin CHAIN_LENGTH) V) (fact : LayerFact pp l e n b y r last)
    (collision : SameKeyCollision pp last l e m n a b) : FirstPair pp state l
      (UInt32.ofNat e) m n a b y := by
  obtain ⟨d,read,encoded⟩ := Option.bind_eq_some_iff.mp (fact.decoded clean)
  obtain ⟨distinct,v,rowL,rowR⟩ := collision
  have genuine := ordinary_digest pp last l e n b d read
  obtain rfl := Option.some.inj (rowR.symm.trans genuine)
  obtain ⟨w,first,firstLog,coldA,loA,_⟩ := origin.filled_low _ ⟨l,_,m,a.randomizer,rfl⟩ fill rowL
  obtain ⟨u,sign,signLog,coldB,loB,_⟩ := origin.filled_low _ ⟨l,_,n,b.randomizer,rfl⟩ fill rowR
  have low {w : HashOutput} (h : (PairedHashWord.halves w).1 = digestEquiv d) :
      halfOf 0 (ofOutput w) = selectedDigest y := by
    rw [PairedHashWord.first_half_bytes, h, selectedDigest_eq encoded]
    exact digestEquiv.symm_apply_apply d
  refine ⟨distinct,w,u,first,sign,firstLog,signLog,coldA,coldB,
    by rwa [selectedDigest_eq encoded],low loA,low loB,?_⟩
  by_cases same : first.1.1.1.1.2 (l,UInt32.ofNat e) = some (selectedDigest y)
  · left
    apply post (trialInput pp l (UInt32.ofNat e) m a.randomizer) w first firstLog coldA
    simp only [target, messageKey_trial, Option.bind_some, same, low loA]
  · exact Or.inr same

/-- The signed and candidate message rows supply both first observations. -/
theorem collision_arrivals {pp : PublicParam} {state : JointState × List Arrival}
    {r : ResidualCache pp} {last : SharedState} {obs : Outcome}
    (origin : Origin pp state) (post : SeenPost pp state)
    (fill : last ∈ support (RelabelState.endFill state.1.1.1.1.1.1))
    (clean : ¬ (graph pp).Conflict last) (facts : LogFacts pp obs.log r last)
    (collision : SignedCollision pp last obs) :
    let sig := obs.candidate.signature
    ∃ req issued, (req,.ok issued) ∈ obs.log ∧
      ((req.leafIndex = sig.leafIndex ∧ ∃ x,
        FirstPair pp state .bottom (UInt32.ofNat sig.leafIndex.toNat)
          (packBytes obs.candidate.message) (packBytes req.message) sig.bottom issued.bottom x) ∨
       (bottomTree req.leafIndex = bottomTree sig.leafIndex ∧ ∃ candidateRoot signedRoot y,
         layerRoot (hashAt pp last) pp .bottom sig.leafIndex.toNat (packBytes obs.candidate.message)
           sig.bottom = some (some candidateRoot) ∧
         last.2 (.inr (.inl (.bottom,LayerGraph.treeRole LAYER_HEIGHT
           (bottomTree sig.leafIndex)))) =
           some (digestEquiv signedRoot) ∧
         FirstPair pp state .top (UInt32.ofNat (bottomTree sig.leafIndex)) (packBytes candidateRoot)
           (packBytes signedRoot) sig.top issued.top y)) := by
  obtain ⟨req,issued,member,cases⟩ := collision
  obtain ⟨_,root,x,y,row,lower,upper⟩ := facts req issued member
  refine ⟨req,issued,member,?_⟩
  rcases cases with ⟨idx,matchBottom⟩ | ⟨idx,candidate,signedRoot,actual,stored,matchTop⟩
  · rw [idx] at lower
    exact Or.inl ⟨idx,x,pair_at origin post fill clean _ _ _ _ _ _ x lower matchBottom⟩
  · rw [idx] at row upper
    obtain rfl := digestEquiv.injective (Option.some.inj (row.symm.trans stored))
    exact Or.inr ⟨idx,candidate,root,y,actual,row,pair_at origin post fill clean
      _ _ _ _ _ _ y upper matchTop⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
