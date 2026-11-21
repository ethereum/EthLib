module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerifiedLayerRows
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerificationTrials
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningComponents
public import EthLib.Cryptography.Proofs.Xmss.Encoding
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SigningRows
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.CanonicalPath
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.VerificationTrials

/-!
# Comparing a verified layer with a successful signing reply

The leanXMSS draft, section "WOTS+C", restricts accepted digit vectors to one fixed sum.

If a signing reply opened every candidate chain early enough, their digit vectors and digests agree.

Different message or randomizer bytes then give a collision between the two public message queries.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography Constants HashSig TwoLayerGraph VerifierProbe
open ChainGraph (Word digestEquiv)

/-- Two distinct byte strings at the same message address have the same low 128-bit response. -/
def SameKeyCollision (pp : PublicParam) (st : Honest.SharedState) (l : Layer) (e : Nat)
    (m n : ByteArray) (a b : LayerSignature) : Prop :=
  let left := (messageInput pp l e m a).data.toList
  let right := (messageInput pp l e n b).data.toList
  left ≠ right ∧ ∃ w : Word, st.1 (.inl left) = some w ∧ st.1 (.inl right) = some w

private theorem ordinary_digest (pp : PublicParam) (st : Honest.SharedState) (l : Layer)
    (e : Nat) (m : ByteArray) (sig : LayerSignature) (d : Digest)
    (read : messageDigest (hashAt pp st) pp l (UInt32.ofNat e) m sig.randomizer = some d) :
    st.1 (.inl (messageInput pp l e m sig).data.toList) = some (digestEquiv d) := by
  obtain ⟨word, raw, eqn⟩ := Option.bind_eq_some_iff.mp read
  have physical := low_of_hashAt _ _ _ _ raw
  rw [show halfOf 0 word = d from Option.some.inj eqn] at physical
  -- The message tag never encodes a chain, leaf or Merkle node.
  have ordinary := (graph pp).merge_apply_of_not_exists (st := st)
    (t := .inl (messageInput pp l e m sig).data.toList) (by
      rintro ⟨r | r, vs, _, eq⟩
      · exact input_ne pp l e m sig r vs (Sum.inl.inj eq)
      · cases eq)
  exact ordinary.symm.trans physical

/-- Compare the whole layer signature or exhibit two colliding queries at its key. -/
theorem compare_layer (pp : PublicParam) (st : Honest.SharedState) (privateTable : ResidualCache pp)
    (l : Layer) (e : Nat) (m n : ByteArray) (a b : LayerSignature)
    (x y : Vector (Fin CHAIN_LENGTH) V)
    (d d' : Digest)
    (left : messageDigest (hashAt pp st) pp l (UInt32.ofNat e) m a.randomizer = some d)
    (right : messageDigest (hashAt pp st) pp l (UInt32.ofNat e) n b.randomizer = some d')
    (candidate : codeword? d = some x) (signed : codeword? d' = some y)
    (earlier : ∀ i : Fin V, y[i] ≤ x[i])
    (values : ∀ i : Fin V, st.2 (inLayer l (LayerGraph.position (UInt32.ofNat e) i x[i].val)) =
      some (digestEquiv a.chainValues[i]))
    (path : ∀ k : Fin LAYER_HEIGHT, AtPosition st l ⟨k.val, (e / 2 ^ k.val) ^^^ 1⟩ a.path[k])
    (issued : LayerFact pp l e n b y privateTable st) :
    SameKeyCollision pp st l e m n a b ∨ (m = n ∧ a = b) := by
  have digits : x = y := by
    by_contra diff
    obtain ⟨i, less⟩ := (codeword_incomparable candidate signed diff).1
    exact Nat.not_lt_of_ge (earlier i) less
  subst y
  have sameDigest := eq_of_codeword candidate signed
  by_cases bytes : (messageInput pp l e m a).data.toList = (messageInput pp l e n b).data.toList
  · have payload := (thInput_inj (ByteArray.ext (Array.toList_inj.mp bytes))).2.2
    have size := congrArg ByteArray.size payload
    have len : m.size = n.size := by simpa using size
    obtain ⟨message, rand⟩ := byteArray_append_inj payload len
    have rho := EthLib.Base.packBytes_injective rand
    have chains : a.chainValues = b.chainValues := by
      apply Vector.ext
      intro i hi
      have same := (values ⟨i,hi⟩).symm.trans (issued.chains ⟨i,hi⟩)
      exact digestEquiv.injective (Option.some.inj same)
    have route : a.path = b.path := by
      apply Vector.ext
      intro k hk
      exact digestEquiv.injective (Option.some.inj ((path ⟨k,hk⟩).symm.trans (issued.route ⟨k,hk⟩)))
    refine Or.inr ⟨message, ?_⟩
    cases a
    cases b
    congr
  · refine Or.inl ⟨bytes, digestEquiv d, ordinary_digest pp st l e m a d left, ?_⟩
    rw [sameDigest]
    exact ordinary_digest pp st l e n b d' right

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
