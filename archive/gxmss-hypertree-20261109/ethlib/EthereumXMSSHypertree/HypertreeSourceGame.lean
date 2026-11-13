/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.SourceGame
public import EthereumXMSSHypertree.HypertreeRepresentation
public import EthereumXMSSHypertree.HypertreePRF
public import EthereumXMSSHypertree.HypertreeHash
public import EthereumXMSSHypertree.HypertreeCorrespondence

/-!
# A source-signature wrapper around the reviewed derived hypertree

The public and secret key fields use the exact source representations. Signing reconstructs the
embedded index from the requested epoch. Verification rejects an index mismatch before applying
the actual generic verifier. This is a deterministic-hash first-request interface.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss ConcreteHypertree HypertreeStrategies HypertreePRF

/-- The actual reviewed paired-counter scheme with one uniform raw source seed. -/
@[expose] def concreteHypertreeScheme (H : Pure.Hash) (seedGen : ProbComp PublicParam) :=
  GXMSS.Hypertree.PRFDerived.scheme (hashInstance H seedGen) (sourceEncodingFamily H)
    .pairedCounter sourceRetrySampling (sourcePRF H) sourceInterpretation sourceRetryInterpretation

/-- The actual generic algorithms expressed with complete source keys and signatures. -/
@[expose] def hypertreeSourceScheme (H : Pure.Hash) (seedGen : ProbComp PublicParam) :
    SyncSignatureAlg ProbComp Message PublicKey SecretKey Signature Epoch where
  keygen := (fun keys => (publicKeyToSource keys.1, (⟨keys.2⟩ : SecretKey))) <$>
    (concreteHypertreeScheme H seedGen).keygen
  sign sk ep msg := (Option.map (signatureToSource ep)) <$>
    (concreteHypertreeScheme H seedGen).sign sk.seed ep msg
  verify pk ep msg sig := if leafIndexEquiv sig.leafIndex = ep then
    (concreteHypertreeScheme H seedGen).verify (publicKeyToGeneric pk) ep msg
      (signatureToGeneric sig) else false

/-- Actual source key generation gives the reviewed derived public key and unchanged raw S0. -/
theorem source_keygen_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) (raw : Seed) :
    GXMSS.Hypertree.PRFDerived.keys (hashInstance H seedGen) .pairedCounter
      sourceRetrySampling (sourceEvaluator H) sourceInterpretation sourceRetryInterpretation raw =
      (publicKeyToGeneric ((keyGenWith (pureHash H) raw).run).2, raw) := by
  rw [keyGenWith_run]
  exact HypertreeCorrespondence.source_keygen_eq H seedGen raw

/-- The concrete generic wrapper samples exactly the source public and secret key distribution. -/
theorem hypertreeSourceScheme_keygen_eq (H : Pure.Hash) (seedGen : ProbComp PublicParam) :
    (hypertreeSourceScheme H seedGen).keygen = (sourceScheme H).keygen := by
  rw [sourceScheme_eq_pureScheme]
  change (fun keys => (publicKeyToSource keys.1, (⟨keys.2⟩ : SecretKey))) <$>
      (GXMSS.Hypertree.PRFDerived.keys (hashInstance H seedGen) .pairedCounter
        sourceRetrySampling (sourceEvaluator H) sourceInterpretation sourceRetryInterpretation <$>
          ($ᵗ Seed : ProbComp Seed)) = _
  rw [Functor.map_map]
  have hfun : (fun raw =>
      (publicKeyToSource (GXMSS.Hypertree.PRFDerived.keys (hashInstance H seedGen) .pairedCounter
        sourceRetrySampling (sourceEvaluator H) sourceInterpretation
        sourceRetryInterpretation raw).1,
       (⟨(GXMSS.Hypertree.PRFDerived.keys (hashInstance H seedGen) .pairedCounter
        sourceRetrySampling (sourceEvaluator H) sourceInterpretation
        sourceRetryInterpretation raw).2⟩ :
          SecretKey))) = fun raw => ((Pure.keys H raw).2, (Pure.keys H raw).1) := by
    funext raw
    rw [HypertreeCorrespondence.source_keygen_eq]
    rfl
  change _ <$> ($ᵗ Seed : ProbComp Seed) = _
  rw [hfun]
  simp only [pureScheme, bind_pure_comp]

/-- A source signature's embedded index cannot be relabelled by the generic wrapper. -/
theorem hypertreeSourceScheme_verify_mismatch (H : Pure.Hash) (seedGen : ProbComp PublicParam)
    (pk : PublicKey) (ep : Epoch) (msg : Message) (sig : Signature)
    (h : leafIndexEquiv sig.leafIndex ≠ ep) :
    (hypertreeSourceScheme H seedGen).verify pk ep msg sig = false := by
  simp [hypertreeSourceScheme, h]

/-- Reconstructing a returned pure source signature preserves success, failure and every field. -/
theorem source_sign_reconstruction (H : Pure.Hash) (sk : SecretKey) (ep : Epoch) (msg : Message) :
    ((Pure.sign H sk (leafIndexEquiv.symm ep) msg).map signatureToGeneric).map
      (signatureToSource ep) = Pure.sign H sk (leafIndexEquiv.symm ep) msg := by
  cases hs : Pure.sign H sk (leafIndexEquiv.symm ep) msg with
  | none => rfl
  | some sig =>
    have hi := Pure.sign_leafIndex H sk (leafIndexEquiv.symm ep) msg hs
    have hc : leafIndexEquiv sig.leafIndex = ep := by simp [hi]
    simpa only [Option.map_some] using
      congrArg some (signatureToSource_signatureToGeneric ep sig hc)

/-- The exact Boolean measure of the complete first-request generic wrapper. -/
@[expose] noncomputable def hypertreeSourceStrongGame (H : Pure.Hash)
    (seedGen : ProbComp PublicParam)
    (adv : SyncSignatureUnforgeability.Adversary unifSpec PublicKey Epoch Message Signature) :
    MeasureTheory.Measure Bool :=
  SyncSignatureUnforgeability.strongUnforgeableExp (hypertreeSourceScheme H seedGen)
    ProbCompRuntime.probComp adv

end EthereumXMSSHypertree
