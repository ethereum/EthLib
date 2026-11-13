/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.HypertreeConnection
public import EthereumXMSSHypertree.HypertreeQueryBudget
public import EthereumXMSSHypertree.AcceptedBridgeFacts
public import HashSig.GXMSS.Security.Hypertree.PRFDerivedUnforgeability

/-!
# Source strong-unforgeability bound for the concrete hypertree

The actual two-layer source family supplies accepted-digest injectivity, encoding observations
and paired-counter sampling laws to the native-hash security bound. Source-signature adversaries
use the existing epoch-guarded game transport and named query-budget-preserving lift.
The exported winning-mass bound uses the actual composite raw-key PRF and its named reduction.
Counter trials retain their strategy-dependent hash game.
-/

public section

open scoped ENNReal

open OracleComp OracleSpec
open EthereumXMSSHypertree EthLib.Cryptography.Xmss
open EthereumXMSSHypertree.ConcreteHypertree EthereumXMSSHypertree.HypertreeStrategies
open EthereumXMSSHypertree.HypertreePRF
open GXMSS.Hypertree.PRFDerived.Unforgeability

namespace EthereumXMSSHypertree.HypertreeSecurity

-- Keep accepted-output observations opaque during definitional comparison.
attribute [local irreducible] AcceptedBridgeFacts.accepts AcceptedBridgeFacts.truncatedWord

noncomputable local instance : DecidableEq EthereumXMSSHypertree.ConcreteHypertree.Input :=
  Classical.decEq _

noncomputable local instance : DecidableEq (GXMSS.Signature Randomizer Digest shape.h shape.v) :=
  Classical.decEq _

noncomputable local instance : DecidableEq EthereumXMSSHypertree.HypertreePRF.Query :=
  Classical.decEq _

/-- The source half projections supply all four actual paired-counter sampling laws. -/
theorem samplingLaws (H : Pure.Hash) :
    SamplingLaws (hashInstance H ($ᵗ PublicParam)) .pairedCounter sourceRetrySampling
      sourceInterpretation sourceRetryInterpretation where
  publicParameter := sourceInterpretation_half_uniform
  starts := sourceInterpretation_jointPair
  bottomCoins := by
    change ((fun responses : Unit → FullResponse => halfOf 0 (responses ())) <$>
      ((fun (response : FullResponse) (_ : Unit) => response) <$> ($ᵗ FullResponse))) =ᵈ
        ($ᵗ Randomizer)
    rw [Functor.map_map]
    exact sourceInterpretation_half_uniform
  internalCoins := by
    change ((fun responses : Unit → FullResponse => halfOf 0 (responses ())) <$>
      ((fun (response : FullResponse) (_ : Unit) => response) <$> ($ᵗ FullResponse))) =ᵈ
        ($ᵗ Randomizer)
    rw [Functor.map_map]
    exact sourceInterpretation_half_uniform

/-- The full source message hash and its accepted-word observation at complete coordinates. -/
def encodingHash (H : Pure.Hash) :
    GXMSS.Hypertree.Security.FamilyEncodingAcceptedOutput.HashFamily
      PublicParam Message Digest Randomizer Digest shape where
  eval pp q r := (messageDigest (pureHash H) pp (sourceLayer q.1.1)
    (sourceKey q.1) (sourceMessageBytes q.1 q.2) r).run
  accepts _ := AcceptedBridgeFacts.accepts
  word _ := AcceptedBridgeFacts.truncatedWord

/-- Source decoding is injective separately on the accepted full digests at each coordinate. -/
theorem encodingHash_injOn (H : Pure.Hash) (p : GXMSS.Hypertree.OTSPosition shape) :
    Set.InjOn ((encodingHash H).word p) {y | (encodingHash H).accepts p y = true} := by
  dsimp only [encodingHash]
  exact AcceptedBridgeFacts.truncatedWord_injOn

/-- The source family retains the complete optional accepted-digest encoding observation. -/
theorem encodingHash_value (H : Pure.Hash) (pp : PublicParam)
    (q : GXMSS.Hypertree.Security.FamilyEncoding.Query Message Digest shape) (r : Randomizer) :
    (sourceEncodingFamily H).value q.1 pp q.2 r =
    if (encodingHash H).accepts q.1 ((encodingHash H).eval pp q r) then
      some ((encodingHash H).word q.1 ((encodingHash H).eval pp q r)) else none := by
  dsimp only [encodingHash]
  have hsource := @AcceptedBridgeFacts.sourceEncoding_value_eq_if_accepts
    (GXMSS.Hypertree.Message shape Message Digest q.1) H (sourceLayer q.1.1)
    (sourceMessageBytes q.1) pp q.2 r (sourceKey q.1)
  dsimp only [] at hsource
  have hfamily := sourceEncodingFamily_value H q.1 pp q.2 r
  exact hfamily.trans hsource

/-- The two explicit source codewords imply the required fibrewise nonmaximum-output property. -/
theorem noMaximumOutput (H : Pure.Hash) : (sourceEncodingFamily H).NoMaximumOutput := by
  apply GXMSS.Encoding.Family.noMaximumOutput_of_two_codewords
  intro p
  exact GenericEncoding.two_codewords

/-- The actual named source-adversary lift preserves its signing-request bound. -/
theorem lifted_source_query_bound
    (adv : SyncSignatureUnforgeability.Adversary unifSpec PublicKey Epoch Message Signature)
    (qs : Nat) (hqueries : ∀ pk,
      (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs)
    (pk : HypertreeGameTransport.GenericPublicKey) :
    ((HypertreeGameTransport.liftedAdversary adv).forge pk).IsQueryBoundP
      (fun q => q.isRight = true) qs :=
  HypertreeQueryBudget.liftedAdversary_query_bound adv (fun q => q.isRight = true) qs hqueries pk

/-- Source adversaries retain the complete source signature and finite epoch domain. -/
abbrev SourceAdversary :=
  SyncSignatureUnforgeability.Adversary unifSpec PublicKey Epoch Message Signature

/-- The actual named eager PRF reduction applied to the source-signature adversary lift. -/
@[expose] noncomputable def sourcePRFReduction (H : Pure.Hash) (adv : SourceAdversary) :
    OracleComp (PRFScheme.PRFOracleSpec Query FullResponse) Bool :=
  randgenPRFReduction (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H)
    .pairedCounter sourceRetrySampling sourceInterpretation sourceRetryInterpretation
    (HypertreeGameTransport.liftedAdversary adv)

/-- The paired full-response layout requests 29 groups for each source 58-chain key. -/
theorem sourcePRFReduction_query_budget (qs : Nat) :
    eagerQueryBound shape .pairedCounter sourceRetrySampling qs =
      1 + GXMSS.Hypertree.otsCount shape * 29 + GXMSS.Hypertree.upperCount shape + qs :=
  eagerQueryBound_pairedCounter shape sourceRetrySampling qs

/-- The source reduction counts one setup response, paired starts, fixed bases and fresh bases. -/
theorem sourcePRFReduction_query_bound (H : Pure.Hash) (adv : SourceAdversary) (qs : Nat)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    (sourcePRFReduction H adv).IsQueryBoundP (fun q => q.isRight = true)
      (1 + GXMSS.Hypertree.otsCount shape * 29 + GXMSS.Hypertree.upperCount shape + qs) := by
  rw [← sourcePRFReduction_query_budget qs]
  exact randgenPRFReduction_query_bound (hashInstance H ($ᵗ PublicParam))
    (sourceEncodingFamily H) .pairedCounter sourceRetrySampling sourceInterpretation
    sourceRetryInterpretation qs (HypertreeGameTransport.liftedAdversary adv)
    (lifted_source_query_bound adv qs hqueries)

/-- The exact generic accepted-hash bound at the actual source parameters and adversary lift. -/
@[expose] noncomputable def sourceSecurityBound (H : Pure.Hash) (qs : Nat)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  hashEncodingStrongUnforgeabilityBound
    (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) .pairedCounter sourceRetrySampling
    sourceInterpretation sourceRetryInterpretation (sourcePRF H) qs
    GenericEncoding.positive_parameters.1 GenericEncoding.positive_parameters.2
    (encodingHash H) (encodingHash_injOn H) (encodingHash_value H)
    (HypertreeGameTransport.liftedAdversary adv)

/-- The single composite raw-key PRF advantage for the actual named eager reduction. -/
@[expose] noncomputable def sourcePRFAdvantage (H : Pure.Hash) (adv : SourceAdversary) : ℝ≥0∞ :=
  (sourcePRF H).prfAdvantage (sourcePRFReduction H adv)

/-- The global Merkle target-collision term. -/
@[expose] noncomputable def sourceMerkleCollisionAdvantage (H : Pure.Hash)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_Advantage (GXMSS.Hypertree.Unforgeability.merkleTargetCollisionReduction
      (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling
      (HypertreeGameTransport.liftedAdversary adv))

/-- The global same-message chain target-collision term. -/
@[expose] noncomputable def sourceSameMessageChainCollisionAdvantage (H : Pure.Hash)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_Advantage
    (GXMSS.Hypertree.Unforgeability.sameMessageChainTargetCollisionReduction
      (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling
      (HypertreeGameTransport.liftedAdversary adv))

/-- The global chain-cut target-collision term. -/
@[expose] noncomputable def sourceChainCutCollisionAdvantage (H : Pure.Hash)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  TweakableHash.SM_DT_TCR_Advantage
    (GXMSS.Hypertree.Unforgeability.chainCutTargetCollisionReduction
      (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling
      (HypertreeGameTransport.liftedAdversary adv))

/-- The global selected-chain preimage term before its chain-count coefficient. -/
@[expose] noncomputable def sourceChainPreimageAdvantage (H : Pure.Hash)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  TweakableHash.SM_DT_PRE_Advantage (GXMSS.Hypertree.Security.chainPreimageReduction
    (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling
    GenericEncoding.positive_parameters.1 GenericEncoding.positive_parameters.2
    (HypertreeGameTransport.liftedAdversary adv))

/-- The global chain-undetectability term before its chain and positive-cut coefficients. -/
@[expose] noncomputable def sourceChainUndetectabilityAdvantage (H : Pure.Hash)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  TweakableHash.SM_DT_UD_Advantage (GXMSS.Hypertree.Security.chainUndetectabilityReduction
    (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling
    GenericEncoding.positive_parameters.1 GenericEncoding.positive_parameters.2
    (HypertreeGameTransport.liftedAdversary adv)
    (GXMSS.Hypertree.Security.selectedCutObservation
      (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H)))

/-- The accepted-output counter-hash term uses the correlated single-base retry strategy. -/
@[expose] noncomputable def sourceCounterHashAdvantage (H : Pure.Hash) (qs : Nat)
    (adv : SourceAdversary) : ℝ≥0∞ :=
  GXMSS.Hypertree.Security.FamilyEncodingAcceptedOutput.advantage
    ((GXMSS.Hypertree.Unforgeability.encodingHashBridge
      (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling qs
      (encodingHash H) (encodingHash_injOn H) (encodingHash_value H)).reduction
        (GXMSS.Hypertree.Security.encodingTargetCollisionReduction
          (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) sourceRetrySampling qs
          (HypertreeGameTransport.liftedAdversary adv)))

/-- The source bound has one PRF term and six global primitive terms with exact coefficients. -/
theorem sourceSecurityBound_eq_expanded (H : Pure.Hash) (qs : Nat) (adv : SourceAdversary) :
    sourceSecurityBound H qs adv = sourcePRFAdvantage H adv +
      (sourceMerkleCollisionAdvantage H adv + sourceCounterHashAdvantage H qs adv +
        sourceSameMessageChainCollisionAdvantage H adv + sourceChainCutCollisionAdvantage H adv +
        (GXMSS.Hypertree.chainCount shape : ℝ≥0∞) * sourceChainPreimageAdvantage H adv +
        (GXMSS.Hypertree.chainCount shape : ℝ≥0∞) * ((2 ^ shape.w - 1 : Nat) : ℝ≥0∞) *
          sourceChainUndetectabilityAdvantage H adv) := rfl

/-- Source strong winning mass is bounded by the actual PRF and accepted-output hash reductions.
The signing-request budget transfers through the named lift without overhead. -/
theorem _root_.EthereumXMSSHypertree.sourceStrongGame_reduction_bound (H : Pure.Hash)
    (qs : Nat) (adv : SourceAdversary)
    (hqueries : ∀ pk, (adv.forge pk).IsQueryBoundP (fun q => q.isRight = true) qs) :
    sourceStrongGame H adv {true} ≤
      hashEncodingStrongUnforgeabilityBound
        (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H)
        .pairedCounter sourceRetrySampling
        sourceInterpretation sourceRetryInterpretation (sourcePRF H) qs
        GenericEncoding.positive_parameters.1 GenericEncoding.positive_parameters.2
        (encodingHash H) (encodingHash_injOn H) (encodingHash_value H)
        (HypertreeGameTransport.liftedAdversary adv) := by
  have hbound := strong_unforgeability_reduction_bound_hashEncoding
    (hashInstance H ($ᵗ PublicParam)) (sourceEncodingFamily H) .pairedCounter sourceRetrySampling
    sourceInterpretation sourceRetryInterpretation (samplingLaws H) (sourcePRF H) qs
    GenericEncoding.positive_parameters.1 GenericEncoding.positive_parameters.2
    (noMaximumOutput H) (encodingHash H) (encodingHash_injOn H) (encodingHash_value H)
    (HypertreeGameTransport.liftedAdversary adv) (lifted_source_query_bound adv qs hqueries)
  exact (sourceStrongGame_le_generic H ($ᵗ PublicParam) adv).trans hbound

end EthereumXMSSHypertree.HypertreeSecurity
