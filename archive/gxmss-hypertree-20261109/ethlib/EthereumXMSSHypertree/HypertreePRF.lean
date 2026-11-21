/- Authors: Matthias Meijers -/

module

public import EthereumXMSSHypertree.HypertreeStrategies
public import EthereumXMSSHypertree.Functional
public import HashSig.GXMSS.Hypertree.PRFDerivedScheme

/-!
# Source interpretation of the reviewed paired-counter derivation layout

The actual generic query domain has one request per paired start and one base
request per complete coordinate/message. Its concrete map uses the legal source
query domain and the original raw seed as the single composite-evaluator key.
-/

public section

namespace EthereumXMSSHypertree.HypertreePRF

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open ConcreteHypertree HypertreeStrategies OracleComp OracleSpec

/-- The reviewed actual request domain with the source's paired starts and counter bases. -/
abbrev Query := GXMSS.Hypertree.PRFDerived.Query PublicParam Message Digest shape .pairedCounter
  (GXMSS.Hypertree.PRFDerived.retryBudget sourceRetrySampling)

/-- Map the actual generic request families to their unique legal source requests. -/
@[expose]
def sourceQueryMap : Query → SourceQuery
  | .publicSeed => .publicParameter
  | .start pp position pair =>
      .start pp (sourceLayer position.1) (sourceKeyCoordinate position)
        ⟨pair.val, by simp [shape, V]⟩
  | .retry pp position message _ =>
      .retryBase pp (sourceLayer position.1) (sourceKeyCoordinate position)
        (messageToSource position message)

private theorem sourceQueryMap_start_eq (pp otherPP : PublicParam)
    (position otherPosition : GXMSS.Hypertree.OTSPosition shape)
    (pair otherPair : GXMSS.Hypertree.PRFDerived.StartIndex shape .pairedCounter)
    (h : sourceQueryMap (.start pp position pair) =
      sourceQueryMap (.start otherPP otherPosition otherPair)) :
    (GXMSS.Hypertree.PRFDerived.Query.start pp position pair : Query) =
      .start otherPP otherPosition otherPair := by
  have hactual := congrArg sourceQueryToDerivation h
  have hpp : pp = otherPP := congrArg DerivationQuery.publicParam hactual
  have haddress : addrPrf (sourceLayer position.1) (sourceKey position) pair =
      addrPrf (sourceLayer otherPosition.1) (sourceKey otherPosition) otherPair :=
    congrArg DerivationQuery.address hactual
  obtain ⟨hlayer, hkey, hpair⟩ := addrPrf_inj.mp haddress
  have hposition := sourceKey_injective hlayer hkey
  subst otherPP otherPosition
  have hp : pair = otherPair := Fin.ext (congrArg Fin.val hpair)
  subst otherPair
  rfl

private theorem sourceQueryMap_retry_eq (pp otherPP : PublicParam)
    (position otherPosition : GXMSS.Hypertree.OTSPosition shape)
    (message : GXMSS.Hypertree.Message shape Message Digest position)
    (otherMessage : GXMSS.Hypertree.Message shape Message Digest otherPosition)
    (index : GXMSS.Hypertree.PRFDerived.RetryIndex .pairedCounter
      (GXMSS.Hypertree.PRFDerived.retryBudget sourceRetrySampling position))
    (otherIndex : GXMSS.Hypertree.PRFDerived.RetryIndex .pairedCounter
      (GXMSS.Hypertree.PRFDerived.retryBudget sourceRetrySampling otherPosition))
    (h : sourceQueryMap (.retry pp position message index) =
      sourceQueryMap (.retry otherPP otherPosition otherMessage otherIndex)) :
    (GXMSS.Hypertree.PRFDerived.Query.retry pp position message index : Query) =
      .retry otherPP otherPosition otherMessage otherIndex := by
  have hactual := congrArg sourceQueryToDerivation h
  have hpp : pp = otherPP := congrArg DerivationQuery.publicParam hactual
  have haddress : addrRnd (sourceLayer position.1) (sourceKey position) =
      addrRnd (sourceLayer otherPosition.1) (sourceKey otherPosition) :=
    congrArg DerivationQuery.address hactual
  obtain ⟨hlayer, hkey⟩ := addrRnd_inj.mp haddress
  have hposition := sourceKey_injective hlayer hkey
  subst otherPP otherPosition
  have hmessage := sourceMessageBytes_injective position (congrArg DerivationQuery.suffix hactual)
  subst otherMessage
  cases index
  cases otherIndex
  rfl

/-- The paired-counter map aliases no distinct full-response request coordinates. -/
theorem sourceQueryMap_injective : Function.Injective sourceQueryMap := by
  intro first second h
  cases first with
  | publicSeed =>
    cases second with
    | publicSeed => rfl
    | start pp position pair => simp only [sourceQueryMap] at h; cases h
    | retry pp position message index => simp only [sourceQueryMap] at h; cases h
  | start pp position pair =>
    cases second with
    | publicSeed => simp only [sourceQueryMap] at h; cases h
    | start otherPP otherPosition otherPair =>
      exact sourceQueryMap_start_eq pp otherPP position otherPosition pair otherPair h
    | retry otherPP otherPosition message index => simp only [sourceQueryMap] at h; cases h
  | retry pp position message index =>
    cases second with
    | publicSeed => simp only [sourceQueryMap] at h; cases h
    | start otherPP otherPosition pair => simp only [sourceQueryMap] at h; cases h
    | retry otherPP otherPosition otherMessage otherIndex =>
      exact sourceQueryMap_retry_eq pp otherPP position otherPosition message otherMessage
        index otherIndex h

/-- Insert a fixed source scheme seed into a reviewed paired-counter query. -/
@[expose]
def queryInput (seed : Seed) (query : Query) : ByteArray :=
  sourceQueryInput seed (sourceQueryMap query)

/-- The reviewed paired-counter inputs remain globally injective after source byte encoding. -/
theorem queryInput_injective (seed : Seed) : Function.Injective (queryInput seed) :=
  (sourceQueryInput_injective seed).comp sourceQueryMap_injective

/-- Interpret every complete response using the source's exact half projections. -/
@[expose]
def sourceInterpretation :
    GXMSS.Hypertree.PRFDerived.Interpretation PublicParam Digest Randomizer FullResponse where
  publicParameter := halfOf 0
  chainStart := halfOf 0
  chainPair := splitResponse
  retryRandomizer := halfOf 0

/-- Decode one base response for each bottom request and each fixed internal certificate. -/
@[expose]
def sourceRetryInterpretation :
    GXMSS.Hypertree.PRFDerived.RetryInterpretation .pairedCounter sourceRetrySampling
      FullResponse where
  bottomCoins responses := halfOf 0 (responses ())
  internalCoins responses := halfOf 0 (responses ())

/-- Both source halves jointly have the actual interpretation's independent digest law. -/
theorem sourceInterpretation_jointPair :
    sourceInterpretation.chainPair <$> ($ᵗ FullResponse : ProbComp FullResponse) =ᵈ
      (do let first ← $ᵗ Digest; let second ← $ᵗ Digest; pure (first, second)) :=
  splitResponse_uniform

/-- The first-half projection supplies the uniform public parameter and counter-base laws. -/
theorem sourceInterpretation_half_uniform :
    halfOf 0 <$> ($ᵗ FullResponse : ProbComp FullResponse) =ᵈ ($ᵗ Digest) := by
  have hpair := SampleableType.map_uniformSample_evalDistEq_of_bijective
    splitResponseEquiv.bijective
  have hfirst := hpair.map (Prod.fst : Digest × Digest → Digest)
  have hprojection : halfOf 0 <$> ($ᵗ FullResponse : ProbComp FullResponse) =ᵈ
      Prod.fst <$> ($ᵗ (Digest × Digest) : ProbComp (Digest × Digest)) := by
    rw [Functor.map_map] at hfirst
    change halfOf 0 <$> ($ᵗ FullResponse : ProbComp FullResponse) =ᵈ
      Prod.fst <$> ($ᵗ (Digest × Digest) : ProbComp (Digest × Digest)) at hfirst
    exact hfirst
  refine hprojection.trans ?_
  apply EvalDistEq.of_forall_prEvent_eq
  intro event
  rw [prEvent_map]
  exact SampleableType.prEvent_uniformSample_fst event

/-- The single raw-key evaluator composes scheme-seed derivation and the actual query map. -/
@[expose]
def sourceEvaluator (hash : ByteArray → FullResponse) (raw : Seed) (query : Query) : FullResponse :=
  (typedSourcePRF hash).eval raw (sourceQueryMap query)

/-- One raw-seed PRF supplies the entire reviewed paired-counter forest. -/
@[expose]
def sourcePRF (hash : ByteArray → FullResponse) : PRFScheme Seed Query FullResponse where
  keygen := (typedSourcePRF hash).keygen
  eval := sourceEvaluator hash

/-- Only the original 32-byte source seed is sampled uniformly. -/
theorem sourcePRF_uniformKey (hash : ByteArray → FullResponse) : (sourcePRF hash).UniformKey := rfl

/-- Evaluation retains the actual composite source hashing operation at every query. -/
theorem sourceEvaluator_eq (hash : ByteArray → FullResponse) (raw : Seed) (query : Query) :
    sourceEvaluator hash raw query =
      hash (queryInput ((schemeSeed (pureHash hash) raw).run) query) := rfl

/-- The shared distinguished response derives the exact source public parameter. -/
theorem publicSeed_eq_source (hash : ByteArray → FullResponse) (raw : Seed) :
    GXMSS.Hypertree.PRFDerived.publicSeed (sourceEvaluator hash) sourceInterpretation raw =
      (publicParamOf (seedPrf (pureHash hash) ((schemeSeed (pureHash hash) raw).run))).run := rfl

/-- The shared distinguished response is the pure source public-parameter derivation. -/
theorem publicSeed_eq_pure (hash : ByteArray → FullResponse) (raw : Seed) :
    GXMSS.Hypertree.PRFDerived.publicSeed (sourceEvaluator hash) sourceInterpretation raw =
      Pure.publicParam (Pure.derivedResponse hash (Pure.schemeSeed hash raw)) := rfl

/-- A counter request projects exactly the source base at its complete coordinate and message. -/
theorem retryBase_eq_source (hash : ByteArray → FullResponse) (raw : Seed) (pp : PublicParam)
    (position : GXMSS.Hypertree.OTSPosition shape)
    (message : GXMSS.Hypertree.Message shape Message Digest position) :
    sourceInterpretation.retryRandomizer
      (sourceEvaluator hash raw (.retry pp position message ())) =
      Pure.randomizerBase pp (Pure.derivedResponse hash (Pure.schemeSeed hash raw))
        (sourceLayer position.1) (sourceKey position) (sourceMessageBytes position message) := rfl

/-- Fixed internal retry coins derive from the exact fixed 16-byte child-root message. -/
theorem internalCoins_eq_source (hash : ByteArray → FullResponse) (raw : Seed) (pp : PublicParam)
    (position : GXMSS.Hypertree.UpperPosition shape) (root : Digest) :
    sourceRetryInterpretation.internalCoins (fun index => sourceEvaluator hash raw
      (.retry pp position.val (GXMSS.Hypertree.internalMessage position root)
        (GXMSS.Hypertree.PRFDerived.internalRetryIndex .pairedCounter sourceRetrySampling
          position index))) =
      Pure.randomizerBase pp (Pure.derivedResponse hash (Pure.schemeSeed hash raw))
        (sourceLayer position.val.1) (sourceKey position.val) (packBytes root) := by
  have hi : GXMSS.Hypertree.PRFDerived.internalRetryIndex .pairedCounter sourceRetrySampling
      position () = () := Subsingleton.elim _ _
  change sourceInterpretation.retryRandomizer (sourceEvaluator hash raw
    (.retry pp position.val (GXMSS.Hypertree.internalMessage position root)
      (GXMSS.Hypertree.PRFDerived.internalRetryIndex .pairedCounter sourceRetrySampling
        position ()))) = _
  rw [hi, retryBase_eq_source, sourceMessageBytes_internal]

/-- The actual paired-layout start projection equals every deterministic source chain start. -/
theorem starts_eq_source (hash : ByteArray → FullResponse) (raw : Seed) (pp : PublicParam)
    (position : GXMSS.Hypertree.OTSPosition shape) (index : Fin shape.v) :
    GXMSS.Hypertree.PRFDerived.starts .pairedCounter
        (GXMSS.Hypertree.PRFDerived.retryBudget sourceRetrySampling)
        (sourceEvaluator hash) sourceInterpretation raw pp position index =
      (Pure.starts pp (Pure.derivedResponse hash (Pure.schemeSeed hash raw))
        (sourceLayer position.1) (sourceKey position))[index.val] := by
  have hmod : index.val % 2 = 0 ∨ index.val % 2 = 1 := by omega
  rcases hmod with hzero | hone
  · simp [GXMSS.Hypertree.PRFDerived.starts, GXMSS.Hypertree.PRFDerived.startHalf,
      GXMSS.Hypertree.PRFDerived.startGroup, sourceInterpretation, sourceEvaluator,
      sourceQueryMap, sourceQueryToDerivation, typedSourcePRF, rawSeedPRF, seedPrf,
      sourceKeyCoordinate, sourceKey, Pure.starts, Pure.derivedResponse, Pure.schemeSeed,
      schemeSeed, pureHash, Id.run_pure, hzero,
      splitResponse]
    rfl
  · simp [GXMSS.Hypertree.PRFDerived.starts, GXMSS.Hypertree.PRFDerived.startHalf,
      GXMSS.Hypertree.PRFDerived.startGroup, sourceInterpretation, sourceEvaluator,
      sourceQueryMap, sourceQueryToDerivation, typedSourcePRF, rawSeedPRF, seedPrf,
      sourceKeyCoordinate, sourceKey, Pure.starts, Pure.derivedResponse, Pure.schemeSeed,
      schemeSeed, pureHash, Id.run_pure, hone,
      splitResponse]
    rfl

end EthereumXMSSHypertree.HypertreePRF
