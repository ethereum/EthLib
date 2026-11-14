/- Authors: Matthias Meijers -/

module

public import EthereumXMSSHypertree.HypertreeCoordinates
public import EthereumXMSSHypertree.GenericEncoding
public import EthereumXMSSHypertree.TypedDerivation
public import EthereumXMSSHypertree.Retry
public import HashSig.GXMSS.Hypertree.Scheme

/-!
# Source encoding fibres and counter retry plans

The reviewed encoding family captures each complete source coordinate. Bottom
messages have 32 bytes and internal messages have 16 bytes. One 16-byte base
determines the source's full bounded modular counter traversal.
-/

public section

namespace EthereumXMSSHypertree.HypertreeStrategies

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open ConcreteHypertree GXMSS.Encoding OracleComp OracleSpec

/-- The actual generic message fibre equals the source layer-specific message type. -/
theorem messageFibre_eq (position : GXMSS.Hypertree.OTSPosition shape) :
    GXMSS.Hypertree.Message shape Message Digest position =
      DerivationMessage (sourceLayer position.1) := by
  cases hs : sourceLayer position.1 with
  | bottom =>
    have hz : position.1.1.val = 0 := by
      have h := sourceLayer_toNat position.1
      rw [hs] at h
      exact h.symm
    simp [GXMSS.Hypertree.Message, hz, DerivationMessage]
  | top =>
    have hz : position.1.1.val ≠ 0 := by
      have h := sourceLayer_toNat position.1
      rw [hs] at h
      have hv : position.1.1.val = 1 := h.symm
      omega
    simp [GXMSS.Hypertree.Message, hz, DerivationMessage]

/-- Interpret the actual generic message fibre as its source layer's exact message domain. -/
@[expose]
def messageToSource (position : GXMSS.Hypertree.OTSPosition shape) :
    GXMSS.Hypertree.Message shape Message Digest position →
      DerivationMessage (sourceLayer position.1) :=
  Equiv.cast (messageFibre_eq position)

/-- Write a coordinate's bottom message or internal child-root message as exact source bytes. -/
@[expose]
def sourceMessageBytes (position : GXMSS.Hypertree.OTSPosition shape)
    (message : GXMSS.Hypertree.Message shape Message Digest position) : ByteArray :=
  derivationMessageBytes (sourceLayer position.1) (messageToSource position message)

/-- Reading the source message fibre loses none of the actual generic message data. -/
theorem messageToSource_injective (position : GXMSS.Hypertree.OTSPosition shape) :
    Function.Injective (messageToSource position) :=
  (Equiv.cast (messageFibre_eq position)).injective

/-- Exact source message bytes identify every message in its actual generic coordinate fibre. -/
theorem sourceMessageBytes_injective (position : GXMSS.Hypertree.OTSPosition shape) :
    Function.Injective (sourceMessageBytes position) :=
  (derivationMessageBytes_injective _).comp (messageToSource_injective position)

/-- A selected bottom coordinate writes the original 32-byte application message unchanged. -/
theorem sourceMessageBytes_bottom (epoch : GXMSS.Hypertree.Epoch shape) (message : Message) :
    sourceMessageBytes (GXMSS.Hypertree.bottomPosition shape epoch)
      (GXMSS.Hypertree.bottomMessage (H := Digest) epoch message) = packBytes message := rfl

/-- A selected internal coordinate writes the original 16-byte child root unchanged. -/
theorem sourceMessageBytes_internal (position : GXMSS.Hypertree.UpperPosition shape)
    (root : Digest) :
    sourceMessageBytes position.val (GXMSS.Hypertree.internalMessage position root) =
      packBytes root := by
  rcases position with ⟨⟨⟨layer, tree⟩, leaf⟩, positive⟩
  have hl : layer = ⟨1, by decide⟩ := by
    apply Fin.ext
    change layer.val = 1
    have ht := layer.isLt
    change layer.val < 2 at ht
    change layer.val ≠ 0 at positive
    omega
  subst layer
  rfl

/-- The source encoding at one complete generic coordinate, with its source key captured. -/
@[expose]
def sourceComponentEncoding (hash : ByteArray → Vector UInt8 32)
    (position : GXMSS.Hypertree.OTSPosition shape) :
    IncomparableEncoding PublicParam (GXMSS.Hypertree.Message shape Message Digest position)
      Randomizer Unit 58 4 where
  code := (GenericEncoding.sourceEncoding hash (sourceLayer position.1)
    (sourceMessageBytes position)).code
  incomparable := (GenericEncoding.sourceEncoding hash (sourceLayer position.1)
    (sourceMessageBytes position)).incomparable
  encode pp message randomizer _ :=
    (GenericEncoding.sourceEncoding hash (sourceLayer position.1)
      (sourceMessageBytes position)).encode pp message randomizer (sourceKey position)

/-- The actual reviewed coordinate-indexed encoding family for both source message kinds. -/
@[expose]
def sourceEncodingFamily (hash : ByteArray → Vector UInt8 32) :
    GXMSS.Hypertree.EncodingFamily PublicParam Message Randomizer Digest shape where
  component := sourceComponentEncoding hash

/-- A family read is exactly the existing source encoding at the captured global source key. -/
theorem sourceEncodingFamily_value (hash : ByteArray → Vector UInt8 32)
    (position : GXMSS.Hypertree.OTSPosition shape) (pp : PublicParam)
    (message : GXMSS.Hypertree.Message shape Message Digest position) (randomizer : Randomizer) :
    (sourceEncodingFamily hash).value position pp message randomizer =
      (GenericEncoding.sourceEncoding hash (sourceLayer position.1)
        (sourceMessageBytes position)).value pp message randomizer (sourceKey position) := by
  simp only [sourceEncodingFamily, Family.value, sourceComponentEncoding,
    IncomparableEncoding.value]
  rfl

/-- The family retains the complete source decoder, including the six zero-tail checks. -/
theorem sourceEncodingFamily_value_source (hash : ByteArray → Vector UInt8 32)
    (position : GXMSS.Hypertree.OTSPosition shape) (pp : PublicParam)
    (message : GXMSS.Hypertree.Message shape Message Digest position) (randomizer : Randomizer) :
    (sourceEncodingFamily hash).value position pp message randomizer =
      (codeword? ((messageDigest (pureHash hash) pp (sourceLayer position.1)
        (sourceKey position) (sourceMessageBytes position message) randomizer).run)).map
          GenericEncoding.sourceCodewordEquiv := by
  rw [sourceEncodingFamily_value]
  exact GenericEncoding.sourceEncoding_value hash (sourceLayer position.1)
    (sourceMessageBytes position) pp message randomizer (sourceKey position)

/-- A finite source counter prefix, parameterized by the number of attempted digests. -/
@[expose, reducible]
def sourceCounterPlan (budget : Nat) : RetryPlan Randomizer where
  Coins := Randomizer
  budget := budget
  randomizers base index := trialRandomizer base index.val

/-- One source base determines the complete source-budget counter sequence. -/
@[expose, reducible]
def sourceRetryPlan : RetryPlan Randomizer := sourceCounterPlan MAX_RANDOMIZER_TRIALS

/-- Every plan index uses exactly the source's modular additive counter randomizer. -/
@[simp]
theorem sourceRetryPlan_randomizers (base : Randomizer) (index : Fin MAX_RANDOMIZER_TRIALS) :
    sourceRetryPlan.randomizers base index = trialRandomizer base index.val := rfl

/-- Distinct bounded attempts give distinct source randomizers even across modular wraparound. -/
theorem sourceRetryPlan_randomizers_injective (base : Randomizer) :
    Function.Injective (sourceRetryPlan.randomizers base) := by
  intro first second h
  apply Fin.ext
  exact trialRandomizer_injective base first.isLt second.isLt h

/-- Both source message kinds sample one uniform base, rather than independent attempt coins. -/
@[expose, reducible]
def sourceRetrySampling : GXMSS.Hypertree.RetrySampling Randomizer where
  bottom := sourceRetryPlan
  internal := sourceRetryPlan
  sampleBottom := $ᵗ Randomizer
  sampleInternal := $ᵗ Randomizer

/-- The actual generic plan's optional output is exactly the source counter search output. -/
theorem sourceCounterPlan_output (budget : Nat) (hash : ByteArray → Vector UInt8 32)
    (position : GXMSS.Hypertree.OTSPosition shape) (pp : PublicParam)
    (message : GXMSS.Hypertree.Message shape Message Digest position) (base : Randomizer) :
    ((sourceCounterPlan budget).run
      ((sourceEncodingFamily hash).atEpoch position (Fin shape.branching))
        pp message position.2 base).output =
      (retryOutcome hash pp (sourceLayer position.1) (sourceKey position)
        (sourceMessageBytes position message) base 0 budget).map
          (fun result => (GenericEncoding.sourceCodewordEquiv result.2, result.1)) := by
  let enc := (sourceEncodingFamily hash).atEpoch position (Fin shape.branching)
  have hvalue (index : Fin budget) :
      enc.value pp message ((sourceCounterPlan budget).randomizers base index) position.2 =
        (retryAccept hash pp (sourceLayer position.1) (sourceKey position)
          (sourceMessageBytes position message) base index.val).map
            GenericEncoding.sourceCodewordEquiv := by
    dsimp only [enc]
    rw [Family.value_atEpoch, sourceEncodingFamily_value_source]
    rfl
  have hspec := @RetryPlan.run_isFirstSuccess PublicParam
    (GXMSS.Hypertree.Message shape Message Digest position) Randomizer (Fin shape.branching)
    shape.v (2 ^ shape.w) (sourceCounterPlan budget) enc pp message position.2 base
  change ((sourceCounterPlan budget).run enc pp message position.2 base).output = _
  cases hrun : (sourceCounterPlan budget).run enc pp message position.2 base with
  | exhausted consumed =>
    simp only [hrun, RetryPlan.IsFirstSuccess] at hspec
    have hsource : retryOutcome hash pp (sourceLayer position.1) (sourceKey position)
        (sourceMessageBytes position message) base 0 budget = none := by
      apply (retryOutcome_none_iff hash pp _ _ _ base 0 budget).2
      intro j hj hj'
      have h := hspec.2 ⟨j, by simpa using hj'⟩
      rw [hvalue] at h
      exact Option.map_eq_none_iff.mp h
    simp only [IncomparableEncoding.IndexedResult.output, hsource, Option.map_none]
  | success word selected attempt consumed =>
    simp only [hrun, RetryPlan.IsFirstSuccess] at hspec
    obtain ⟨index, hselected, _, _, hword, hbefore⟩ := hspec
    rw [hvalue] at hword
    obtain ⟨digits, hdecoded, hrepresented⟩ := Option.map_eq_some_iff.mp hword
    have hsource := retryOutcome_at_first hash pp (sourceLayer position.1) (sourceKey position)
      (sourceMessageBytes position message) base 0 budget index.val
      (by omega) (by simp) hdecoded (by
        intro k hk hk'
        have h := hbefore ⟨k, by have := index.isLt; omega⟩ hk'
        rw [hvalue] at h
        exact Option.map_eq_none_iff.mp h)
    simp only [IncomparableEncoding.IndexedResult.output, hsource, Option.map_some]
    rw [hrepresented, hselected]

/-- The full-budget generic plan preserves the source's returned success and exhaustion. -/
theorem sourceRetryPlan_output (hash : ByteArray → Vector UInt8 32)
    (position : GXMSS.Hypertree.OTSPosition shape) (pp : PublicParam)
    (message : GXMSS.Hypertree.Message shape Message Digest position) (base : Randomizer) :
    (sourceRetryPlan.run ((sourceEncodingFamily hash).atEpoch position (Fin shape.branching))
      pp message position.2 base).output =
      (retryOutcome hash pp (sourceLayer position.1) (sourceKey position)
        (sourceMessageBytes position message) base 0 MAX_RANDOMIZER_TRIALS).map
          (fun result => (GenericEncoding.sourceCodewordEquiv result.2, result.1)) :=
  sourceCounterPlan_output MAX_RANDOMIZER_TRIALS hash position pp message base

end EthereumXMSSHypertree.HypertreeStrategies
