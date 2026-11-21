/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.QueryCache
public import EthereumXMSSHypertree.Reachability
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Legal source seed-derivation requests

The source derives its public parameter, paired chain starts and randomizer
bases. Bottom bases carry 32-byte messages; top bases carry 16-byte child roots.
The complete-response query map retains the public parameter, address and suffix
and is injective across these three source families.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open Reachability

/-- The actual source message domain for each layer's randomizer base. -/
@[expose]
def DerivationMessage : Layer → Type
  | .bottom => Message
  | .top => Digest

/-- The source writes bottom messages and top child roots as their exact bytes. -/
@[expose]
def derivationMessageBytes : (layer : Layer) → DerivationMessage layer → ByteArray
  | .bottom, message => packBytes message
  | .top, root => packBytes root

/-- A source randomizer-base suffix retains its complete layer-specific message. -/
theorem derivationMessageBytes_injective (layer : Layer) :
    Function.Injective (derivationMessageBytes layer) := by
  cases layer <;> exact packBytes_injective

/-- Legal requests to the source seed derivation, with one full response per paired start. -/
inductive SourceQuery where
  /-- The unique request with zero parameter, parameter address and empty suffix. -/
  | publicParameter
  /-- One complete response supplies chains `2j` and `2j+1` at a legal source key. -/
  | start (publicParam : PublicParam) (layer : Layer) (key : KeyCoordinate layer)
      (pair : Fin (V / 2))
  /-- One complete response supplies the base for the source's modular counter traversal. -/
  | retryBase (publicParam : PublicParam) (layer : Layer) (key : KeyCoordinate layer)
      (message : DerivationMessage layer)

/-- Equality of legal requests is available without enumerating the source domains. -/
noncomputable instance sourceQueryDecidableEq : DecidableEq SourceQuery := Classical.decEq _

/-- The legal source domain is finite without constructing an enumeration of byte vectors. -/
instance sourceQueryFinite : Finite SourceQuery := by
  let : Finite Layer := Finite.of_equiv (Fin 2) layerEquiv.symm
  let : (layer : Layer) → Finite (DerivationMessage layer) := by
    intro layer
    cases layer with
    | bottom => change Finite Message; infer_instance
    | top => change Finite Digest; infer_instance
  let fields := Unit ⊕
    ((Σ layer : Layer, PublicParam × KeyCoordinate layer × Fin (V / 2)) ⊕
      (Σ layer : Layer, PublicParam × KeyCoordinate layer × DerivationMessage layer))
  let decode : fields → SourceQuery := fun query => match query with
    | .inl _ => .publicParameter
    | .inr (.inl ⟨layer, pp, key, pair⟩) => .start pp layer key pair
    | .inr (.inr ⟨layer, pp, key, message⟩) => .retryBase pp layer key message
  apply Finite.of_surjective decode
  intro query
  cases query with
  | publicParameter => exact ⟨.inl (), rfl⟩
  | start pp layer key pair => exact ⟨.inr (.inl ⟨layer, pp, key, pair⟩), rfl⟩
  | retryBase pp layer key message => exact ⟨.inr (.inr ⟨layer, pp, key, message⟩), rfl⟩

/-- Embed each legal family into the actual complete-response `SeedPrf` interface. -/
@[expose]
def sourceQueryToDerivation : SourceQuery → DerivationQuery
  | .publicParameter => ⟨Vector.replicate PUBLIC_PARAM_LEN 0, addrParam, .empty⟩
  | .start pp layer key pair =>
      ⟨pp, addrPrf layer (UInt32.ofNat key.val) pair, .empty⟩
  | .retryBase pp layer key message =>
      ⟨pp, addrRnd layer (UInt32.ofNat key.val), derivationMessageBytes layer message⟩

private theorem param_ne_start (layer : Layer) (word : UInt32) (pair : Fin (V / 2)) :
    addrParam ≠ addrPrf layer word pair := by
  intro h
  have hcode := (encodeAddress_inj.mp h).1
  exact (by decide : AddressType.param.code ≠ AddressType.prf.code) hcode

private theorem param_ne_base (layer : Layer) (word : UInt32) :
    addrParam ≠ addrRnd layer word := by
  intro h
  have hcode := (encodeAddress_inj.mp h).1
  exact (by decide : AddressType.param.code ≠ AddressType.rnd.code) hcode

private theorem start_ne_base (layer otherLayer : Layer) (word otherWord : UInt32)
    (pair : Fin (V / 2)) : addrPrf layer word pair ≠ addrRnd otherLayer otherWord := by
  intro h
  have hcode := (encodeAddress_inj.mp h).1
  exact (by decide : AddressType.prf.code ≠ AddressType.rnd.code) hcode

private theorem keyCoordinate_word_injective (layer : Layer) :
    Function.Injective (fun key : KeyCoordinate layer => UInt32.ofNat key.val) := by
  intro first second h
  apply Fin.ext
  have hn := congrArg UInt32.toNat h
  simpa only [keyCoordinate_no_wrap] using hn

private theorem sourceQueryToDerivation_param_injective (second : SourceQuery)
    (h : sourceQueryToDerivation .publicParameter = sourceQueryToDerivation second) :
    SourceQuery.publicParameter = second := by
  cases second with
  | publicParameter => rfl
  | start pp layer key pair =>
    exact False.elim (param_ne_start layer (UInt32.ofNat key.val) pair
      (congrArg DerivationQuery.address h))
  | retryBase pp layer key message =>
    exact False.elim (param_ne_base layer (UInt32.ofNat key.val)
      (congrArg DerivationQuery.address h))

private theorem sourceQueryToDerivation_start_eq (pp otherPP : PublicParam)
    (layer otherLayer : Layer) (key : KeyCoordinate layer) (otherKey : KeyCoordinate otherLayer)
    (pair otherPair : Fin (V / 2))
    (h : sourceQueryToDerivation (.start pp layer key pair) =
      sourceQueryToDerivation (.start otherPP otherLayer otherKey otherPair)) :
    SourceQuery.start pp layer key pair = .start otherPP otherLayer otherKey otherPair := by
  have hpp : pp = otherPP := congrArg DerivationQuery.publicParam h
  have haddress : addrPrf layer (UInt32.ofNat key.val) pair =
      addrPrf otherLayer (UInt32.ofNat otherKey.val) otherPair :=
    congrArg DerivationQuery.address h
  obtain ⟨hlayer, hkey, hpair⟩ := (addrPrf_inj (layer := layer) (layer' := otherLayer)
    (e := UInt32.ofNat key.val) (e' := UInt32.ofNat otherKey.val)
    (j := pair) (j' := otherPair)).mp haddress
  subst otherPP otherLayer otherPair
  have hk := keyCoordinate_word_injective layer hkey
  subst otherKey
  rfl

private theorem sourceQueryToDerivation_start_injective (pp : PublicParam) (layer : Layer)
    (key : KeyCoordinate layer) (pair : Fin (V / 2)) (second : SourceQuery)
    (h : sourceQueryToDerivation (.start pp layer key pair) = sourceQueryToDerivation second) :
    SourceQuery.start pp layer key pair = second := by
  cases second with
  | publicParameter =>
    exact False.elim (param_ne_start layer (UInt32.ofNat key.val) pair
      (congrArg DerivationQuery.address h).symm)
  | start otherPP otherLayer otherKey otherPair =>
    exact sourceQueryToDerivation_start_eq pp otherPP layer otherLayer key otherKey
      pair otherPair h
  | retryBase otherPP otherLayer otherKey message =>
    have haddress : addrPrf layer (UInt32.ofNat key.val) pair =
        addrRnd otherLayer (UInt32.ofNat otherKey.val) := congrArg DerivationQuery.address h
    exact False.elim (start_ne_base layer otherLayer
      (UInt32.ofNat key.val) (UInt32.ofNat otherKey.val) pair
      haddress)

private theorem sourceQueryToDerivation_base_injective (pp : PublicParam) (layer : Layer)
    (key : KeyCoordinate layer) (message : DerivationMessage layer) (second : SourceQuery)
    (h : sourceQueryToDerivation (.retryBase pp layer key message) =
      sourceQueryToDerivation second) : SourceQuery.retryBase pp layer key message = second := by
  cases second with
  | publicParameter =>
    exact False.elim (param_ne_base layer (UInt32.ofNat key.val)
      (congrArg DerivationQuery.address h).symm)
  | start otherPP otherLayer otherKey pair =>
    exact False.elim (start_ne_base otherLayer layer
      (UInt32.ofNat otherKey.val) (UInt32.ofNat key.val) pair
      (congrArg DerivationQuery.address h).symm)
  | retryBase otherPP otherLayer otherKey otherMessage =>
    have hpp : pp = otherPP := congrArg DerivationQuery.publicParam h
    have haddress : addrRnd layer (UInt32.ofNat key.val) =
        addrRnd otherLayer (UInt32.ofNat otherKey.val) := congrArg DerivationQuery.address h
    obtain ⟨hlayer, hkey⟩ := (addrRnd_inj (layer := layer) (layer' := otherLayer)
      (e := UInt32.ofNat key.val) (e' := UInt32.ofNat otherKey.val)).mp haddress
    subst otherPP otherLayer
    have hk := keyCoordinate_word_injective layer hkey
    subst otherKey
    have hmessage := derivationMessageBytes_injective layer (congrArg DerivationQuery.suffix h)
    subst otherMessage
    rfl

/-- Complete source requests determine their family, parameter, legal coordinate and message. -/
theorem sourceQueryToDerivation_injective : Function.Injective sourceQueryToDerivation := by
  intro first second h
  cases first with
  | publicParameter => exact sourceQueryToDerivation_param_injective second h
  | start pp layer key pair =>
    exact sourceQueryToDerivation_start_injective pp layer key pair second h
  | retryBase pp layer key message =>
    exact sourceQueryToDerivation_base_injective pp layer key message second h

/-- Insert the fixed source scheme seed into a legal complete-response request. -/
@[expose]
def sourceQueryInput (seed : Seed) (query : SourceQuery) : ByteArray :=
  derivationInput seed (sourceQueryToDerivation query)

/-- Legal source queries have distinct complete byte inputs for every fixed scheme seed. -/
theorem sourceQueryInput_injective (seed : Seed) : Function.Injective (sourceQueryInput seed) :=
  (derivationInput_injective seed).comp sourceQueryToDerivation_injective

/-- Restrict the source's raw-seed PRF to precisely the legal source derivation families. -/
@[expose]
def typedSourcePRF (hash : ByteArray → FullResponse) : PRFScheme Seed SourceQuery FullResponse where
  keygen := (rawSeedPRF hash).keygen
  eval raw query := (rawSeedPRF hash).eval raw (sourceQueryToDerivation query)

/-- The legal-family restriction preserves the exact uniform raw 32-byte key sampler. -/
theorem typedSourcePRF_uniformKey (hash : ByteArray → FullResponse) :
    (typedSourcePRF hash).UniformKey := rfl

/-- The legal-family evaluator still derives the scheme seed inside raw-key evaluation. -/
theorem typedSourcePRF_eval (hash : ByteArray → FullResponse) (raw : Seed) (query : SourceQuery) :
    (typedSourcePRF hash).eval raw query =
      hash (sourceQueryInput ((schemeSeed (pureHash hash) raw).run) query) := rfl

/-- Paired start coordinates for all bottom keys and all top keys, at one fixed public parameter. -/
abbrev SourceStartCoordinate :=
  (KeyCoordinate .bottom × Fin (V / 2)) ⊕ (KeyCoordinate .top × Fin (V / 2))

/-- Every global start coordinate names exactly one of the legal paired-response queries. -/
@[expose]
def sourceStartCoordinateQuery (pp : PublicParam) : SourceStartCoordinate → SourceQuery
  | .inl (key, pair) => .start pp .bottom key pair
  | .inr (key, pair) => .start pp .top key pair

/-- At a fixed parameter, different global start coordinates give different source queries. -/
theorem sourceStartCoordinateQuery_injective (pp : PublicParam) :
    Function.Injective (sourceStartCoordinateQuery pp) := by
  intro first second h
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      obtain ⟨key, pair⟩ := first
      obtain ⟨otherKey, otherPair⟩ := second
      cases h
      rfl
    | inr second => cases h
  | inr first =>
    cases second with
    | inl second => cases h
    | inr second =>
      obtain ⟨key, pair⟩ := first
      obtain ⟨otherKey, otherPair⟩ := second
      cases h
      rfl

/-- The exact global paired-start capacity at a fixed source public parameter. -/
theorem sourceStartCoordinate_card :
    Nat.card SourceStartCoordinate = 29 * (2 ^ 32 + 2 ^ 16) := by
  simp [SourceStartCoordinate, KeyCoordinate, layerBits, V]

/-- There are 124,555,952,128 complete paired-start coordinates across both source layers. -/
theorem sourceStartCoordinate_card_value : Nat.card SourceStartCoordinate = 124555952128 := by
  rw [sourceStartCoordinate_card]
  norm_num

end EthereumXMSSHypertree
