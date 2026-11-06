module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Signature

/-!
# Proofs: every EthLib signature is a model signature

The adversary of EthLib's game forges an EthLib signature.

Reading each byte field as a little-endian number gives a model signature.

Its translation back is the forgery itself, so the verifier lemma applies to every forgery.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

/-- EthLib's bytes as a model digest: their little-endian number, on 128 bits. -/
def toDigest {k : Nat} (d : Vector UInt8 k) : SphincsSecurity.Digest :=
  BitVec.ofNat _ (bytesToUint d)

/-- A digest read as a number and written back is itself. -/
theorem ofDigest_toDigest (d : Digest) : ofDigest (toDigest d) = d :=
  HashSig.ofBV_ofNat_bytesToUint d (by decide)

/-- A randomizer read as a number and written back is itself. -/
theorem ofRandomizer_toDigest (r : Randomizer) : ofRandomizer (toDigest r) = r :=
  HashSig.ofBV_ofNat_bytesToUint r (by decide)

/-- EthLib's opening as the model's. -/
def toOpening (o : TreeOpening) : SphincsSecurity.TreeOpening :=
  ⟨toDigest o.secret, fun i => toDigest (o.path[i.val]'(lt_of_lt_of_eq i.isLt rfl))⟩

/-- An opening read as the model's and written back is itself. -/
theorem ofOpening_toOpening (o : TreeOpening) : ofOpening (toOpening o) = o := by
  rcases o with ⟨secret, path⟩
  simp only [ofOpening, toOpening, ofPath, ofDigest_toDigest, TreeOpening.mk.injEq, true_and]
  exact Vector.ext fun i hi => by simp only [Vector.getElem_ofFn]; rfl

/-- EthLib's layer signature as the model's, on the same layer. -/
def toLayerSignature (lay : SphincsSecurity.Layer) (s : LayerSignature (layerOf lay)) :
    SphincsSecurity.LayerSignature lay :=
  ⟨BitVec.ofNat _ s.counter.toNat,
    fun c => toDigest (s.chainValues[c.val]'(lt_of_lt_of_eq c.isLt rfl)),
    fun i => toDigest (s.path[i.val]'(by rw [height_layerOf]; exact i.isLt))⟩

/-- A layer signature read as the model's and written back is itself. -/
theorem ofLayerSignature_toLayerSignature (lay : SphincsSecurity.Layer)
    (s : LayerSignature (layerOf lay)) : ofLayerSignature lay (toLayerSignature lay s) = s := by
  rcases s with ⟨counter, chainValues, path⟩
  simp only [ofLayerSignature, toLayerSignature, LayerSignature.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · apply UInt32.toNat.inj
    simp [ofCounter, SphincsSecurity.counterBits]
  · exact Vector.ext fun i hi => by
      simp only [ofChains, Vector.getElem_ofFn, ofDigest_toDigest]
      rfl
  · exact Vector.ext fun i hi => by simp [ofDigest_toDigest]

/-- EthLib's signature as the model's: the bottom layer is the model's layer 2. -/
def toSignature (sig : Signature) : SphincsSecurity.Signature where
  randomness := toDigest sig.randomizer
  fors := fun κ => toOpening (sig.fors[κ.val]'(lt_of_lt_of_eq κ.isLt rfl))
  layers := fun lay => match lay with
    | ⟨0, _⟩ => toLayerSignature _ sig.top
    | ⟨1, _⟩ => toLayerSignature _ sig.middle
    | ⟨2, _⟩ => toLayerSignature _ sig.bottom
    | ⟨n + 3, h⟩ => absurd h (by change ¬ n + 3 < 3; omega)

/-- Every EthLib signature is the translation of a model signature. -/
theorem ofSignature_toSignature (sig : Signature) : ofSignature (toSignature sig) = sig := by
  rcases sig with ⟨randomizer, fors, bottom, middle, top⟩
  have hfors : ofOpenings (toSignature ⟨randomizer, fors, bottom, middle, top⟩).fors = fors :=
    Vector.ext fun i hi => by
      simp only [ofOpenings, toSignature, Vector.getElem_ofFn, ofOpening_toOpening]
      rfl
  exact (Signature.mk.injEq _ _ _ _ _ _ _ _ _ _).mpr ⟨ofRandomizer_toDigest _, hfors,
    ofLayerSignature_toLayerSignature bottomLayer bottom,
    ofLayerSignature_toLayerSignature middleLayer middle,
    ofLayerSignature_toLayerSignature SphincsSecurity.topLayer top⟩

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
