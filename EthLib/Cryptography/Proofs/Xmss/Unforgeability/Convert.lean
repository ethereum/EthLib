import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Bytes

/-!
# Proofs: EthLib's values from the model's

The security proof's model (`XmssSecurity`) writes values as bit vectors.

These definitions read them as EthLib's: digests, paths, chain values, leaf indices, public keys
and signatures.

`queryH` is `H` as a query to the model's oracle.

The model's verifier is EthLib's `verifyWith`, run with `queryH` on these translations.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] [HasQuery XmssSecurity.HashSpec m]

/-- A chain as the model numbers it. -/
def chainOf (i : Fin V) : XmssSecurity.ChainIndex := ⟨i.val, i.isLt⟩

/-- `H` as a query to the model's oracle.

The input's bytes go in, and the answer's 32 bytes come out. -/
def queryH (input : ByteArray) : m (Vector UInt8 32) :=
  ofOutput <$> XmssSecurity.Concrete.oracleHash (m := m) input.data.toList


/-- The 58 values of a function on chains, as EthLib's vector of digests. -/
def ofChains (f : XmssSecurity.ChainIndex → XmssSecurity.Digest) : Vector Digest V :=
  Vector.ofFn fun i => ofDigest (f (chainOf i))

/-- A path as the model writes it, as EthLib's vector of 16 digests. -/
def ofPath (f : Fin XmssSecurity.treeHeight → XmssSecurity.Digest) : Vector Digest LAYER_HEIGHT :=
  Vector.ofFn fun l => ofDigest (f ⟨l.val, l.isLt⟩)


/-! ## Keys

A bottom key is a leaf index below `2^32`, and a top key an index below `2^16`.

EthLib numbers both as `UInt32`. -/

/-- A leaf index as EthLib's. -/
def ofLeafIndex (idx : XmssSecurity.LeafIndex) : LeafIndex :=
  UInt32.ofNatLT idx.val (by simpa [XmssSecurity.lifetime, XmssSecurity.treeHeight] using idx.isLt)

/-- A top key as EthLib's. -/
def ofTopIndex (key : XmssSecurity.TopIndex) : UInt32 :=
  UInt32.ofNatLT key.val (lt_of_lt_of_le key.isLt (by decide))

@[simp] theorem toNat_ofLeafIndex (idx : XmssSecurity.LeafIndex) :
    (ofLeafIndex idx).toNat = idx.val := by
  simp [ofLeafIndex]

@[simp] theorem toNat_ofTopIndex (key : XmssSecurity.TopIndex) :
    (ofTopIndex key).toNat = key.val := by
  simp [ofTopIndex]


/-! ## Keys and signatures -/

/-- A public key as EthLib's. -/
@[simps] def ofPublicKey (pk : XmssSecurity.PublicKey) : PublicKey where
  root := ofDigest pk.root
  publicParam := ofParam pk.parameter

/-- One layer's signature as EthLib's. -/
@[simps] def ofLayerSig (s : XmssSecurity.LayerSignature) : LayerSignature where
  randomizer := ofRandomizer s.randomness
  chainValues := ofChains s.chainValue
  path := ofPath s.authPath

/-- A signature at a leaf index as EthLib's, which carries the leaf index. -/
@[simps] def ofSignature (idx : XmssSecurity.LeafIndex) (σ : XmssSecurity.Signature) :
    Signature where
  leafIndex := ofLeafIndex idx
  bottom := ofLayerSig ⟨σ.randomness, σ.chainValue, σ.authPath⟩
  top := ofLayerSig σ.top

/-- A digest as the model writes it, from its bytes. -/
def toDigest (d : Digest) : XmssSecurity.Digest :=
  BitVec.ofNat _ (fromLittleEndian d)

@[simp] theorem ofDigest_toDigest (d : Digest) : ofDigest (toDigest d) = d :=
  ofBV_ofNat_fromLittleEndian d (by simp [DIGEST_LEN, XmssSecurity.digestBits])

@[simp] theorem toDigest_ofDigest (d : XmssSecurity.Digest) : toDigest (ofDigest d) = d :=
  ofBV_inj (n := DIGEST_LEN) (by simp [DIGEST_LEN, XmssSecurity.digestBits]) (ofDigest_toDigest _)

end EthLib.Cryptography.Xmss.Unforgeability
