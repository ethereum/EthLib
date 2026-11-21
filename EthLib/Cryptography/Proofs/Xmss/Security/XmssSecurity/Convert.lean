module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Bytes

/-!
# Proofs: EthLib's values from the model's

The security proof's model writes values as bit vectors.

These definitions read them as EthLib's.

They cover digests, paths, chain values, leaf indices, public keys and signatures.

The hash `H` is also a query to the model's oracle.

The model's hashes and verifier are EthLib's, run with that query on these translations.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- `H` as a query to the oracle: the bytes of the input's lanes go in.

The answer comes out as four lanes. -/
abbrev queryH {m : Type → Type} [Monad m] [HasQuery XmssSecurity.HashSpec m]
    (input : Array UInt64) : m Lanes4 :=
  HashSig.queryLanes input

/-- A chain as the model numbers it. -/
def chainOf (i : Fin V) : XmssSecurity.ChainIndex := ⟨i.val, i.isLt⟩

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

/-- A digest as the model writes it, from the integer of its lanes. -/
def toDigest (d : Digest) : XmssSecurity.Digest :=
  BitVec.ofNat _ (d.toNat)

@[simp] theorem ofDigest_toDigest (d : Digest) : ofDigest (toDigest d) = d := by
  apply Hash.Keccak.Lanes2.bytes_injective
  rw [HashSig.bytes_ofDigestLanes, toDigest, Hash.Keccak.Lanes2.bytes_eq_uintToBytes,
    ← ofBV_ofNat_bytesToUint (uintToBytes 16 (d.toNat)) (w := XmssSecurity.digestBits)
      (by simp [XmssSecurity.digestBits]),
    Base.bytesToUint_uintToBytes, Nat.mod_eq_of_lt (by simpa using Hash.Keccak.Lanes2.toNat_lt d)]

@[simp] theorem toDigest_ofDigest (d : XmssSecurity.Digest) : toDigest (ofDigest d) = d :=
  HashSig.ofDigestLanes_injective (ofDigest_toDigest _)

end EthLib.Cryptography.Xmss.Unforgeability
