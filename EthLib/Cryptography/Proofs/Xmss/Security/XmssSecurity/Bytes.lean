module

public import EthLib.Cryptography.Xmss
public import EthLib.Cryptography.Proofs.Xmss.Types
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Types
public import EthLib.Cryptography.Proofs.HashSig.Lanes
public import EthLib.Cryptography.Proofs.Xmss.Words

/-!
# Proofs: EthLib's lanes as the security proof's bit vectors

The security proof writes leanXMSS over bit vectors, EthLib over Keccak lanes.

Each leanXMSS object is the lanes of the low bits of its bit vector.

The bytes of those lanes are the proof's own little-endian encoding of the bit vector.

So EthLib builds a hash input from the converted values, and the oracle reads its bytes.

The proof builds the same bytes from the values themselves.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

export EthLib.Cryptography.HashSig (ofBV getElem_ofBV toList_ofBV ofBV_ofNat ofBV_eq_uintToBytes
  ofBV_ofNat_bytesToUint ofBV_inj)

/-! ## The lanes of each object

Each EthLib object is the lanes of the low bits of the proof's bit vector.

The lemmas state the bytes of those lanes as the proof's 16- and 32-byte little-endian encodings.
-/

open EthLib.Cryptography.Hash.Keccak (lanesBytes)

/-- A digest's two lanes. -/
abbrev ofDigest {w : Nat} (x : BitVec w) : Digest := HashSig.ofDigestLanes x

/-- A public parameter's two lanes. -/
abbrev ofParam {w : Nat} (x : BitVec w) : PublicParam := HashSig.ofDigestLanes x

/-- A randomizer's two lanes. -/
abbrev ofRandomizer {w : Nat} (x : BitVec w) : Randomizer := HashSig.ofDigestLanes x

/-- A seed's four lanes. -/
abbrev ofSeed {w : Nat} (x : BitVec w) : Seed := HashSig.ofOutputLanes x

/-- A message's four lanes. -/
abbrev ofMessage {w : Nat} (x : BitVec w) : Message := HashSig.ofOutputLanes x

/-- An oracle answer's four lanes. -/
abbrev ofOutput {w : Nat} (x : BitVec w) : Lanes4 := HashSig.ofOutputLanes x

@[simp] theorem toList_ofDigest (x : XmssSecurity.Digest) :
    lanesBytes (ofDigest x).toArray = XmssSecurity.bytesLE 16 x := by
  rw [Hash.Keccak.lanesBytes_lanes2, HashSig.bytes_ofDigestLanes]
  exact HashSig.toList_ofBV 16 x

@[simp] theorem toList_ofParam (x : XmssSecurity.PublicParameter) :
    lanesBytes (ofParam x).toArray = XmssSecurity.bytesLE 16 x := by
  rw [Hash.Keccak.lanesBytes_lanes2, HashSig.bytes_ofDigestLanes]
  exact HashSig.toList_ofBV 16 x

@[simp] theorem toList_ofRandomizer (x : XmssSecurity.Randomness) :
    lanesBytes (ofRandomizer x).toArray = XmssSecurity.bytesLE 16 x := by
  rw [Hash.Keccak.lanesBytes_lanes2, HashSig.bytes_ofDigestLanes]
  exact HashSig.toList_ofBV 16 x

@[simp] theorem toList_ofSeed (x : XmssSecurity.MasterSeed) :
    lanesBytes (ofSeed x).toArray = XmssSecurity.bytesLE 32 x := by
  rw [Hash.Keccak.lanesBytes_lanes4, HashSig.bytes_ofOutputLanes]
  exact HashSig.toList_ofBV 32 x

@[simp] theorem toList_ofMessage (x : XmssSecurity.Message) :
    lanesBytes (ofMessage x).toArray = XmssSecurity.bytesLE 32 x := by
  rw [Hash.Keccak.lanesBytes_lanes4, HashSig.bytes_ofOutputLanes]
  exact HashSig.toList_ofBV 32 x

/-! ## The two halves of a hash value -/

/-- The first 16 bytes of a hash value are the lanes of its low 128 bits. -/
theorem halfOf_zero_ofOutput (x : XmssSecurity.HashOutput) :
    halfOf 0 (ofOutput x) = ofDigest (XmssSecurity.truncateHash x) :=
  HashSig.first_lanes_ofOutputLanes x

/-- The last 16 bytes of a hash value are the lanes of its high 128 bits. -/
theorem halfOf_one_ofOutput (x : XmssSecurity.HashOutput) :
    halfOf 1 (ofOutput x) = ofDigest (XmssSecurity.upperHash x) := by
  rw [show halfOf 1 (ofOutput x) = ⟨(HashSig.ofOutputLanes x).w2, (HashSig.ofOutputLanes x).w3⟩
      from rfl, HashSig.last_lanes_ofOutputLanes]
  rfl

/-- The half of a hash value that starts chain `i`: the first for even `i`, the last for odd `i`. -/
theorem halfOf_mod_two_ofOutput (x : XmssSecurity.HashOutput) (i : Nat) :
    halfOf ⟨i % 2, Nat.mod_lt _ (by decide)⟩ (ofOutput x)
      = ofDigest (XmssSecurity.hashHalf i x) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · simp only [h, XmssSecurity.hashHalf, ↓reduceIte]
    exact halfOf_zero_ofOutput x
  · simp only [h, XmssSecurity.hashHalf, Nat.one_ne_zero, ↓reduceIte]
    exact halfOf_one_ofOutput x

end EthLib.Cryptography.Xmss.Unforgeability
