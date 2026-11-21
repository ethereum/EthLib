module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Bytes
public import EthLib.Cryptography.Proofs.Xmss.Address

/-!
# Proofs: EthLib's addresses are the model's

The model writes an address as the bytes of four fields, `tau`, `mu`, `hi` and `lo`.

EthLib's address of the same call has the same 16 bytes.

```text
    [ lo: 4 | hi: 3 | tau + 32 mu: 1 | zero: 8 ]     both
```

The top layer sets bit 23 of `hi`, the model's top flag.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.HashSig (toList_uintToBytes append_ofNat)

/-! ## The encoding -/

/-- The bytes of an address's lanes are its four fields, each in its own little-endian bytes. -/
theorem bytes_encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    (encodeAddress tau mu hi lo).bytes.toList =
      (uintToBytes 4 lo.toNat).toList ++ (uintToBytes 3 hi.val).toList
        ++ (uintToBytes 1 (tau.val + 32 * mu.val)).toList ++ (uintToBytes 8 0).toList := by
  have hlo : lo.toNat < 2 ^ 32 := lo.toNat_lt_size
  have hhi := hi.isLt
  have ht : tau.val + 32 * mu.val < 2 ^ 8 := by have := tau.isLt; have := mu.isLt; omega
  -- Both are the bytes of `lo + 2^32 hi + 2^56 (tau + 32 mu)`, the high lane being zero.
  have hn : lanesToNat (encodeAddress tau mu hi lo) =
      lo.toNat + 2 ^ 32 * hi.val + 2 ^ 56 * (tau.val + 32 * mu.val) := by
    rw [lanesToNat, toNat_encodeAddress_lo]
    simp [encodeAddress]
  rw [bytes_eq, hn]
  generalize lo.toNat = a at *
  generalize hi.val = b at *
  generalize tau.val + 32 * mu.val = c at *
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [Vector.length_toList] at h1
  apply UInt8.toNat_inj.mp
  simp only [Vector.getElem_toList, Base.uintToBytes_eq_div, Vector.getElem_ofFn]
  interval_cases j <;> simp [UInt8.toNat_ofNat'] <;> omega

/-- EthLib's address encoding lists the bytes of the model's, for the same four fields. -/
theorem toList_encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    Hash.Keccak.lanesBytes (encodeAddress tau mu hi lo).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields tau.val mu.val hi.val lo.toNat) := by
  -- The address is a concatenation of 4 + 3 + 1 + 8 bytes, which is its length constant.
  rw [Hash.Keccak.lanesBytes_lanes2, bytes_encodeAddress]
  simp only [toList_uintToBytes, XmssSecurity.fieldBytes,
    XmssSecurity.tweakFields, append_ofNat tau.val mu.val tau.isLt mu.isLt]
  rfl

/-! ## The addresses of a key

`2^23 l` is the flag of layer `l` in `hi`.

It is zero at the bottom, and the model's top flag at the top. -/

theorem toList_addrChain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) :
    Hash.Keccak.lanesBytes (addrChain layer e mu).toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 1 mu.val (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrChain, toList_encodeAddress]
  simp [layerHi, AddressType.code]

theorem toList_addrLeaf (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (addrLeaf layer e).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 2 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrLeaf, toList_encodeAddress]
  simp [layerHi, AddressType.code]

theorem toList_addrMsg (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (addrMsg layer e).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 12 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrMsg, toList_encodeAddress]
  simp [layerHi, AddressType.code]

theorem toList_addrRnd (layer : Layer) (e : UInt32) :
    Hash.Keccak.lanesBytes (addrRnd layer e).toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrRnd, toList_encodeAddress]
  simp [layerHi, AddressType.code]

/-- The parent at level `level`, `level >= 1`, carries the level in `hi`. -/
theorem toList_addrNode (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32) :
    Hash.Keccak.lanesBytes (addrNode layer level j).toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 3 0 (2 ^ 23 * layer.toNat + level.val) j.toNat) := by
  rw [addrNode, toList_encodeAddress]
  simp [layerHi, AddressType.code, Nat.add_comm]

theorem toList_addrPrf (layer : Layer) (e : UInt32) (j : Fin (V / 2)) :
    Hash.Keccak.lanesBytes (addrPrf layer e j).toArray
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 0 0 (2 ^ 23 * layer.toNat + j.val) e.toNat) := by
  rw [addrPrf, toList_encodeAddress]
  simp [layerHi, AddressType.code, Nat.add_comm]

theorem toList_addrParam :
    Hash.Keccak.lanesBytes addrParam.toArray
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 5 0 0 0) := by
  rw [addrParam, toList_encodeAddress]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability
