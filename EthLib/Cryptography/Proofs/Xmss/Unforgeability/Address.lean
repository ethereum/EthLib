import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Bytes

/-!
# Proofs: EthLib's addresses are the model's

The model writes an address as four fields, `fieldBytes (tweakFields tau mu hi lo)`.

EthLib's address of the same call has the same 16 bytes.

```text
    [ lo: 4 | hi: 3 | tau + 32 mu: 1 | zero: 8 ]     both
```

The top layer sets bit 23 of `hi`, the model's `topFlag`.
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## The encoding -/

/-- `LE_{8k}(z)`, listed, is the model's `bytesLE k` of `z` as a `8 k`-bit vector. -/
theorem toList_littleEndian (k z : Nat) :
    (littleEndian k z).toList = XmssSecurity.bytesLE k (BitVec.ofNat (8 * k) z) := by
  rw [← ofBV_ofNat, toList_ofBV]

/-- The byte that holds a type below 32 and a position below 8. -/
private theorem append_ofNat (tau mu : Nat) (htau : tau < 32) (hmu : mu < 8) :
    BitVec.ofNat 3 mu ++ BitVec.ofNat 5 tau = BitVec.ofNat (8 * 1) (tau + 32 * mu) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmu,
    show tau % 2 ^ 5 = tau from Nat.mod_eq_of_lt (by omega)]
  -- The position sits above the 5 bits of the type, so `or` is a sum.
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

/-- EthLib's address encoding lists the bytes of the model's, for the same four fields. -/
theorem toList_encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    (encodeAddress tau mu hi lo).toList
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields tau.val mu.val hi.val lo.toNat) := by
  -- The address is a concatenation of 4 + 3 + 1 + 8 bytes, which is its length constant.
  show (littleEndian 4 lo.toNat ++ littleEndian 3 hi.val ++ littleEndian 1 (tau.val + 32 * mu.val)
    ++ littleEndian 8 0 : Vector UInt8 (4 + 3 + 1 + 8)).toList = _
  simp only [Vector.toList_append, toList_littleEndian, XmssSecurity.fieldBytes,
    XmssSecurity.tweakFields, append_ofNat tau.val mu.val tau.isLt mu.isLt]
  rfl

/-! ## The addresses of a key

`2^23 l` is the flag of layer `l` in `hi`: zero at the bottom, the model's `topFlag` at the top. -/

theorem toList_addrChain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) :
    (addrChain layer e mu).toList
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 1 mu.val (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrChain, toList_encodeAddress]
  simp [layerHi, AddressType.code]

theorem toList_addrLeaf (layer : Layer) (e : UInt32) :
    (addrLeaf layer e).toList
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 2 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrLeaf, toList_encodeAddress]
  simp [layerHi, AddressType.code]

theorem toList_addrMsg (layer : Layer) (e : UInt32) :
    (addrMsg layer e).toList
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 12 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrMsg, toList_encodeAddress]
  simp [layerHi, AddressType.code]

theorem toList_addrRnd (layer : Layer) (e : UInt32) :
    (addrRnd layer e).toList
      = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 7 0 (2 ^ 23 * layer.toNat) e.toNat) := by
  rw [addrRnd, toList_encodeAddress]
  simp [layerHi, AddressType.code]

/-- The parent at level `level`, `level >= 1`, carries the level in `hi`. -/
theorem toList_addrNode (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : UInt32) :
    (addrNode layer level j).toList
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 3 0 (2 ^ 23 * layer.toNat + level.val) j.toNat) := by
  rw [addrNode, toList_encodeAddress]
  simp [layerHi, AddressType.code, Nat.add_comm]

theorem toList_addrPrf (layer : Layer) (e : UInt32) (j : Fin (V / 2)) :
    (addrPrf layer e j).toList
      = XmssSecurity.fieldBytes
          (XmssSecurity.tweakFields 0 0 (2 ^ 23 * layer.toNat + j.val) e.toNat) := by
  rw [addrPrf, toList_encodeAddress]
  simp [layerHi, AddressType.code, Nat.add_comm]

theorem toList_addrParam :
    addrParam.toList = XmssSecurity.fieldBytes (XmssSecurity.tweakFields 5 0 0 0) := by
  rw [addrParam, toList_encodeAddress]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability
