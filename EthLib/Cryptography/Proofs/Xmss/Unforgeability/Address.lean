import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Bytes

/-!
# Proofs: EthLib's addresses are the security proof's

The security proof names each hash call by a domain, a call site of one key.

Its address bytes are `fieldBytes` of the domain's four fields.

EthLib's address of the same call site has the same 16 bytes.

```text
    [ lo: 4 | hi: 3 | tau + 32 mu: 1 | zero: 8 ]     both
```
-/

namespace EthLib.Cryptography.Xmss.Unforgeability

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-! ## Layers and keys -/

/-- A layer as the proof numbers it: 0 at the bottom, 1 at the top. -/
def layerOf (layer : Layer) : LeanXmss.Layer :=
  ⟨layer.toNat, by cases layer <;> decide⟩

@[simp] theorem val_layerOf (layer : Layer) : (layerOf layer).val = layer.toNat := rfl

/-- A key's index as the proof writes it, below `2^32`. -/
def keyOf (e : UInt32) : LeanXmss.KeyIndex :=
  ⟨e.toNat, by simpa [LeanXmss.lifetime, LeanXmss.numLayers, LeanXmss.layerHeight] using e.toNat_lt⟩

@[simp] theorem val_keyOf (e : UInt32) : (keyOf e).val = e.toNat := rfl

/-! ## The encoding -/

/-- `LE_{8k}(z)`, listed, is the proof's `bytesLE k` of `z` as a `8 k`-bit vector. -/
theorem toList_littleEndian (k z : Nat) :
    (littleEndian k z).toList = LeanXmss.bytesLE k (BitVec.ofNat (8 * k) z) := by
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

/-- EthLib's address encoding lists the bytes of the proof's, for the same four fields. -/
theorem toList_encodeAddress (tau : Fin 32) (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) :
    (encodeAddress tau mu hi lo).toList
      = LeanXmss.fieldBytes (LeanXmss.tweakFields tau.val mu.val hi.val lo.toNat) := by
  -- The address is a concatenation of 4 + 3 + 1 + 8 bytes, which is its length constant.
  show (littleEndian 4 lo.toNat ++ littleEndian 3 hi.val ++ littleEndian 1 (tau.val + 32 * mu.val)
    ++ littleEndian 8 0 : Vector UInt8 (4 + 3 + 1 + 8)).toList = _
  simp only [Vector.toList_append, toList_littleEndian, LeanXmss.fieldBytes, LeanXmss.tweakFields,
    append_ofNat tau.val mu.val tau.isLt mu.isLt]
  rfl

/-! ## The addresses of a key -/

/-- `hi_l(a)`, as EthLib and as the proof compute it. -/
@[simp] theorem val_layerHi (layer : Layer) (a : Fin (2 ^ 23)) :
    (layerHi layer a).val = LeanXmss.layerHi (layerOf layer) a.val := rfl

theorem toList_addrChain (layer : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1)) :
    (addrChain layer e mu).toList
      = LeanXmss.fieldBytes (LeanXmss.hashDomainFields (.chain (layerOf layer) (keyOf e) mu)) := by
  rw [addrChain, toList_encodeAddress]
  rfl

theorem toList_addrLeaf (layer : Layer) (e : UInt32) :
    (addrLeaf layer e).toList
      = LeanXmss.fieldBytes (LeanXmss.hashDomainFields (.leaf (layerOf layer) (keyOf e))) := by
  rw [addrLeaf, toList_encodeAddress]
  rfl

theorem toList_addrMsg (layer : Layer) (e : UInt32) :
    (addrMsg layer e).toList
      = LeanXmss.fieldBytes (LeanXmss.hashDomainFields (.message (layerOf layer) (keyOf e))) := by
  rw [addrMsg, toList_encodeAddress]
  rfl

/-- A node's index is the low 32 bits of the proof's, which only those bits enter. -/
theorem toList_addrNode (layer : Layer) (level : Fin (LAYER_HEIGHT + 1)) (j : Nat) :
    (addrNode layer level (UInt32.ofNat j)).toList
      = LeanXmss.fieldBytes (LeanXmss.hashDomainFields (.node (layerOf layer) level.val j)) := by
  rw [addrNode, toList_encodeAddress]
  have hlo : BitVec.ofNat 32 (UInt32.ofNat j).toNat = BitVec.ofNat 32 j := by
    apply BitVec.eq_of_toNat_eq
    simp
  simp only [LeanXmss.hashDomainFields, LeanXmss.tweakFields, hlo]
  rfl

theorem toList_addrRnd (layer : Layer) (e : UInt32) :
    (addrRnd layer e).toList
      = LeanXmss.fieldBytes (LeanXmss.tweakFields 7 0 (LeanXmss.layerHi (layerOf layer) 0)
          (keyOf e)) := by
  rw [addrRnd, toList_encodeAddress]
  rfl

/-- A pair of chains as the proof writes it. -/
def pairOf (j : Fin (V / 2)) : LeanXmss.ChainPair :=
  ⟨j.val, by simpa [V, LeanXmss.numChains] using j.isLt⟩

theorem toList_addrPrf (layer : Layer) (e : UInt32) (j : Fin (V / 2)) :
    (addrPrf layer e j).toList
      = LeanXmss.fieldBytes
          (LeanXmss.keygenDomainFields (.ots (layerOf layer) (keyOf e) (pairOf j))) := by
  rw [addrPrf, toList_encodeAddress]
  rfl

theorem toList_addrParam :
    addrParam.toList = LeanXmss.fieldBytes (LeanXmss.keygenDomainFields .parameter) := by
  rw [addrParam, toList_encodeAddress]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability
