module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Bytes

/-!
# Proofs: EthLib's addresses are the model's

The model writes an address as the bytes of six fields, from the type to `hi` and `lo`.

EthLib's address of the same call has the same 16 bytes.

The model numbers the layers from the top, and EthLib's address byte counts them from the bottom.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity (fieldBytes tweakBytes TweakFields)

/-! ## The encoding -/

/-- `LE_{8k}(z)`, listed, is the model's `k` bytes of `z` as a `8 k`-bit vector. -/
theorem toList_uintToBytes (k z : Nat) :
    (uintToBytes k z).toList = SphincsSecurity.bytesLE k (BitVec.ofNat (8 * k) z) := by
  rw [← ofBV_ofNat, toList_ofBV]
  rfl

/-- The byte that holds a type below 32 and a step below 8. -/
private theorem append_ofNat (tau mu : Nat) (htau : tau < 32) (hmu : mu < 8) :
    BitVec.ofNat 3 mu ++ BitVec.ofNat 5 tau = BitVec.ofNat (8 * 1) (tau + 32 * mu) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmu,
    show tau % 2 ^ 5 = tau from Nat.mod_eq_of_lt (by omega)]
  -- The step sits above the 5 bits of the type, so `or` is a sum.
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The model's fields of an address that EthLib encodes. -/
def addressFields (type : Nat) (step : Nat) (layer tree hi lo : Nat) : TweakFields :=
  ⟨BitVec.ofNat 5 type, BitVec.ofNat 3 step, BitVec.ofNat 8 layer, BitVec.ofNat 32 tree,
    BitVec.ofNat 24 hi, BitVec.ofNat 32 lo⟩

/-- EthLib's address encoding lists the bytes of the model's, for the same six fields. -/
theorem toList_encodeAddress (type : Fin 32) (step : Fin 8) (layer : Fin 256) (tree : UInt32)
    (hi : Fin (2 ^ 24)) (lo : UInt32) :
    (encodeAddress type step layer tree hi lo).toList
      = fieldBytes (addressFields type step layer tree.toNat hi lo.toNat) := by
  -- The address is a concatenation of 4 + 3 + 1 + 1 + 4 + 3 bytes, its length constant.
  show (uintToBytes 4 lo.toNat ++ uintToBytes 3 hi.val ++ uintToBytes 1 (type.val + 32 * step.val)
    ++ uintToBytes 1 layer.val ++ uintToBytes 4 tree.toNat ++ uintToBytes 3 0 :
      Vector UInt8 (4 + 3 + 1 + 1 + 4 + 3)).toList = _
  simp only [Vector.toList_append, toList_uintToBytes, fieldBytes, addressFields,
    append_ofNat type.val step.val type.isLt step.isLt]
  rfl

/-- Two lists of fields that agree modulo each field's width give the same bytes. -/
theorem addressFields_congr {a b c d e f a' b' c' d' e' f' : Nat} (ha : a % 2 ^ 5 = a' % 2 ^ 5)
    (hb : b % 2 ^ 3 = b' % 2 ^ 3) (hc : c % 2 ^ 8 = c' % 2 ^ 8) (hd : d % 2 ^ 32 = d' % 2 ^ 32)
    (he : e % 2 ^ 24 = e' % 2 ^ 24) (hf : f % 2 ^ 32 = f' % 2 ^ 32) :
    addressFields a b c d e f = addressFields a' b' c' d' e' f' := by
  simp only [addressFields, TweakFields.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.toNat_ofNat] <;> assumption

/-! ## Layers

The model's layer `0` is the top, and its layer byte is `2` minus the layer. -/

/-- A layer of the model as EthLib's. -/
def layerOf (lay : SphincsSecurity.Layer) : Layer :=
  match lay.val with
  | 0 => .top
  | 1 => .middle
  | _ => .bottom

/-- EthLib's layer byte is the model's. -/
theorem toNat_layerOf (lay : SphincsSecurity.Layer) :
    (layerOf lay).toNat = SphincsSecurity.layerByte lay := by
  obtain ⟨v, hv⟩ := lay
  change v < 3 at hv
  simp only [layerOf, SphincsSecurity.layerByte]
  interval_cases v <;> rfl

/-- EthLib's layer height is the model's. -/
theorem height_layerOf (lay : SphincsSecurity.Layer) :
    (layerOf lay).height = SphincsSecurity.layerHeight lay := by
  obtain ⟨v, hv⟩ := lay
  change v < 3 at hv
  simp only [layerOf, SphincsSecurity.layerHeight]
  interval_cases v <;> rfl

/-- The one-time key at a leaf of a tree of a layer of the model. -/
def keyOf (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) : OtsKey :=
  ⟨layerOf lay, tree.val, leaf.val⟩

/-! ## The hypertree -/

/-- The fields of a call in a tree of a layer, as the model writes them. -/
theorem treeFields_eq (tag step : Nat) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (hi lo : Nat) :
    SphincsSecurity.treeFields tag step lay tree hi lo
      = addressFields tag step (layerOf lay).toNat tree.val hi lo := by
  rw [toNat_layerOf]
  rfl

theorem toList_keyAddress (type : AddressType) (step : Fin 8) (key : OtsKey) (hi : Fin (2 ^ 24)) :
    (keyAddress type step key hi).toList
      = fieldBytes (addressFields type.code step key.layer.toNat key.tree hi key.leaf) := by
  rw [keyAddress, toList_encodeAddress]
  congr 1
  apply addressFields_congr <;> simp

theorem toList_addrPrf (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) (pair : SphincsSecurity.ChainPair) :
    (addrPrf (keyOf lay tree leaf) ⟨pair.val, pair.isLt⟩).toList
      = fieldBytes (SphincsSecurity.keygenDomainFields (.ots lay tree leaf pair)) := by
  rw [addrPrf, toList_keyAddress, SphincsSecurity.keygenDomainFields, treeFields_eq]
  rfl

theorem toList_addrChain (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) :
    (addrChain (keyOf lay tree leaf) i mu).toList
      = tweakBytes (.chain lay tree leaf ⟨i.val, i.isLt⟩ ⟨mu.val, mu.isLt⟩) := by
  rw [addrChain, toList_keyAddress, tweakBytes, SphincsSecurity.hashDomainFields, treeFields_eq]
  rfl

theorem toList_addrLeaf (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    (addrLeaf (keyOf lay tree leaf)).toList = tweakBytes (.leaf lay tree leaf) := by
  rw [addrLeaf, toList_keyAddress, tweakBytes, SphincsSecurity.hashDomainFields, treeFields_eq]
  rfl

theorem toList_addrEncoding (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    (addrEncoding (keyOf lay tree leaf)).toList = tweakBytes (.encoding lay tree leaf) := by
  rw [addrEncoding, toList_keyAddress, tweakBytes, SphincsSecurity.hashDomainFields, treeFields_eq]
  rfl

/-- The parent at level `level`, `1 <= level <= 10`, carries the level in `hi`. -/
theorem toList_addrNode (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (level j : Nat) (hlevel : level ≤ TOP_HEIGHT) :
    (addrNode (layerOf lay) tree.val (Fin.ofNat _ level) j).toList
      = tweakBytes (.node lay tree level j) := by
  rw [addrNode, toList_encodeAddress, tweakBytes, SphincsSecurity.hashDomainFields, treeFields_eq]
  congr 1
  apply addressFields_congr <;>
    simp [AddressType.code, Nat.mod_eq_of_lt (show level < TOP_HEIGHT + 1 by omega)]

/-! ## Calls outside the hypertree -/

theorem toList_addrParam :
    addrParam.toList = fieldBytes (SphincsSecurity.keygenDomainFields .parameter) := by
  rw [addrParam, toList_encodeAddress]
  rfl

theorem toList_addrRnd : addrRnd.toList = fieldBytes ⟨7#5, 0#3, 0#8, 0#32, 0#24, 0#32⟩ := by
  rw [addrRnd, toList_encodeAddress]
  rfl

theorem toList_addrMsg (call : SphincsSecurity.DigestCall) :
    (addrMsg ⟨call.val, call.isLt⟩).toList = tweakBytes (.message call) := by
  rw [addrMsg, toList_encodeAddress]
  rfl

/-! ## FORS -/

/-- A FORS tree of the model as EthLib's. -/
def treeOf (κ : SphincsSecurity.FTree) : Fin FORS_TREES := ⟨κ.val, κ.isLt⟩

theorem toList_addrForsPrf (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree)
    (pair : SphincsSecurity.FPair) :
    (addrForsPrf index.val (treeOf κ) ⟨pair.val, pair.isLt⟩).toList
      = fieldBytes (SphincsSecurity.keygenDomainFields (.fors index κ pair)) := by
  rw [addrForsPrf, toList_encodeAddress, SphincsSecurity.keygenDomainFields]
  congr 1
  apply addressFields_congr <;>
    simp [AddressType.code, forsHi, forsLeafPosition, SphincsSecurity.forsSlot, treeOf]

theorem toList_addrForsLeaf (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree)
    (leaf : SphincsSecurity.FLeaf) :
    (addrForsLeaf index.val (treeOf κ) leaf).toList = tweakBytes (.forsLeaf index κ leaf) := by
  unfold addrForsLeaf
  rw [toList_encodeAddress, tweakBytes, SphincsSecurity.hashDomainFields]
  congr 1
  apply addressFields_congr <;>
    simp [AddressType.code, forsHi, forsLeafPosition, SphincsSecurity.forsSlot, treeOf]
  rfl

/-- A FORS node at tree level `level + 1`, which the model stores as `level`. -/
theorem toList_addrForsNode (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree)
    (level : SphincsSecurity.FLevel) (node : SphincsSecurity.FLeaf) :
    (addrForsNode index.val (treeOf κ) (Fin.ofNat _ (level.val + 1)) (forsIndex node.val)).toList
      = tweakBytes (.forsNode index κ level node) := by
  rw [addrForsNode, toList_encodeAddress, tweakBytes, SphincsSecurity.hashDomainFields]
  have hl : level.val + 1 < 16 := by have := level.isLt; change _ < 10 at this; omega
  have hn : node.val % 2 ^ FORS_HEIGHT = node.val := Nat.mod_eq_of_lt node.isLt
  congr 1
  apply addressFields_congr <;>
    simp [AddressType.code, forsHi, forsNodePosition, forsIndex, SphincsSecurity.forsSlot,
      SphincsSecurity.nodePosition, treeOf, Nat.mod_eq_of_lt hl, hn]

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
