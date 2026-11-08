module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Bytes

/-!
# Proofs: EthLib's addresses are the model's

Both write FIPS 205's address: eight big-endian words, of which the tree takes three.

```text
    [ layer: 4 | tree: 12 | type: 4 | key pair: 4 | chain or height: 4 | hash or index: 4 ]
```

So EthLib's address of a call has the 32 bytes of the model's address of the same call.

The model numbers the layers from the top, and the layer word counts them from the bottom.

EthLib's layers carry the layer word, so the model's layer `0` is EthLib's top layer.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants
open SphincsSecurity (fieldBytes tweakBytes tweakFields TweakFields)

/-! ## The encoding -/

/-- A 32-bit word written as a model field: only its value modulo `2^32` stays. -/
theorem ofNat_toNat_uint32 (x : Nat) :
    BitVec.ofNat 32 (UInt32.ofNat x).toNat = BitVec.ofNat 32 x := by
  apply BitVec.eq_of_toNat_eq
  simp

/-- EthLib's address encoding lists the bytes of the model's, for the same six words. -/
theorem toList_encodeAdrs_fieldBytes (layer : UInt32) (tree : UInt64)
    (type keyPair word2 word3 : UInt32) :
    (encodeAdrs layer tree type keyPair word2 word3).toList
      = fieldBytes (tweakFields type.toNat layer.toNat tree.toNat keyPair.toNat word2.toNat
          word3.toNat) := by
  -- The address is a concatenation of six words, its length constant.
  show (toByte 4 layer.toNat ++ toByte 12 tree.toNat ++ toByte 4 type.toNat
    ++ toByte 4 keyPair.toNat ++ toByte 4 word2.toNat ++ toByte 4 word3.toNat :
      Vector UInt8 (4 + 12 + 4 + 4 + 4 + 4)).toList = _
  simp only [Vector.toList_append, toList_toByte_bytesBE, fieldBytes, tweakFields,
    List.append_assoc]

/-- The address of a call of a key, for any type and words, is the model's. -/
theorem toList_adrs (type : AdrsType) (layer : Layer) (tree keyPair word2 word3 : Nat) :
    (adrs type layer tree keyPair word2 word3).toList
      = fieldBytes (tweakFields type.code.toNat layer.toNat (tree % 2 ^ 64) keyPair word2
          word3) := by
  rw [adrs, toList_encodeAdrs_fieldBytes]
  simp only [tweakFields, ofNat_toNat_uint32, UInt64.toNat_ofNat']

/-! ## Layers

The model's layer `0` is the top, and its layer word is `2` minus the layer. -/

/-- A layer of the model as EthLib's. -/
def layerOf (lay : SphincsSecurity.Layer) : Layer :=
  match lay.val with
  | 0 => .top
  | 1 => .middle
  | _ => .bottom

/-- EthLib's layer word is the model's. -/
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

/-- The address of a call in a tree of a layer, for any type and words, is the model's. -/
theorem toList_keyAdrs (type : AdrsType) (lay : SphincsSecurity.Layer)
    (tree : SphincsSecurity.TreeIndex) (leaf : SphincsSecurity.LeafIndex) (word2 word3 : Nat) :
    (keyAdrs type (keyOf lay tree leaf) word2 word3).toList
      = fieldBytes (SphincsSecurity.treeFields type.code.toNat lay tree leaf.val word2 word3) := by
  -- A tree of the model is below `2^26`, so its 64-bit word holds it.
  have htree : tree.val % 2 ^ 64 = tree.val :=
    Nat.mod_eq_of_lt (tree.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by decide)))
  rw [keyAdrs, toList_adrs, SphincsSecurity.treeFields, ← toNat_layerOf]
  simp only [keyOf, htree]

theorem toList_adrsPrf (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) (i : Fin V) :
    (adrsPrf (keyOf lay tree leaf) i).toList
      = fieldBytes (SphincsSecurity.keygenDomainFields (.ots lay tree leaf ⟨i.val, i.isLt⟩)) := by
  rw [adrsPrf, toList_keyAdrs]
  rfl

theorem toList_adrsChain (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) (i : Fin V) (mu : Fin (CHAIN_LENGTH - 1)) :
    (adrsChain (keyOf lay tree leaf) i mu).toList
      = tweakBytes (.chain lay tree leaf ⟨i.val, i.isLt⟩ ⟨mu.val, mu.isLt⟩) := by
  rw [adrsChain, toList_keyAdrs]
  rfl

theorem toList_adrsPk (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    (adrsPk (keyOf lay tree leaf)).toList = tweakBytes (.leaf lay tree leaf) := by
  rw [adrsPk, toList_keyAdrs]
  rfl

theorem toList_adrsEnc (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (leaf : SphincsSecurity.LeafIndex) :
    (adrsEnc (keyOf lay tree leaf)).toList = tweakBytes (.encoding lay tree leaf) := by
  rw [adrsEnc, toList_keyAdrs]
  rfl

/-- The node at height `z` and index `j` of a tree, for every height and index. -/
theorem toList_adrsNode (lay : SphincsSecurity.Layer) (tree : SphincsSecurity.TreeIndex)
    (z j : Nat) :
    (adrsNode (layerOf lay) tree.val z j).toList = tweakBytes (.node lay tree z j) := by
  have h := toList_keyAdrs .tree lay tree ⟨0, Nat.two_pow_pos _⟩ z j
  rw [keyAdrs] at h
  rw [adrsNode]
  exact h

/-! ## FORS

The FORS instance of an index sits at the bottom key of the index. -/

/-- A FORS tree of the model as EthLib's. -/
def treeOf (κ : SphincsSecurity.FTree) : Fin FORS_TREES := ⟨κ.val, κ.isLt⟩

/-- A FORS address of an instance, for any type and words, is the model's. -/
theorem toList_forsAdrs (type : AdrsType) (index : SphincsSecurity.Index) (z j : Nat) :
    (keyAdrs type (OtsKey.ofIndex .bottom index.val) z j).toList
      = fieldBytes (SphincsSecurity.forsFields type.code.toNat index z j) := by
  -- The bottom tree of an index is below `2^18`, so its 64-bit word holds it.
  have htree : index.val >>> 8 % 2 ^ 64 = index.val / 2 ^ 8 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt
      (index.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by decide))))
  rw [keyAdrs, toList_adrs]
  simp only [OtsKey.ofIndex, Layer.below, Layer.height, Nat.zero_add, LOWER_HEIGHT,
    Nat.shiftRight_zero]
  rw [htree]
  rfl

/-- In a tree of nodes `j < 2^(10 - z)` at height `z`, EthLib's tree index is the model's. -/
theorem forsTreeIndex_eq (κ : SphincsSecurity.FTree) (z j : Nat) (hj : j < 2 ^ (FORS_HEIGHT - z)) :
    forsTreeIndex (treeOf κ) z j = SphincsSecurity.forsTreeIndex κ z j := by
  have hj' : j < 2 ^ (SphincsSecurity.forsHeight - z) := hj
  simp only [forsTreeIndex, SphincsSecurity.forsTreeIndex, treeOf, hj', ↓reduceIte]
  rfl

theorem toList_adrsFprf (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree)
    (leaf : SphincsSecurity.FLeaf) :
    (adrsFprf index.val (forsTreeIndex (treeOf κ) 0 leaf.val)).toList
      = fieldBytes (SphincsSecurity.keygenDomainFields (.fors index κ leaf)) := by
  rw [adrsFprf, toList_forsAdrs, forsTreeIndex_eq κ 0 leaf.val leaf.isLt]
  rfl

theorem toList_adrsFors_leaf (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree)
    (leaf : SphincsSecurity.FLeaf) :
    (adrsFors index.val 0 (forsTreeIndex (treeOf κ) 0 leaf.val)).toList
      = tweakBytes (.forsLeaf index κ leaf) := by
  rw [adrsFors, toList_forsAdrs, forsTreeIndex_eq κ 0 leaf.val leaf.isLt]
  rfl

/-- A FORS node at height `level + 1`, which the model stores as `level`, below its width. -/
theorem toList_adrsFors_node (index : SphincsSecurity.Index) (κ : SphincsSecurity.FTree)
    (level : SphincsSecurity.FLevel) (node : SphincsSecurity.FLeaf)
    (hnode : node.val < 2 ^ (FORS_HEIGHT - (level.val + 1))) :
    (adrsFors index.val (level.val + 1) (forsTreeIndex (treeOf κ) (level.val + 1) node.val)).toList
      = tweakBytes (.forsNode index κ level node) := by
  rw [adrsFors, toList_forsAdrs, forsTreeIndex_eq κ _ node.val hnode]
  rfl

theorem toList_adrsRoots (index : SphincsSecurity.Index) :
    (adrsRoots index.val).toList = tweakBytes (.forsRoots index) := by
  rw [adrsRoots, toList_forsAdrs]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
