module

public import EthLib.Cryptography.Sphincs.Fors
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: leanSPHINCS addresses

Distinct call sites have distinct addresses.

- A big-endian word of `k` bytes determines its value below `256^k`.
- The 32 bytes of an address determine all six of its words.
- The eight address types have the eight codes 0 to 7, so two address types never share an address.
- Each address of a key determines its own arguments, the layer and the tree included.
- A FORS address determines its instance, its height and its tree index.
- A FORS tree index at height `z` determines its tree and its node, below `2^(10 - z)` nodes a tree.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## Big-endian words -/

/-- The bytes of `toByte(x, k)` are `x` written on `k` big-endian bytes. -/
@[simp] theorem toList_toByte (k x : Nat) : (toByte k x).toList = Base.natToBytes k x := by
  simp [toByte]

/-- Writing `x` on `k` bytes and reading it back gives `x mod 256^k`. -/
@[simp] theorem toInt_toByte (k x : Nat) : toInt (toByte k x) = x % 256 ^ k := by
  rw [toInt, toList_toByte, Base.bytesToNat_natToBytes]

/-- Reading `k` bytes and writing the value back on `k` bytes gives the same bytes. -/
@[simp] theorem toByte_toInt {k : Nat} (v : Vector UInt8 k) : toByte k (toInt v) = v := by
  apply Vector.toList_inj.mp
  have h := Base.natToBytes_bytesToNat v.toList
  rw [Vector.length_toList] at h
  rw [toList_toByte, toInt, h]

/-- `k` bytes hold a value below `256^k`. -/
theorem toInt_lt {k : Nat} (v : Vector UInt8 k) : toInt v < 256 ^ k := by
  have h := Base.bytesToNat_lt v.toList
  rwa [Vector.length_toList] at h

/-- Two values below `256^k` with the same `k` bytes are equal. -/
theorem toByte_inj {k x y : Nat} (hx : x < 256 ^ k) (hy : y < 256 ^ k)
    (h : toByte k x = toByte k y) : x = y := by
  have h := congrArg toInt h
  rwa [toInt_toByte, toInt_toByte, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h

/-- Writing a value on `k` bytes keeps only its value modulo `256^k`. -/
theorem toByte_mod (k x : Nat) : toByte k (x % 256 ^ k) = toByte k x := by
  rw [← toByte_toInt (toByte k x), toInt_toByte]

/-- A 32-bit word survives its four big-endian bytes. -/
theorem toByte_uint32_inj {x y : UInt32} (h : toByte 4 x.toNat = toByte 4 y.toNat) : x = y :=
  UInt32.toNat_inj.mp
    (toByte_inj (lt_of_lt_of_eq x.toNat_lt_size (by decide))
      (lt_of_lt_of_eq y.toNat_lt_size (by decide)) h)

/-- A 64-bit word survives its twelve big-endian bytes. -/
theorem toByte_uint64_inj {x y : UInt64} (h : toByte 12 x.toNat = toByte 12 y.toNat) : x = y :=
  UInt64.toNat_inj.mp
    (toByte_inj (Nat.lt_of_lt_of_le x.toNat_lt_size (by decide))
      (Nat.lt_of_lt_of_le y.toNat_lt_size (by decide)) h)

/-! ## The encoding is injective -/

/-- The 32 bytes of an address are its six words, each big-endian, the tree on 12 bytes. -/
theorem toList_encodeAdrs (layer : UInt32) (tree : UInt64) (type keyPair word2 word3 : UInt32) :
    (encodeAdrs layer tree type keyPair word2 word3).toList
      = Base.natToBytes 4 layer.toNat ++ Base.natToBytes 12 tree.toNat
        ++ Base.natToBytes 4 type.toNat ++ Base.natToBytes 4 keyPair.toNat
        ++ Base.natToBytes 4 word2.toNat ++ Base.natToBytes 4 word3.toNat := by
  -- The six words have 32 bytes in all, so the address is their concatenation.
  show (toByte 4 layer.toNat ++ toByte 12 tree.toNat ++ toByte 4 type.toNat
      ++ toByte 4 keyPair.toNat ++ toByte 4 word2.toNat ++ toByte 4 word3.toNat
      : Vector UInt8 (4 + 12 + 4 + 4 + 4 + 4)).toList = _
  simp only [Vector.toList_append, toList_toByte]

/-- The 32 bytes of an address determine all six of its words.

```text
    [ layer: 4 | tree: 12 | type: 4 | u_1: 4 | u_2: 4 | u_3: 4 ]
```
-/
theorem encodeAdrs_inj {layer layer' : UInt32} {tree tree' : UInt64}
    {type type' keyPair keyPair' word2 word2' word3 word3' : UInt32} :
    encodeAdrs layer tree type keyPair word2 word3
        = encodeAdrs layer' tree' type' keyPair' word2' word3' ↔
      layer = layer' ∧ tree = tree' ∧ type = type' ∧ keyPair = keyPair' ∧ word2 = word2' ∧
        word3 = word3' := by
  constructor
  · intro h
    -- Peel the words off from the last one, each of a fixed length.
    obtain ⟨h, h3⟩ := Vector.append_inj h
    obtain ⟨h, h2⟩ := Vector.append_inj h
    obtain ⟨h, hk⟩ := Vector.append_inj h
    obtain ⟨h, ht⟩ := Vector.append_inj h
    obtain ⟨hl, htree⟩ := Vector.append_inj h
    exact ⟨toByte_uint32_inj hl, toByte_uint64_inj htree, toByte_uint32_inj ht,
      toByte_uint32_inj hk, toByte_uint32_inj h2, toByte_uint32_inj h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-! ## Address types -/

/-- The eight address types have eight different codes. -/
theorem AdrsType.code_injective : Function.Injective AdrsType.code := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- Every type code is one of the words 0 to 7. -/
theorem AdrsType.toNat_code_lt (type : AdrsType) : type.code.toNat < 8 := by
  cases type <;> decide

/-- Every word from 0 to 7 is the code of an address type. -/
theorem AdrsType.exists_toNat_code {n : Nat} (h : n < 8) :
    ∃ type : AdrsType, type.code.toNat = n :=
  match n, h with
  | 0, _ => ⟨.wotsHash, rfl⟩
  | 1, _ => ⟨.wotsPk, rfl⟩
  | 2, _ => ⟨.tree, rfl⟩
  | 3, _ => ⟨.forsTree, rfl⟩
  | 4, _ => ⟨.forsRoots, rfl⟩
  | 5, _ => ⟨.wotsPrf, rfl⟩
  | 6, _ => ⟨.forsPrf, rfl⟩
  | 7, _ => ⟨.wotsEnc, rfl⟩
  | _ + 8, h => absurd h (by omega)

/-! ## Addresses of one key -/

/-- The three layers have three different numbers. -/
theorem Layer.toNat_injective : Function.Injective Layer.toNat := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- A layer's number is 0, 1 or 2. -/
theorem Layer.toNat_lt (layer : Layer) : layer.toNat < 3 := by
  cases layer <;> decide

/-- A number below `2^32` survives the trip through a 32-bit word. -/
theorem uint32_ofNat_inj {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (h : UInt32.ofNat x = UInt32.ofNat y) : x = y := by
  have := congrArg UInt32.toNat h
  rwa [UInt32.toNat_ofNat_of_lt' hx, UInt32.toNat_ofNat_of_lt' hy] at this

/-- A number below `2^64` survives the trip through a 64-bit word. -/
theorem uint64_ofNat_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64)
    (h : UInt64.ofNat x = UInt64.ofNat y) : x = y := by
  have := congrArg UInt64.toNat h
  rwa [UInt64.toNat_ofNat_of_lt' hx, UInt64.toNat_ofNat_of_lt' hy] at this

/-- An address determines its type and its layer, and each other value modulo its word's size.

The tree word holds the tree modulo `2^64`, and each 32-bit word its value modulo `2^32`. -/
theorem adrs_inj {type type' : AdrsType} {layer layer' : Layer}
    {tree tree' keyPair keyPair' word2 word2' word3 word3' : Nat}
    (h : adrs type layer tree keyPair word2 word3
      = adrs type' layer' tree' keyPair' word2' word3') :
    type = type' ∧ layer = layer' ∧ tree % 2 ^ 64 = tree' % 2 ^ 64 ∧
      keyPair % 2 ^ 32 = keyPair' % 2 ^ 32 ∧ word2 % 2 ^ 32 = word2' % 2 ^ 32 ∧
      word3 % 2 ^ 32 = word3' % 2 ^ 32 := by
  obtain ⟨hl, ht, htype, hk, h2, h3⟩ := encodeAdrs_inj.mp h
  -- A word read back is its value modulo the word's size.
  have word32 {x y : Nat} (h : UInt32.ofNat x = UInt32.ofNat y) : x % 2 ^ 32 = y % 2 ^ 32 := by
    simpa only [UInt32.toNat_ofNat'] using congrArg UInt32.toNat h
  have hlayer := word32 hl
  rw [Nat.mod_eq_of_lt (by have := layer.toNat_lt; omega),
    Nat.mod_eq_of_lt (by have := layer'.toNat_lt; omega)] at hlayer
  exact ⟨AdrsType.code_injective htype, Layer.toNat_injective hlayer,
    by simpa only [UInt64.toNat_ofNat'] using congrArg UInt64.toNat ht, word32 hk, word32 h2,
    word32 h3⟩

/-- Addresses whose types differ are different addresses, whatever their other fields. -/
theorem adrs_ne_of_type_ne {type type' : AdrsType} (layer layer' : Layer)
    (tree tree' keyPair keyPair' word2 word2' word3 word3' : Nat) (h : type ≠ type') :
    adrs type layer tree keyPair word2 word3 ≠ adrs type' layer' tree' keyPair' word2' word3' :=
  fun same => h (adrs_inj same).1

/-- A key whose tree and leaf fit their words: the tree below `2^64`, the leaf below `2^32`. -/
def OtsKey.Fits (key : OtsKey) : Prop :=
  key.tree < 2 ^ 64 ∧ key.leaf < 2 ^ 32

/-- The key of a layer on the way up from an index below `2^64` fits its words. -/
theorem OtsKey.fits_ofIndex (layer : Layer) {idx : Nat} (h : idx < 2 ^ 64) :
    (OtsKey.ofIndex layer idx).Fits := by
  refine ⟨Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) h, ?_⟩
  -- The leaf is below `2^h`, and every height is at most 10.
  have hleaf := Nat.mod_lt (idx >>> layer.below) (Nat.two_pow_pos layer.height)
  have hheight : 2 ^ layer.height ≤ 2 ^ 32 := by
    cases layer <;> simp only [Layer.height, LOWER_HEIGHT, TOP_HEIGHT] <;> decide
  exact Nat.lt_of_lt_of_le hleaf hheight

/-- Two key addresses with values that fit name the same type, key and last two words. -/
theorem keyAdrs_inj {type type' : AdrsType} {key key' : OtsKey} {word2 word2' word3 word3' : Nat}
    (hk : key.Fits) (hk' : key'.Fits) (h2 : word2 < 2 ^ 32) (h2' : word2' < 2 ^ 32)
    (h3 : word3 < 2 ^ 32) (h3' : word3' < 2 ^ 32)
    (h : keyAdrs type key word2 word3 = keyAdrs type' key' word2' word3') :
    type = type' ∧ key = key' ∧ word2 = word2' ∧ word3 = word3' := by
  obtain ⟨htype, hlayer, htree, hleaf, hw2, hw3⟩ := adrs_inj h
  rw [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hk'.1] at htree
  rw [Nat.mod_eq_of_lt hk.2, Nat.mod_eq_of_lt hk'.2] at hleaf
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h2'] at hw2
  rw [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h3'] at hw3
  -- The layer, the tree and the leaf rebuild the key.
  obtain ⟨l, t, e⟩ := key
  obtain ⟨l', t', e'⟩ := key'
  simp_all

/-! ## WOTS+C and the hypertree -/

/-- A chain index is below `2^32`. -/
private theorem chain_lt_two_pow (i : Fin V) : i.val < 2 ^ 32 :=
  Nat.lt_trans i.isLt (by decide)

/-- A chain-step address names its key, its chain and the position the step leaves. -/
theorem adrsChain_inj {key key' : OtsKey} {i i' : Fin V} {mu mu' : Fin (CHAIN_LENGTH - 1)}
    (hk : key.Fits) (hk' : key'.Fits) (h : adrsChain key i mu = adrsChain key' i' mu') :
    key = key' ∧ i = i' ∧ mu = mu' := by
  obtain ⟨-, hkey, hi, hmu⟩ := keyAdrs_inj hk hk' (chain_lt_two_pow i) (chain_lt_two_pow i')
    (Nat.lt_trans mu.isLt (by decide)) (Nat.lt_trans mu'.isLt (by decide)) h
  exact ⟨hkey, Fin.ext hi, Fin.ext hmu⟩

/-- A one-time key's leaf address names its key. -/
theorem adrsPk_inj {key key' : OtsKey} (hk : key.Fits) (hk' : key'.Fits)
    (h : adrsPk key = adrsPk key') : key = key' :=
  (keyAdrs_inj hk hk' (by decide) (by decide) (by decide) (by decide) h).2.1

/-- A chain-start address names its key and its chain. -/
theorem adrsPrf_inj {key key' : OtsKey} {i i' : Fin V} (hk : key.Fits) (hk' : key'.Fits)
    (h : adrsPrf key i = adrsPrf key' i') : key = key' ∧ i = i' := by
  obtain ⟨-, hkey, hi, -⟩ := keyAdrs_inj hk hk' (chain_lt_two_pow i) (chain_lt_two_pow i')
    (by decide) (by decide) h
  exact ⟨hkey, Fin.ext hi⟩

/-- An encoding address names its key. -/
theorem adrsEnc_inj {key key' : OtsKey} (hk : key.Fits) (hk' : key'.Fits)
    (h : adrsEnc key = adrsEnc key') : key = key' :=
  (keyAdrs_inj hk hk' (by decide) (by decide) (by decide) (by decide) h).2.1

/-- A node address names its layer, its tree, its height and its index, when they fit. -/
theorem adrsNode_inj {layer layer' : Layer} {tree tree' z z' j j' : Nat}
    (ht : tree < 2 ^ 64) (ht' : tree' < 2 ^ 64) (hz : z < 2 ^ 32) (hz' : z' < 2 ^ 32)
    (hj : j < 2 ^ 32) (hj' : j' < 2 ^ 32)
    (h : adrsNode layer tree z j = adrsNode layer' tree' z' j') :
    layer = layer' ∧ tree = tree' ∧ z = z' ∧ j = j' := by
  obtain ⟨-, hlayer, htree, -, hw2, hw3⟩ := adrs_inj h
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt ht'] at htree
  rw [Nat.mod_eq_of_lt hz, Nat.mod_eq_of_lt hz'] at hw2
  rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj'] at hw3
  exact ⟨hlayer, htree, hw2, hw3⟩

/-! ## FORS -/

/-- The bottom key of an index determines the index: its tree and its leaf hold all of its bits. -/
theorem OtsKey.ofIndex_bottom_injective : Function.Injective (OtsKey.ofIndex .bottom) := by
  intro idx idx' h
  have htree := congrArg OtsKey.tree h
  have hleaf := congrArg OtsKey.leaf h
  simp only [OtsKey.ofIndex, Layer.below, Layer.height, LOWER_HEIGHT, Nat.zero_add,
    Nat.shiftRight_eq_div_pow] at htree hleaf
  -- The index is `256 tree + leaf`.
  omega

/-- A FORS tree address names its instance, its height and its tree index, when they fit. -/
theorem adrsFors_inj {idx idx' z z' j j' : Nat} (hi : idx < 2 ^ 64) (hi' : idx' < 2 ^ 64)
    (hz : z < 2 ^ 32) (hz' : z' < 2 ^ 32) (hj : j < 2 ^ 32) (hj' : j' < 2 ^ 32)
    (h : adrsFors idx z j = adrsFors idx' z' j') : idx = idx' ∧ z = z' ∧ j = j' := by
  obtain ⟨-, hkey, hw2, hw3⟩ := keyAdrs_inj (OtsKey.fits_ofIndex .bottom hi)
    (OtsKey.fits_ofIndex .bottom hi') hz hz' hj hj' h
  exact ⟨OtsKey.ofIndex_bottom_injective hkey, hw2, hw3⟩

/-- A FORS public key address names its instance. -/
theorem adrsRoots_inj {idx idx' : Nat} (hi : idx < 2 ^ 64) (hi' : idx' < 2 ^ 64)
    (h : adrsRoots idx = adrsRoots idx') : idx = idx' :=
  OtsKey.ofIndex_bottom_injective (keyAdrs_inj (OtsKey.fits_ofIndex .bottom hi)
    (OtsKey.fits_ofIndex .bottom hi') (by decide) (by decide) (by decide) (by decide) h).2.1

/-- A FORS secret address names its instance and its tree index, when they fit. -/
theorem adrsFprf_inj {idx idx' j j' : Nat} (hi : idx < 2 ^ 64) (hi' : idx' < 2 ^ 64)
    (hj : j < 2 ^ 32) (hj' : j' < 2 ^ 32) (h : adrsFprf idx j = adrsFprf idx' j') :
    idx = idx' ∧ j = j' := by
  obtain ⟨-, hkey, -, hw3⟩ := keyAdrs_inj (OtsKey.fits_ofIndex .bottom hi)
    (OtsKey.fits_ofIndex .bottom hi') (by decide) (by decide) hj hj' h
  exact ⟨OtsKey.ofIndex_bottom_injective hkey, hw3⟩

/-- Node `j` of tree `kappa` at height `z` has a tree index below `24 * 2^(10 - z)`. -/
theorem forsTreeIndex_lt (kappa : Fin FORS_TREES) {z j : Nat} (hj : j < 2 ^ (FORS_HEIGHT - z)) :
    forsTreeIndex kappa z j < FORS_TREES * 2 ^ (FORS_HEIGHT - z) := by
  unfold forsTreeIndex
  -- Tree `kappa` holds the indices from `kappa 2^(10 - z)` on, and tree `kappa + 1` the next.
  have := Nat.mul_le_mul_right (2 ^ (FORS_HEIGHT - z)) (Nat.succ_le_of_lt kappa.isLt)
  rw [Nat.succ_mul] at this
  omega

/-- The tree index of a node below `2^(10 - z)` fits its 32-bit word. -/
theorem forsTreeIndex_lt_two_pow (kappa : Fin FORS_TREES) {z j : Nat}
    (hj : j < 2 ^ (FORS_HEIGHT - z)) : forsTreeIndex kappa z j < 2 ^ 32 := by
  -- The heights from `z` up leave at most `2^10` nodes a tree, and 24 trees fit in `2^32`.
  have hpow : 2 ^ (FORS_HEIGHT - z) ≤ 2 ^ FORS_HEIGHT := Nat.pow_le_pow_right (by decide) (by omega)
  exact Nat.lt_of_lt_of_le (forsTreeIndex_lt kappa hj)
    (Nat.le_trans (Nat.mul_le_mul_left FORS_TREES hpow) fors_tree_index_fits)

/-- At one height, a tree index determines its tree and its node, below `2^(10 - z)` nodes a tree.

Above that bound, node `2^(10 - z)` of one tree has the index of node 0 of the next. -/
theorem forsTreeIndex_inj {kappa kappa' : Fin FORS_TREES} {z j j' : Nat}
    (hj : j < 2 ^ (FORS_HEIGHT - z)) (hj' : j' < 2 ^ (FORS_HEIGHT - z))
    (h : forsTreeIndex kappa z j = forsTreeIndex kappa' z j') : kappa = kappa' ∧ j = j' := by
  unfold forsTreeIndex at h
  have hpos : 0 < 2 ^ (FORS_HEIGHT - z) := Nat.two_pow_pos _
  -- The tree is the quotient by `2^(10 - z)`, and the node the remainder.
  have hdiv := congrArg (· / 2 ^ (FORS_HEIGHT - z)) h
  have hmod := congrArg (· % 2 ^ (FORS_HEIGHT - z)) h
  simp only [Nat.mul_comm _ (2 ^ (FORS_HEIGHT - z)), Nat.mul_add_div hpos, Nat.mul_add_mod,
    Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj',
    Nat.add_zero] at hdiv hmod
  exact ⟨Fin.ext hdiv, hmod⟩

/-- A FORS node address names its instance, its height, its tree and its node.

The node must be below `2^(10 - z)`, the nodes of one tree at height `z`. -/
theorem adrsFors_forsTreeIndex_inj {idx idx' z z' j j' : Nat} {kappa kappa' : Fin FORS_TREES}
    (hi : idx < 2 ^ 64) (hi' : idx' < 2 ^ 64) (hz : z < 2 ^ 32) (hz' : z' < 2 ^ 32)
    (hj : j < 2 ^ (FORS_HEIGHT - z)) (hj' : j' < 2 ^ (FORS_HEIGHT - z'))
    (h : adrsFors idx z (forsTreeIndex kappa z j) = adrsFors idx' z' (forsTreeIndex kappa' z' j')) :
    idx = idx' ∧ z = z' ∧ kappa = kappa' ∧ j = j' := by
  obtain ⟨hidx, rfl, hindex⟩ := adrsFors_inj hi hi' hz hz'
    (forsTreeIndex_lt_two_pow kappa hj) (forsTreeIndex_lt_two_pow kappa' hj') h
  obtain ⟨hkappa, hnode⟩ := forsTreeIndex_inj hj hj' hindex
  exact ⟨hidx, rfl, hkappa, hnode⟩

/-- A FORS secret address names its instance, its tree and its leaf. -/
theorem adrsFprf_forsTreeIndex_inj {idx idx' s s' : Nat} {kappa kappa' : Fin FORS_TREES}
    (hi : idx < 2 ^ 64) (hi' : idx' < 2 ^ 64) (hs : s < 2 ^ FORS_HEIGHT)
    (hs' : s' < 2 ^ FORS_HEIGHT)
    (h : adrsFprf idx (forsTreeIndex kappa 0 s) = adrsFprf idx' (forsTreeIndex kappa' 0 s')) :
    idx = idx' ∧ kappa = kappa' ∧ s = s' := by
  obtain ⟨hidx, hindex⟩ := adrsFprf_inj hi hi' (forsTreeIndex_lt_two_pow kappa hs)
    (forsTreeIndex_lt_two_pow kappa' hs') h
  exact ⟨hidx, forsTreeIndex_inj hs hs' hindex⟩

end EthLib.Cryptography.Sphincs
