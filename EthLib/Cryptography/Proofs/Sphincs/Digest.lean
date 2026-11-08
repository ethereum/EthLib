module

public import EthLib.Cryptography.Sphincs.Digest
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: the leanSPHINCS message digest

FIPS 205 Algorithm 19 splits the 34-byte digest `D` into three fields of whole bytes.

```text
    [ md: 30 | tree: 3 | leaf: 1 ]
```

Read big-endian, `D` is a 272-bit integer, and the fields read disjoint runs of its bits.

```text
    toInt(D) / 2^32   = sum_{kappa < 24} s_kappa * 2^(10 (23 - kappa))
    toInt(D) mod 2^26 = idx = tree * 2^8 + leaf
```

- The 24 leaves `s_kappa` are the top 240 bits, 10 at a time, leaf 0 first.
- The index is the low 26 bits: the low 18 bits of the tree field, then the leaf byte.
- The top 6 bits of the tree field are not read.

So a uniform digest gives a uniform index and 24 independent uniform leaves.

The tree and leaf fields are FIPS 205's `idx_tree` and `idx_leaf`: the bottom key's tree and leaf.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-! ## The ranges of the fields -/

/-- The tree field has `h - h_0 = 18` bits. -/
theorem digestTree_lt (d : MessageDigest) : digestTree d < 2 ^ (HEIGHT - LOWER_HEIGHT) :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The leaf field has `h_0 = 8` bits. -/
theorem digestLeaf_lt (d : MessageDigest) : digestLeaf d < 2 ^ LOWER_HEIGHT :=
  Nat.mod_lt _ (Nat.two_pow_pos _)

/-- The digest's index has 26 bits. -/
theorem digestIndex_lt (d : MessageDigest) : digestIndex d < 2 ^ HEIGHT := by
  have htree := digestTree_lt d
  have hleaf := digestLeaf_lt d
  simp only [digestIndex, HEIGHT, LOWER_HEIGHT, TOP_HEIGHT] at htree hleaf ⊢
  omega

/-- The bottom key the index names is the tree field's tree and the leaf field's leaf. -/
theorem OtsKey.ofIndex_bottom_digestIndex (d : MessageDigest) :
    OtsKey.ofIndex .bottom (digestIndex d) = ⟨.bottom, digestTree d, digestLeaf d⟩ := by
  have hleaf := digestLeaf_lt d
  simp only [OtsKey.ofIndex, Layer.below, Layer.height, digestIndex, Nat.shiftRight_eq_div_pow,
    LOWER_HEIGHT] at hleaf ⊢
  -- `tree * 2^8 + leaf` with `leaf < 2^8` splits back into `tree` and `leaf`.
  simp only [Nat.zero_add, Nat.pow_zero, Nat.div_one, OtsKey.mk.injEq, true_and]
  omega

/-! ## Fields of bits -/

/-- A field of one more bit doubles the field and adds the next bit. -/
theorem msbField_succ {k : Nat} (x : Vector UInt8 k) (offset width : Nat) :
    msbField x offset (width + 1) = 2 * msbField x offset width + msbBit x (offset + width) := by
  simp only [msbField, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- A field of `a + b` bits is its first `a` bits, shifted by `b`, then its last `b` bits. -/
theorem msbField_add {k : Nat} (x : Vector UInt8 k) (offset a b : Nat) :
    msbField x offset (a + b) = msbField x offset a * 2 ^ b + msbField x (offset + a) b := by
  induction b with
  | zero => simp [msbField]
  | succ b ih =>
    rw [← Nat.add_assoc, msbField_succ, ih, msbField_succ, Nat.pow_succ, ← Nat.mul_assoc,
      Nat.add_assoc offset a b]
    omega

/-- Two folds over `0, ..., w - 1` agree when their steps agree there. -/
private theorem foldl_range_congr {f g : Nat → Nat → Nat} (w : Nat)
    (h : ∀ v t, t < w → f v t = g v t) :
    (List.range w).foldl f 0 = (List.range w).foldl g 0 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih fun v t ht => h v t (by omega), h _ w (by omega)]

/-- Every number below 256 is its 8 bits, read most significant first. -/
private theorem byte_msb_bits : ∀ n < 256,
    (List.range 8).foldl (fun v t => 2 * v + (n >>> (7 - t)) % 2) 0 = n := by
  decide +kernel

/-- The 8 bits from bit `8j` are byte `j`, or 0 past the end. -/
theorem msbField_byte {k : Nat} (x : Vector UInt8 k) (j : Nat) :
    msbField x (8 * j) 8 = ((x[j]?).getD 0).toNat := by
  -- Bit `8j + t` of the string is bit `7 - t` of byte `j`.
  have hbit : ∀ v t, t < 8 → 2 * v + msbBit x (8 * j + t)
      = 2 * v + (((x[j]?).getD 0).toNat >>> (7 - t)) % 2 := by
    intro v t ht
    rw [msbBit, show (8 * j + t) / 8 = j by omega, show (8 * j + t) % 8 = t by omega]
  rw [msbField, foldl_range_congr 8 hbit]
  exact byte_msb_bits _ (UInt8.toNat_lt _)

/-- The first `8n` bits of a byte string are its first `n` bytes, read big-endian. -/
theorem msbField_eq_bytesToNat {k : Nat} (x : Vector UInt8 k) :
    ∀ n, n ≤ k → msbField x 0 (8 * n) = EthLib.Base.bytesToNat (x.toList.take n)
  | 0, _ => rfl
  | n + 1, hn => by
    -- One more byte shifts the bytes read by 8 bits and adds itself.
    rw [Nat.mul_succ, msbField_add, msbField_eq_bytesToNat x n (by omega), Nat.zero_add,
      msbField_byte, List.take_add_one, EthLib.Base.bytesToNat_append, Vector.getElem?_toList,
      Vector.getElem?_eq_getElem (by omega)]
    simp [EthLib.Base.bytesToNat]

/-- A sum scaled by `c` is the sum of its terms scaled by `c`. -/
private theorem sum_map_mul_right (l : List Nat) (g : Nat → Nat) (c : Nat) :
    (l.map fun i => g i * c).sum = (l.map g).sum * c := by
  induction l with
  | nil => simp
  | cons i l ih => simp only [List.map_cons, List.sum_cons, ih, Nat.add_mul]

/-- A field of `n` blocks of `a` bits is the sum of the blocks, block 0 on top. -/
theorem msbField_mul {k : Nat} (x : Vector UInt8 k) (offset a : Nat) : ∀ n,
    msbField x offset (a * n)
      = ((List.range n).map fun i => msbField x (offset + a * i) a * 2 ^ (a * (n - 1 - i))).sum
  | 0 => by simp [msbField]
  | n + 1 => by
    -- Block `n` comes last, below the `n` blocks before it.
    rw [Nat.mul_succ, msbField_add, msbField_mul x offset a n, List.range_succ, List.map_append,
      List.sum_append_nat, List.map_singleton, List.sum_singleton, Nat.add_sub_cancel,
      Nat.sub_self, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, ← sum_map_mul_right]
    refine congrArg (· + _) (congrArg List.sum (List.map_congr_left fun i hi => ?_))
    -- Each earlier block moves up by `a` bits.
    rw [List.mem_range] at hi
    rw [Nat.mul_assoc, ← Nat.pow_add, ← Nat.mul_succ]
    exact congrArg (fun e => msbField x (offset + a * i) a * 2 ^ (a * e)) (by omega)

/-! ## The digest's fields -/

/-- The 24 leaves fill `md`: its 30 bytes, read big-endian, are the leaves, leaf 0 on top. -/
theorem digestLeaves_fill_md (d : MessageDigest) :
    EthLib.Base.bytesToNat (d.toList.take MD_BYTES)
      = ((List.finRange FORS_TREES).map fun kappa : Fin FORS_TREES =>
          ((digestLeaves d)[kappa] : Nat)
            * 2 ^ (FORS_HEIGHT * (FORS_TREES - 1 - kappa.val))).sum := by
  rw [← msbField_eq_bytesToNat d MD_BYTES (by decide), ← fors_leaves_fill_md,
    Nat.mul_comm FORS_TREES, msbField_mul]
  refine congrArg List.sum (List.ext_getElem (by simp) fun i _ _ => ?_)
  simp [digestLeaves]

/-- The digest read big-endian: `md` on top of the 4 bytes of the tree and leaf fields. -/
theorem toInt_digest (d : MessageDigest) :
    toInt d = EthLib.Base.bytesToNat (d.toList.take MD_BYTES) * 2 ^ 32
      + EthLib.Base.bytesToNat ((d.toList.drop MD_BYTES).take TREE_INDEX_BYTES) * 2 ^ 8
      + EthLib.Base.bytesToNat
          ((d.toList.drop (MD_BYTES + TREE_INDEX_BYTES)).take LEAF_INDEX_BYTES) := by
  have hlength : d.toList.length = 34 := by
    rw [Vector.length_toList]
    exact digest_bytes_eq.2.2.2
  rw [toInt]
  -- From here on the digest is a list of 34 bytes.
  generalize d.toList = l at hlength ⊢
  obtain ⟨hmd, htree, hleaf, -⟩ := digest_bytes_eq
  rw [hmd, htree, hleaf]
  -- Cut the list after byte 30 and after byte 33.
  have hsplit : l = l.take 30 ++ ((l.drop 30).take 3 ++ (l.drop (30 + 3)).take 1) := by
    rw [List.take_of_length_le (l := l.drop (30 + 3)) (by simp [hlength]), ← List.drop_drop,
      List.take_append_drop, List.take_append_drop]
  have hrest : ((l.drop 30).take 3 ++ (l.drop (30 + 3)).take 1).length = 4 := by
    simp [hlength]
  have hlast : ((l.drop (30 + 3)).take 1).length = 1 := by
    simp [hlength]
  rw [congrArg EthLib.Base.bytesToNat hsplit, EthLib.Base.bytesToNat_append,
    EthLib.Base.bytesToNat_append, hrest, hlast]
  omega

/-- The tree field has 3 bytes. -/
theorem length_treeBytes (d : MessageDigest) :
    ((d.toList.drop MD_BYTES).take TREE_INDEX_BYTES).length = TREE_INDEX_BYTES := by
  simp only [List.length_take, List.length_drop, Vector.length_toList]
  decide

/-- The leaf field has 1 byte. -/
theorem length_leafBytes (d : MessageDigest) :
    ((d.toList.drop (MD_BYTES + TREE_INDEX_BYTES)).take LEAF_INDEX_BYTES).length
      = LEAF_INDEX_BYTES := by
  simp only [List.length_take, List.length_drop, Vector.length_toList]
  decide

/-- The digest, read big-endian, is its 24 leaves on top and its index at the bottom.

```text
    toInt(D) / 2^32   = sum_{kappa < 24} s_kappa * 2^(10 (23 - kappa))
    toInt(D) mod 2^26 = idx
```

The 6 bits between the two are not read. -/
theorem digest_fields (d : MessageDigest) :
    toInt d / 2 ^ (8 * (TREE_INDEX_BYTES + LEAF_INDEX_BYTES))
        = ((List.finRange FORS_TREES).map fun kappa : Fin FORS_TREES =>
            ((digestLeaves d)[kappa] : Nat)
              * 2 ^ (FORS_HEIGHT * (FORS_TREES - 1 - kappa.val))).sum ∧
      toInt d % 2 ^ HEIGHT = digestIndex d := by
  rw [← digestLeaves_fill_md, toInt_digest, digestIndex, digestTree, digestLeaf]
  -- The tree field is below `2^24`, and the leaf field below `2^8`.
  have htree := EthLib.Base.bytesToNat_lt ((d.toList.drop MD_BYTES).take TREE_INDEX_BYTES)
  have hleaf := EthLib.Base.bytesToNat_lt
    ((d.toList.drop (MD_BYTES + TREE_INDEX_BYTES)).take LEAF_INDEX_BYTES)
  rw [length_treeBytes] at htree
  rw [length_leafBytes] at hleaf
  generalize EthLib.Base.bytesToNat (d.toList.take MD_BYTES) = a
  generalize EthLib.Base.bytesToNat ((d.toList.drop MD_BYTES).take TREE_INDEX_BYTES) = b at htree ⊢
  generalize EthLib.Base.bytesToNat
    ((d.toList.drop (MD_BYTES + TREE_INDEX_BYTES)).take LEAF_INDEX_BYTES) = c at hleaf ⊢
  simp only [TREE_INDEX_BYTES, LEAF_INDEX_BYTES, HEIGHT, TOP_HEIGHT, LOWER_HEIGHT] at htree hleaf ⊢
  omega

/-- Two digests with the same index and the same leaves agree on every bit those fields read. -/
theorem digest_fields_inj {d d' : MessageDigest} (hidx : digestIndex d = digestIndex d')
    (hleaves : digestLeaves d = digestLeaves d') :
    toInt d / 2 ^ (8 * (TREE_INDEX_BYTES + LEAF_INDEX_BYTES))
        = toInt d' / 2 ^ (8 * (TREE_INDEX_BYTES + LEAF_INDEX_BYTES)) ∧
      toInt d % 2 ^ HEIGHT = toInt d' % 2 ^ HEIGHT := by
  rw [(digest_fields d).1, (digest_fields d).2, (digest_fields d').1, (digest_fields d').2, hidx,
    hleaves]
  exact ⟨rfl, rfl⟩

end EthLib.Cryptography.Sphincs
