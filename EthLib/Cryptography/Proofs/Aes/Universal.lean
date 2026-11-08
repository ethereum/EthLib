module

public import EthLib.Cryptography.Aes.Gcm
public import EthLib.Cryptography.Proofs.Aes.GaloisField
public import VCVio.OracleComp.Constructions.SampleableType.Measure
import EthLib.Cryptography.Proofs.Aes.Field

/-!
# Proofs: GHASH is almost XOR universal

SP 800-38D §6.4 reads GHASH of blocks `X_1 ... X_m` as `X_1 H^m + ... + X_m H`.

`Proofs/Aes/Field.lean` proves that the residues form the field of `2^128` elements.

Take two different lists of `m` blocks, and a target block `c`.

The blocks `H` where the XOR of their two GHASH values is `c` are the roots of one polynomial.

That polynomial is not zero, and its degree is at most `m`.

A field has at most `m` roots of it, so a uniform key hits one with probability at most `m / 2^128`.

This is Lemma 1 of McGrew and Viega, INDOCRYPT 2004:

<https://eprint.iacr.org/2004/193>

A list of zero blocks in front does not change GHASH, so `[X]` and `[0, X]` agree for every key.

GCM avoids that.

It hashes the padded data, the padded ciphertext, and one block of both bit lengths (§7.1).

Under the 64-bit length bounds, that block records both lengths.

So two different pairs still give two different lists after the shorter one grows by zero blocks.

The same bound then applies, with `m` the longer of the two lists.

The bound is a uniform count over the hash subkey.

It is not a bound on tag forgery, and it says nothing about the cipher.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

open OracleComp ENNReal
open scoped Polynomial

/-! ## A uniform hash subkey -/

/-- There are `2^128` blocks of 16 bytes. -/
theorem card_block : Fintype.card Block = 2 ^ 128 := by
  rw [Fintype.card_congr (arrayVectorEquivFin UInt8 16), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  norm_num

/-! ## Zero blocks in front -/

/-- A zero block in front does not change GHASH, for any hash subkey `H`.

The first step of Algorithm 2 multiplies `(0 + 0) • H`, which is the zero block. -/
theorem ghash_zeroBlock_cons (H : Block) (xs : List Block) :
    ghash H (zeroBlock :: xs) = ghash H xs := by
  have h0 : mul (xorBlock zeroBlock zeroBlock) H = zeroBlock :=
    residue_injective (by rw [residue_mul, residue_xorBlock, residue_zeroBlock, add_zero, zero_mul])
  rw [ghash, ghash, List.foldl_cons, h0]

/-- Lists of different lengths `[x]` and `[0, x]` have the same GHASH for every key `H`. -/
theorem ghash_pair_zeroBlock_eq (H x : Block) :
    ghash H [zeroBlock, x] = ghash H [x] :=
  ghash_zeroBlock_cons H [x]

/-! ## The difference polynomial -/

section
open Polynomial

/-- The difference of two GHASH polynomials, plus the target block `c`.

Block `i` of each list, counted from 0, takes the power `m - i`.

The target takes the constant term. -/
noncomputable def ghashDiffPoly (A B : List Block) (c : Block) : (AdjoinRoot modulus)[X] :=
  (∑ i : Fin A.length,
      C (residue A[i] + residue (B.getD i.val zeroBlock)) *
        X ^ (A.length - i.val)) +
    C (residue c)

/-- The difference polynomial has degree at most the length of the lists. -/
theorem natDegree_ghashDiffPoly_le (A B : List Block) (c : Block) :
    (ghashDiffPoly A B c).natDegree ≤ A.length := by
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · refine le_trans (natDegree_sum_le _ _) ?_
    refine Finset.sup_le fun i _ => ?_
    exact le_trans (natDegree_C_mul_le _ _) (le_trans (natDegree_X_pow_le _) (by omega))
  · rw [natDegree_C]
    exact Nat.zero_le _

/-- The coefficient of `X^(m - i)` is the sum of the two residues at `i`.

It does not meet the constant term, since `m - i` is at least 1. -/
theorem coeff_ghashDiffPoly (A B : List Block) (c : Block) (i : Fin A.length) :
    (ghashDiffPoly A B c).coeff (A.length - i.val) =
      residue A[i] + residue (B.getD i.val zeroBlock) := by
  rw [ghashDiffPoly, coeff_add, finsetSum_coeff]
  have hi : ∀ j : Fin A.length, A.length - j.val = A.length - i.val → j = i := by
    intro j hj
    exact Fin.ext (by omega)
  rw [Finset.sum_eq_single i ?_ (fun h => absurd (Finset.mem_univ i) h)]
  · rw [coeff_C_mul, coeff_X_pow, ite_eq_left rfl, mul_one, coeff_C,
      ite_eq_right (by omega : A.length - i.val ≠ 0), add_zero]
  · intro j _ hji
    rw [coeff_C_mul, coeff_X_pow, ite_eq_right (fun h => hji (hi j h.symm)), mul_zero]

/-- Two residues sum to zero exactly when their blocks are equal. -/
theorem residue_add_eq_zero_iff (A B : Block) : residue A + residue B = 0 ↔ A = B := by
  have hself (x : Block) : residue x + residue x = 0 := by
    rw [← residue_xorBlock, ← residue_zeroBlock]
    congr 1
    apply blockToNat_injective
    rw [blockToNat_xorBlock, Nat.xor_self]
    rfl
  refine ⟨fun h => residue_injective ?_, fun h => h ▸ hself A⟩
  calc residue A
      = residue A + (residue B + residue B) := by rw [hself, add_zero]
    _ = (residue A + residue B) + residue B := (add_assoc _ _ _).symm
    _ = residue B := by rw [h, zero_add]

/-- Two different lists of one length give a difference polynomial that is not zero.

Some block differs, and its power has a nonzero coefficient. -/
theorem ghashDiffPoly_ne_zero {A B : List Block} (hne : A ≠ B) (hlen : A.length = B.length)
    (c : Block) : ghashDiffPoly A B c ≠ 0 := by
  have ⟨i, hi⟩ : ∃ i : Fin A.length, A[i] ≠ B.getD i.val zeroBlock := by
    by_contra h
    push Not at h
    refine hne (List.ext_getElem hlen fun i hiA hiB => ?_)
    have hget := h ⟨i, hiA⟩
    rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiB, Option.getD_some] at hget
  have hcoeff := coeff_ghashDiffPoly A B c i
  intro h0
  rw [h0, coeff_zero] at hcoeff
  exact hi ((residue_add_eq_zero_iff _ _).mp hcoeff.symm)

/-- XOR of the two GHASH values equals `c` exactly when the residue of `H` is a root. -/
theorem xorBlock_ghash_eq_iff (A B : List Block) (c H : Block) (hlen : A.length = B.length) :
    xorBlock (ghash H A) (ghash H B) = c ↔ (ghashDiffPoly A B c).eval (residue H) = 0 := by
  rw [← residue_add_eq_zero_iff, residue_xorBlock, residue_ghash, residue_ghash]
  have hsum :
      (∑ i : Fin A.length, residue A[i] * residue H ^ (A.length - i.val)) +
        (∑ i : Fin B.length, residue B[i] * residue H ^ (B.length - i.val)) =
        ∑ i : Fin A.length,
          (residue A[i] + residue (B.getD i.val zeroBlock)) * residue H ^ (A.length - i.val) := by
    have hA :
        (∑ i : Fin A.length, residue A[i] * residue H ^ (A.length - i.val)) =
          ∑ i ∈ Finset.range A.length,
            residue (A.getD i zeroBlock) * residue H ^ (A.length - i) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some,
        Fin.getElem_fin]
    have hB :
        (∑ i : Fin B.length, residue B[i] * residue H ^ (B.length - i.val)) =
          ∑ i ∈ Finset.range B.length,
            residue (B.getD i zeroBlock) * residue H ^ (B.length - i) := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt, Option.getD_some,
        Fin.getElem_fin]
    rw [hA, hB, ← hlen, ← Finset.sum_add_distrib, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [List.getD_eq_getElem?_getD (l := A), List.getElem?_eq_getElem i.isLt, Option.getD_some,
      Fin.getElem_fin, add_mul]
  rw [hsum, ghashDiffPoly, eval_add, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]

/-! ## The bound

The root count is stated over any field.

On the residues, the ring instance and the field instance give two semirings.

Matching them unfolds the modulus `u^128 + ...`. -/

/-- An injective map into a field hits the roots of a nonzero polynomial at most its degree times.
-/
theorem card_filter_eval_eq_zero_le {α F : Type*} [Fintype α] [Field F] {f : α → F}
    (hf : Function.Injective f) {P : F[X]} (hP : P ≠ 0) {d : Nat} (hd : P.natDegree ≤ d)
    [DecidablePred fun x : α => P.eval (f x) = 0] :
    (Finset.univ.filter fun x : α => P.eval (f x) = 0).card ≤ d := by
  classical
  let s := Finset.univ.filter fun x : α => P.eval (f x) = 0
  have hsub : s.image f ⊆ P.roots.toFinset := by
    intro r hr
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hr
    obtain ⟨x, hx, rfl⟩ := hr
    exact Multiset.mem_toFinset.mpr ((mem_roots hP).mpr hx)
  calc s.card
      = (s.image f).card := (Finset.card_image_of_injective s hf).symm
    _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := card_roots' P
    _ ≤ d := hd

/-- The keys that give the XOR collision are at most `m`.

Each is a root of the polynomial, and degree at most `m` allows at most `m` roots. -/
theorem card_ghash_xor_le {A B : List Block} (hne : A ≠ B) (hlen : A.length = B.length)
    (c : Block) :
    (Finset.univ.filter fun H : Block => xorBlock (ghash H A) (ghash H B) = c).card ≤
      A.length := by
  classical
  have heq : (Finset.univ.filter fun H : Block => xorBlock (ghash H A) (ghash H B) = c) =
      Finset.univ.filter fun H : Block => (ghashDiffPoly A B c).eval (residue H) = 0 := by
    ext H
    simp [xorBlock_ghash_eq_iff A B c H hlen]
  rw [heq]
  exact card_filter_eval_eq_zero_le residue_injective (ghashDiffPoly_ne_zero hne hlen c)
    (natDegree_ghashDiffPoly_le A B c)

end

/-- **GHASH is `m / 2^128`-almost XOR universal on equal-length block lists.**

This is Lemma 1 of McGrew and Viega, INDOCRYPT 2004, and the bound of SP 800-38D §6.4.

Take two different lists `A` and `B` of `m` blocks, and a target block `c`.

A uniform key `H` gives `xorBlock (ghash H A) (ghash H B) = c` with probability at most `m / 2^128`.
-/
theorem prEvent_xorBlock_ghash_eq_le {A B : List Block} (hne : A ≠ B)
    (hlen : A.length = B.length) (c : Block) :
    Pr{let H ← $ᵗ Block}[xorBlock (ghash H A) (ghash H B) = c] ≤
      (A.length : ℝ≥0∞) / 2 ^ 128 := by
  rw [SampleableType.prEvent_uniformSample, card_block, Nat.cast_pow, Nat.cast_ofNat]
  gcongr
  exact_mod_cast card_ghash_xor_le hne hlen c

/-! ## One block

On one block, GHASH is multiplication by the block.

So the XOR of two such values is multiplication by `x + x'`.

When the blocks differ, that multiplication is a bijection of the blocks. -/

/-- On one block, GHASH is the product of the block with the key. -/
theorem ghash_singleton (H x : Block) : ghash H [x] = mul x H := by
  have h0 : mul (xorBlock zeroBlock x) H = mul x H := by
    apply residue_injective
    rw [residue_mul, residue_xorBlock, residue_zeroBlock, zero_add, residue_mul]
  rw [ghash, List.foldl_cons, List.foldl_nil, h0]

/-- The XOR of two one-block GHASH values is the product of `x + x'` with the key. -/
theorem xorBlock_ghash_singleton (H x x' : Block) :
    xorBlock (ghash H [x]) (ghash H [x']) = mul (xorBlock x x') H := by
  apply residue_injective
  rw [residue_xorBlock, ghash_singleton, ghash_singleton, residue_mul, residue_mul,
    residue_mul, residue_xorBlock, add_mul]

/-- Multiplication by a block other than zero is a bijection of the blocks.

In the field, multiplication by its nonzero residue is injective, and the blocks are finite. -/
theorem mul_bijective_of_ne_zeroBlock {d : Block} (hd : d ≠ zeroBlock) :
    Function.Bijective (mul d) := by
  refine Finite.injective_iff_bijective.mp fun H H' h => ?_
  apply residue_injective
  have hres : residue d * residue H = residue d * residue H' := by
    simpa only [residue_mul] using congrArg residue h
  exact mul_left_cancel₀ (fun h0 => hd (residue_injective (h0.trans residue_zeroBlock.symm))) hres

/-- On distinct one-block inputs, the XOR collision probability is exactly `1 / 2^128`.

`H ↦ (x + x') • H` is a bijection of the blocks, so it hits `c` once. -/
theorem prEvent_xorBlock_ghash_singleton_eq {x x' : Block} (hne : x ≠ x') (c : Block) :
    Pr{let H ← $ᵗ Block}[xorBlock (ghash H [x]) (ghash H [x']) = c] = 1 / 2 ^ 128 := by
  have hd : xorBlock x x' ≠ zeroBlock := fun h =>
    hne ((residue_add_eq_zero_iff x x').mp (by
      rw [← residue_xorBlock, h, residue_zeroBlock]))
  simp_rw [xorBlock_ghash_singleton]
  rw [SampleableType.prEvent_uniformSample_comp_of_bijective (mul_bijective_of_ne_zeroBlock hd)
      (· = c),
    SampleableType.prEvent_uniformSample_eq_singleton, card_block, Nat.cast_pow, Nat.cast_ofNat,
    one_div]

/-! ## The padded input of GCM

GCM hashes the padded data, the padded ciphertext, and one block of both bit lengths (§7.1).

A list of zero blocks in front does not change GHASH, so padding alone cannot separate two inputs.

The length block can.

Under the 64-bit bounds, that block records both lengths.

So two different pairs stay different after the shorter list grows by zero blocks. -/

/-- Zero blocks in front do not change GHASH, for any hash subkey `H`. -/
theorem ghash_replicate_zeroBlock_append (H : Block) (k : Nat) (xs : List Block) :
    ghash H (List.replicate k zeroBlock ++ xs) = ghash H xs := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, List.cons_append, ghash_zeroBlock_cons, ih]

/-- A byte string of `n` bytes has `(n + 15) / 16` blocks. -/
theorem length_blocksOf (data : ByteArray) : (blocksOf data).length = (data.size + 15) / 16 := by
  simp [blocksOf]

/-- Two byte strings of one length with the same blocks are equal.

Each byte sits at row `k % 16` of block `k / 16`, and that block is completed with zeros. -/
theorem blocksOf_inj {a b : ByteArray} (hs : a.size = b.size) (h : blocksOf a = blocksOf b) :
    a = b := by
  apply ByteArray.ext
  apply Array.ext hs
  intro k hkA hkB
  have hk : k < a.size := hkA
  have hj : k / 16 < (a.size + 15) / 16 := by omega
  have hr : k % 16 < 16 := Nat.mod_lt _ (by decide)
  have hblock := congrArg (fun l : List Block => l[k / 16]?) h
  simp only [blocksOf, List.getElem?_map, List.getElem?_range, hj, hs ▸ hj,
    Option.map_some, Option.some.injEq] at hblock
  have hbyte := congrArg (fun v : Block => v[k % 16]) hblock
  simp only [Vector.getElem_ofFn, Nat.div_add_mod, Array.getD, hkA, hkB, ↓reduceDIte] at hbyte
  exact hbyte

/-- Under the 64-bit bounds, the length block records both lengths. -/
theorem blockOfNat_bitLengths_inj {aad c aad' c' : ByteArray}
    (haad : 8 * aad.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (haad' : 8 * aad'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (h : blockOfNat (8 * aad.size * 2 ^ 64 + 8 * c.size) =
      blockOfNat (8 * aad'.size * 2 ^ 64 + 8 * c'.size)) :
    aad.size = aad'.size ∧ c.size = c'.size := by
  have hlt (a x : ByteArray) (ha : 8 * a.size < 2 ^ 64) (hx : 8 * x.size < 2 ^ 64) :
      8 * a.size * 2 ^ 64 + 8 * x.size < 2 ^ 128 := by
    have : 8 * a.size * 2 ^ 64 + 8 * x.size < 2 ^ 64 * 2 ^ 64 := by omega
    simpa [Nat.pow_add] using this
  have hnat := congrArg blockToNat h
  rw [blockToNat_blockOfNat (hlt aad c haad hc),
    blockToNat_blockOfNat (hlt aad' c' haad' hc')] at hnat
  omega

/-- The length checks of §5.2.1.1 keep both bit lengths below `2^64`. -/
theorem bitLengths_lt_of_checkLengths {t : Nat} {iv text aad : ByteArray}
    (h : checkLengths t iv text aad = .ok ()) :
    8 * aad.size < 2 ^ 64 ∧ 8 * text.size < 2 ^ 64 := by
  have haad : 8 * aad.size ≤ 2 ^ 64 - 1 := by
    by_contra hbad
    unfold checkLengths at h
    simp only [hbad] at h
    repeat' split at h
    all_goals contradiction
  have htext : 8 * text.size ≤ 2 ^ 39 - 256 := by
    by_contra hbad
    unfold checkLengths at h
    simp only [hbad] at h
    repeat' split at h
    all_goals contradiction
  omega

/-- Two pairs with one padded input to GHASH are the same pair, under the 64-bit bounds. -/
theorem ghashInput_inj {aad c aad' c' : ByteArray}
    (haad : 8 * aad.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (haad' : 8 * aad'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (h : ghashInput aad c = ghashInput aad' c') : (aad, c) = (aad', c') := by
  simp only [ghashInput] at h
  obtain ⟨hbc, hlast⟩ := List.append_inj' h (by simp)
  have hlen := blockOfNat_bitLengths_inj haad hc haad' hc' (List.singleton_injective hlast)
  have hlenA : (blocksOf aad).length = (blocksOf aad').length := by
    simp [length_blocksOf, hlen.1]
  obtain ⟨hA, hC⟩ := List.append_inj hbc hlenA
  exact Prod.ext (blocksOf_inj hlen.1 hA) (blocksOf_inj hlen.2 hC)

/-- Two different pairs give two different padded lists after the shorter one grows by zero blocks.

The common length is the longer of the two lists, and both still end with their length block. -/
theorem ghashInput_pad_ne {aad c aad' c' : ByteArray}
    (haad : 8 * aad.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (haad' : 8 * aad'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (hne : (aad, c) ≠ (aad', c')) :
    List.replicate
        (max (ghashInput aad c).length (ghashInput aad' c').length - (ghashInput aad c).length)
        zeroBlock ++ ghashInput aad c ≠
      List.replicate
        (max (ghashInput aad c).length (ghashInput aad' c').length - (ghashInput aad' c').length)
        zeroBlock ++ ghashInput aad' c' := by
  intro heq
  apply hne
  have hexpand :
      (List.replicate
            (max (ghashInput aad c).length (ghashInput aad' c').length - (ghashInput aad c).length)
            zeroBlock ++ (blocksOf aad ++ blocksOf c)) ++
          [blockOfNat (8 * aad.size * 2 ^ 64 + 8 * c.size)] =
        (List.replicate
            (max (ghashInput aad c).length (ghashInput aad' c').length -
              (ghashInput aad' c').length)
            zeroBlock ++ (blocksOf aad' ++ blocksOf c')) ++
          [blockOfNat (8 * aad'.size * 2 ^ 64 + 8 * c'.size)] := by
    simpa only [ghashInput, List.append_assoc] using heq
  have hlast := (List.append_inj' hexpand (by simp)).2
  have hlen := blockOfNat_bitLengths_inj haad hc haad' hc' (List.singleton_injective hlast)
  have hm : (ghashInput aad c).length = (ghashInput aad' c').length := by
    simp [ghashInput, length_blocksOf, hlen.1, hlen.2]
  rw [hm, Nat.max_self, Nat.sub_self, List.replicate_zero, List.nil_append, List.nil_append] at heq
  exact ghashInput_inj haad hc haad' hc' heq

/-- **The bound for the padded input of GCM.**

Take two different pairs of additional data and ciphertext, each of bit length below `2^64`.

Let `m` be the longer of their two padded lists.

A uniform key `H` gives XOR `d` on their GHASH values with probability at most `m / 2^128`.

The length checks of §5.2.1.1 give the bit-length bounds, by `bitLengths_lt_of_checkLengths`.

The bound counts keys.

It is not a bound on tag forgery, and it says nothing about the cipher. -/
theorem prEvent_xorBlock_ghash_ghashInput_eq_le {aad c aad' c' : ByteArray}
    (haad : 8 * aad.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (haad' : 8 * aad'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (hne : (aad, c) ≠ (aad', c')) (d : Block) :
    Pr{let H ← $ᵗ Block}[
        xorBlock (ghash H (ghashInput aad c)) (ghash H (ghashInput aad' c')) = d] ≤
      ((max (ghashInput aad c).length (ghashInput aad' c').length : Nat) : ℝ≥0∞) / 2 ^ 128 := by
  let A := ghashInput aad c
  let B := ghashInput aad' c'
  let m := max A.length B.length
  let Ap := List.replicate (m - A.length) zeroBlock ++ A
  let Bp := List.replicate (m - B.length) zeroBlock ++ B
  have hAp : Ap.length = m := by
    simp only [Ap, List.length_append, List.length_replicate]
    omega
  have hlen : Ap.length = Bp.length := by
    simp only [Ap, Bp, List.length_append, List.length_replicate]
    omega
  have hneP : Ap ≠ Bp := ghashInput_pad_ne haad hc haad' hc' hne
  have hpr := prEvent_xorBlock_ghash_eq_le hneP hlen d
  simp only [Ap, Bp, ghash_replicate_zeroBlock_append] at hpr
  rwa [hAp] at hpr

end EthLib.Cryptography.Aes.Gcm
