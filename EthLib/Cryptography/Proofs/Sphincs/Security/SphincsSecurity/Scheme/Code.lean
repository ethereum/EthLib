module

public import EthLib.Cryptography.Proofs.Sphincs.CodeSize
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Lemmas

/-!
# How many digests the target-sum code accepts

The counter search accepts a digest whose 64 two-bit digits sum to `T = 128`.

The number of such digests is the coefficient of `z^128` in `(1 + z + z^2 + z^3)^64`.

The model's digit words are the digit strings that the specification counts.

So their number is the code size that the specification computes.

This file shows that this number is at least `2^114`.
-/

@[expose] public section

open Finset

set_option maxRecDepth 100000

namespace SphincsSecurity.Completeness

variable [Params]

open TargetSum

omit [Params] in
theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

/-- The number of words with digit sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => TargetSum.sum x = s)).card

omit [Params] in
/-- `[z^128](1 + z + z^2 + z^3)^64`. -/
theorem codeCount_target : codeCount targetSum = 23195210617839120199658819909693679 :=
  -- A digit word of sum `T` is a digit string of sum `T`, which the specification counts.
  (EthLib.Cryptography.Wots.card_filter_sum_eq _ _ _).trans
    EthLib.Cryptography.Sphincs.card_digitStrings_code

omit [Params] in
theorem two_pow_le_codeCount : 2 ^ 114 ≤ codeCount targetSum := by
  rw [codeCount_target]
  decide

omit [Params] in
/-- A number with `n` base-`B` digits, each below `B`, is below `B^n`. -/
theorem sum_digits_lt (B : Nat) (hB : 0 < B) (v : Nat → Nat) (hv : ∀ j, v j < B) :
    ∀ n, ∑ j ∈ range n, v j * B ^ j < B ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have hle : v n * B ^ n ≤ (B - 1) * B ^ n :=
        Nat.mul_le_mul_right _ (by have := hv n; omega)
      have : B ^ n * B = (B - 1) * B ^ n + B ^ n := by
        cases B with
        | zero => omega
        | succ b => simp; ring
      omega

def digit (x : Encoding) (j : Nat) : Nat :=
  if h : j < numChains then (x ⟨j, h⟩).val else 0

omit [Params] in
theorem digit_lt (x : Encoding) (j : Nat) : digit x j < 4 := by
  unfold digit
  split
  · exact (x _).isLt
  · decide

/-- The base-4 position of the digit of chain `j`.

`base_2b` reverses the order of the four digits in each byte. -/
def digitSlot (j : Nat) : Nat := 4 * (j / 4) + 3 - j % 4

omit [Params] in
theorem digitSlot_digitSlot (j : Nat) : digitSlot (digitSlot j) = j := by
  unfold digitSlot
  omega

omit [Params] in
theorem digitSlot_lt {j : Nat} (h : j < numChains) : digitSlot j < numChains := by
  unfold digitSlot numChains at *
  omega

def packNat (x : Encoding) : Nat := ∑ j ∈ range numChains, digit x (digitSlot j) * 4 ^ j

def pack (x : Encoding) : Digest := BitVec.ofNat digestBits (packNat x)

omit [Params] in
theorem packNat_lt (x : Encoding) : packNat x < 2 ^ 128 := by
  exact sum_digits_lt 4 (by decide) (fun j => digit x (digitSlot j)) (fun j => digit_lt x _)
    numChains

omit [Params] in
theorem toNat_pack (x : Encoding) : (pack x).toNat = packNat x := by
  rw [pack, BitVec.toNat_ofNat, digestBits, Nat.mod_eq_of_lt (packNat_lt x)]

omit [Params] in
theorem encoding_val (d : Digest) (i : ChainIndex) :
    (digestEncoding d i).val = d.toNat / 2 ^ (digitOffset i) % 4 := by
  simp [digestEncoding, BitVec.extractLsb', winternitzBits, Nat.shiftRight_eq_div_pow]

omit [Params] in
theorem digestEncoding_pack (x : Encoding) : digestEncoding (pack x) = x := by
  funext i
  apply Fin.ext
  rw [encoding_val, toNat_pack]
  have hoff : digitOffset i = 2 * digitSlot i.val := by
    unfold digitOffset digitSlot winternitzBits
    omega
  have hp : (2 : Nat) ^ digitOffset i = 4 ^ digitSlot i.val := by
    rw [hoff, pow_mul]; norm_num
  rw [hp, packNat, digit_of_sum 4 (by decide) (fun j => digit x (digitSlot j))
    (fun j => digit_lt x _) numChains (digitSlot i.val) (digitSlot_lt i.isLt),
    digitSlot_digitSlot, digit, dite_eq_left i.isLt]

omit [Params] in
theorem decodeDigest_pack (x : Encoding) (hx : Valid x) : decodeDigest (pack x) = some x := by
  rw [decodeDigest, digestEncoding_pack, ite_eq_left hx]

omit [Params] in
/-- At least `2^114` of the `2^128` digests decode to a word of the code. -/
theorem two_pow_le_card_accepting :
    2 ^ 114 ≤ (Finset.univ.filter fun d : Digest => (decodeDigest d).isSome).card := by
  refine le_trans two_pow_le_codeCount ?_
  rw [codeCount]
  apply Finset.card_le_card_of_injOn pack
  · intro x hx
    have hvalid : Valid x := (Finset.mem_filter.mp hx).2
    simp [decodeDigest_pack x hvalid]
  · intro left _ right _ heq
    have h := congrArg digestEncoding heq
    simpa only [digestEncoding_pack] using h

omit [Params] in
/-- Two words of the code with `x_i <= y_i` for every `i` are equal.

So walking chains forward cannot turn one word of the code into another. -/
theorem encoding_antichain {x y : Encoding} (hx : Valid x) (hy : Valid y)
    (hle : ∀ i, (x i).val ≤ (y i).val) : x = y := by
  have hsum : TargetSum.sum x = TargetSum.sum y := hx.trans hy.symm
  funext i
  refine Fin.ext (le_antisymm (hle i) ?_)
  by_contra hnot
  have hstrict : (x i).val < (y i).val := by omega
  have : TargetSum.sum x < TargetSum.sum y :=
    Finset.sum_lt_sum (fun j _ => hle j) ⟨i, Finset.mem_univ i, hstrict⟩
  omega

omit [Params] in
/-- For a word of the code, the verifier walks `sum_i (3 - x_i) = 64` chain steps. -/
theorem verification_chain_steps (word : Encoding) (hword : Valid word) :
    (∑ i : ChainIndex, (chainLength - 1 - (word i).val)) = 64 := by
  have hle : ∀ i ∈ (Finset.univ : Finset ChainIndex), (word i).val ≤ chainLength - 1 :=
    fun i _ => Nat.le_of_lt_succ (word i).isLt
  rw [Finset.sum_tsub_distrib Finset.univ hle,
    show (∑ i : ChainIndex, (word i).val) = targetSum from hword]
  simp [chainLength, winternitzBits, numChains, targetSum]

end SphincsSecurity.Completeness
