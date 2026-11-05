module

public import EthLib.Base.Proofs.LittleEndian
public import Mathlib.Tactic
public import VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Proofs: target-sum codes of digit vectors

A target-sum code holds the digit vectors whose digits sum to a fixed target.

leanXMSS and leanSPHINCS both encode a digest into such a code, with other lengths and targets.

The facts here hold for every length, digit range and target.

- A number is the sum of its base-`b` digits, weighted by powers of `b`.
- A 16-byte digest is its 64 base-4 digits, and every digit string is the digits of one digest.
- Two distinct vectors with equal digit sums are incomparable: each has a digit below the other's.
- A dynamic program counts the digit strings with a given sum.
-/

@[expose] public section

namespace EthLib.Cryptography.Wots

open EthLib.Base (bytesToUint)

/-! ## Base-`b` digits -/

/-- The low `k` base-`b` digits of a number reconstruct it modulo `b ^ k`. -/
theorem sum_base_digits_eq_mod (b n : Nat) : ∀ k : Nat,
    ∑ r ∈ Finset.range k, n / b ^ r % b * b ^ r = n % b ^ k := by
  intro k
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    -- One more digit is one more factor of the base in the modulus.
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ring

/-- The 64 base-4 digits of a 16-byte digest, read as one little-endian number. -/
def digits4 (d : Vector UInt8 16) : Vector (Fin 4) 64 :=
  Vector.ofFn fun i => ⟨bytesToUint d / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩

/-- There are `2^128` digests of 16 bytes. -/
theorem card_bytes16 : Fintype.card (Vector UInt8 16) = 2 ^ 128 := by
  rw [Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  norm_num

/-- A digest is the base-4 number its 64 digits spell. -/
theorem bytesToUint_eq_sum_digits4 (d : Vector UInt8 16) :
    bytesToUint d = ∑ i : Fin 64, ((digits4 d)[i] : ℕ) * 4 ^ i.val := by
  have hlt : bytesToUint d < 4 ^ 64 := by
    have := Base.bytesToUint_lt d
    simpa using this
  have hall := sum_base_digits_eq_mod 4 (bytesToUint d) 64
  rw [Nat.mod_eq_of_lt hlt] at hall
  rw [← hall, ← Fin.sum_univ_eq_sum_range (fun r => bytesToUint d / 4 ^ r % 4 * 4 ^ r)]
  exact Finset.sum_congr rfl fun i _ => by simp [digits4]

/-- Every string of 64 base-4 digits is the digits of exactly one 16-byte digest. -/
theorem digits4_bijective : Function.Bijective digits4 := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun d d' h => ?_, ?_⟩
  · have : bytesToUint d = bytesToUint d' := by
      rw [bytesToUint_eq_sum_digits4 d, bytesToUint_eq_sum_digits4 d', h]
    rw [← Base.uintToBytes_bytesToUint d, ← Base.uintToBytes_bytesToUint d', this]
  · rw [card_bytes16, Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin]
    norm_num

/-! ## Incomparability

A signature reveals chain `i` at position `x_i`.

So a signature for one codeword reaches another only if that one dominates it.

A constant digit sum rules that out. -/

/-- Pointwise domination with equal sums forces equality. -/
theorem eq_of_le_of_sum_eq {n k : Nat} {x y : Vector (Fin k) n}
    (hle : ∀ i : Fin n, (x[i] : Nat) ≤ (y[i] : Nat))
    (hsum : ∑ i : Fin n, (x[i] : Nat) = ∑ i : Fin n, (y[i] : Nat)) : x = y := by
  -- Equal sums of dominated terms force every term to be equal.
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).mp hsum
  exact Vector.ext fun i hi => Fin.val_inj.mp (heq ⟨i, hi⟩ (Finset.mem_univ _))

/-- Two distinct digit vectors with equal sums are incomparable.

Each has a digit below the other's. -/
theorem incomparable_of_sum_eq {n k : Nat} {x y : Vector (Fin k) n}
    (hsum : ∑ i : Fin n, (x[i] : Nat) = ∑ i : Fin n, (y[i] : Nat)) (hne : x ≠ y) :
    (∃ i : Fin n, (x[i] : Nat) < (y[i] : Nat)) ∧ (∃ i : Fin n, (y[i] : Nat) < (x[i] : Nat)) := by
  constructor
  -- Were one never to exceed the other, equal sums would make them equal.
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno hsum.symm).symm
  · by_contra hno
    simp only [not_exists, Nat.not_lt] at hno
    exact hne (eq_of_le_of_sum_eq hno hsum)

/-! ## Counting digit strings -/

/-- Strings of `n` digits below `k` that sum to `s`. -/
abbrev DigitStrings (n k s : ℕ) := {x : Fin n → Fin k // ∑ i, (x i : ℕ) = s}

/-- Only the empty string has no digits, and it sums to 0. -/
theorem card_digitStrings_zero (k s : ℕ) :
    Fintype.card (DigitStrings 0 k s) = if s = 0 then 1 else 0 := by
  split <;> rename_i h <;> simp [DigitStrings, Fintype.card_subtype, h, eq_comm]

/-- Fixing the first digit `d` leaves the rest to sum to `s - d`. -/
theorem card_digitStrings_succ (n k s : ℕ) :
    Fintype.card (DigitStrings (n + 1) k s)
      = ∑ d ∈ Finset.range k,
          if d ≤ s then Fintype.card (DigitStrings n k (s - d)) else 0 := by
  -- Split a string into its first digit and the rest.
  let e : DigitStrings (n + 1) k s
      ≃ Σ d : Fin k, {y : Fin n → Fin k // (d : ℕ) + ∑ i, (y i : ℕ) = s} :=
    { toFun := fun x => ⟨x.1 0, Fin.tail x.1, by
        have h := x.2
        rw [Fin.sum_univ_succ] at h
        exact h⟩
      invFun := fun p => ⟨Fin.cons p.1 p.2.1, by
        rw [Fin.sum_univ_succ]; simpa using p.2.2⟩
      left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma,
    ← Fin.sum_univ_eq_sum_range (fun d =>
      if d ≤ s then Fintype.card (DigitStrings n k (s - d)) else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  split
  -- A first digit up to `s` leaves exactly `s - d` for the rest.
  · rename_i hd
    exact Fintype.card_congr (Equiv.subtypeEquivRight fun y => by omega)
  -- A first digit above `s` overshoots on its own.
  · rename_i hd
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun y => by have := y.2; omega⟩

/-! ## The same count by dynamic programming

Row `n` lists the counts for length `n`, one entry per sum up to a bound.

Each row is the previous one, added to itself shifted by every digit. -/

/-- A row, added to itself shifted by each of the first `d` digits. -/
def shiftAdd (r : List ℕ) : ℕ → List ℕ
  | 0 => List.replicate r.length 0
  | d + 1 => List.zipWith (· + ·) (shiftAdd r d) (List.replicate d 0 ++ r)

/-- Counts of `n`-digit strings with digits below `k`, for each sum. -/
def countRow (k bound : ℕ) : ℕ → List ℕ
  | 0 => 1 :: List.replicate bound 0
  | n + 1 => shiftAdd (countRow k bound n) k

/-- Adding two rows adds their entries, wherever both have one. -/
theorem getD_zipWith_add {a b : List ℕ} {s : ℕ} (ha : s < a.length)
    (hb : s < b.length) :
    (List.zipWith (· + ·) a b).getD s 0 = a.getD s 0 + b.getD s 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_zipWith,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb]

/-- Shifting a row by `d` puts `d` zeros in front of it. -/
theorem getD_shift (r : List ℕ) (d s : ℕ) :
    (List.replicate d 0 ++ r).getD s 0
      = if d ≤ s then r.getD (s - d) 0 else 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append,
    List.length_replicate, List.getElem?_replicate]
  -- Below the shift the entry is a padding zero, above it a row entry.
  split <;> split <;> first | omega | simp_all

/-- Shifting keeps the length, and entry `s` gathers one term per digit. -/
theorem shiftAdd_spec (r : List ℕ) :
    ∀ d, (shiftAdd r d).length = r.length ∧
      ∀ s < r.length, (shiftAdd r d).getD s 0
        = ∑ j ∈ Finset.range d, if j ≤ s then r.getD (s - j) 0 else 0 := by
  intro d
  induction d with
  | zero =>
    refine ⟨by simp [shiftAdd], fun s hs => ?_⟩
    simp [shiftAdd, List.getD_eq_getElem?_getD, hs]
  | succ d ih =>
    obtain ⟨hlen, hget⟩ := ih
    refine ⟨by simp [shiftAdd, hlen], fun s hs => ?_⟩
    -- Both rows have entry `s`, so the sum has it too.
    rw [shiftAdd, getD_zipWith_add (by omega) (by simp; omega), hget s hs,
      getD_shift, Finset.sum_range_succ]

/-- Every row has one entry per sum, from 0 to the bound. -/
theorem countRow_length (k bound n : ℕ) :
    (countRow k bound n).length = bound + 1 := by
  induction n with
  | zero => simp [countRow]
  | succ n ih => rw [countRow, (shiftAdd_spec _ k).1, ih]

/-- The dynamic program counts the digit strings. -/
theorem countRow_eq_card (k bound : ℕ) :
    ∀ n, ∀ s ≤ bound,
      (countRow k bound n).getD s 0 = Fintype.card (DigitStrings n k s) := by
  intro n
  induction n with
  | zero =>
    intro s hs
    rw [card_digitStrings_zero]
    rcases s with _ | s <;> simp [countRow, List.getD_eq_getElem?_getD]
    -- Entries past the first are the zeros the row starts with.
    rw [List.getElem?_replicate]
    split <;> simp
  | succ n ih =>
    intro s hs
    rw [countRow, (shiftAdd_spec _ k).2 s (by rw [countRow_length]; omega),
      card_digitStrings_succ]
    -- Each term reads an earlier entry of the previous row.
    refine Finset.sum_congr rfl fun d _ => ?_
    split
    · exact ih (s - d) (by omega)
    · rfl

end EthLib.Cryptography.Wots
