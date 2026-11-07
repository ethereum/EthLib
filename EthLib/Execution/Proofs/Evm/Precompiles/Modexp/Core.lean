module

public import EthLib.Execution.Proofs.Evm.Precompiles.Modexp.Encoding
public import EthLib.Execution.Proofs.Evm.PowMod
public import EthLib.Execution.Proofs.Evm.Precompiles.Modexp.Gas
public import EthLib.Execution.Evm.Precompiles.Modexp.Core

/-!
# Proofs: `Core`

The precompile does what EIP-198 and EIP-7823 say.

- The output is `base ^ exponent mod modulus`, or `0` when the modulus is `0`.
- The output has exactly `len_mod` bytes.
- A short input reads as if padded with zeros.
- Data past the last field is ignored.
- From Fusaka, a length above 1024 fails before gas is charged.
- Otherwise the call fails exactly when the gas given is below the price.
- A call succeeds exactly when both checks pass, and it then returns the computed output.
- The price always fits in 64 bits.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Modexp

open EthLib.Base
open EthLib.Execution.Evm

/-- The big-endian integer held by the output bytes. -/
def outputNat (bytes : ByteArray) : Nat :=
  bytesToNat bytes.data.toList

/-- The output bytes are the fixed-width encoding of the result. -/
theorem compute_data (data : ByteArray) (l : Lengths) :
    (compute data l).data.toList
      = natToBytes l.modulus
          (if readNat data l.modulusStart l.modulus = 0 then 0
           else powMod (readNat data BASE_OFFSET l.base) (readNat data l.exponentStart l.exponent)
                  (readNat data l.modulusStart l.modulus)) := by
  simp [compute]

/-- The output has exactly `len_mod` bytes.

EIP-198: "returns an output ... as a byte array with the same length as the modulus". -/
theorem compute_size (data : ByteArray) (l : Lengths) : (compute data l).size = l.modulus := by
  have h := congrArg List.length (compute_data data l)
  rw [natToBytes_length, Array.length_toList] at h
  exact h

/-- The output is the mathematical `base ^ exponent mod modulus`.

EIP-198: "returns an output `(BASE**EXPONENT) % MODULUS`".
The case of a zero modulus is not in EIP-198.

Appendix E of the Yellow Paper takes `x mod 0` to be zero. -/
theorem compute_eq_pow_mod (data : ByteArray) (l : Lengths) :
    outputNat (compute data l)
      = if readNat data l.modulusStart l.modulus = 0 then 0
        else readNat data BASE_OFFSET l.base ^ readNat data l.exponentStart l.exponent
              % readNat data l.modulusStart l.modulus := by
  unfold outputNat
  rw [compute_data]
  split
  · -- A zero modulus gives the number 0 (written as zero bytes).
    rw [bytesToNat_natToBytes, Nat.zero_mod]
  · next h =>
    -- No truncation: the remainder is below the modulus, which fits in `len_mod` bytes.
    rw [bytesToNat_natToBytes_of_lt, powMod_eq]
    -- The side goal is that bound, stated on the loop.
    rw [powMod_eq]
    exact Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero h)) (readNat_lt _ _ _)

/-- A zero modulus gives `len_mod` zero bytes. -/
theorem compute_modulus_zero (data : ByteArray) (l : Lengths)
    (h : readNat data l.modulusStart l.modulus = 0) :
    (compute data l).data = Array.replicate l.modulus 0 := by
  have := compute_data data l
  rw [ite_eq_left h, natToBytes_zero_right] at this
  exact Array.toList_inj.mp (by simpa using this)

/-- An empty modulus gives an empty output, even with an empty base.

This covers the early return when both `base_length` and `modulus_length` are zero. -/
theorem compute_modulus_len_zero (data : ByteArray) (l : Lengths) (h : l.modulus = 0) :
    (compute data l).size = 0 := by
  rw [compute_size, h]

/-! ## Padding and excess -/

/-- Padding the call data with zeros does not change the lengths read. -/
theorem parseLengths_append_zeros (data : ByteArray) (n : Nat) :
    parseLengths (data ++ ByteArray.mk (Array.replicate n 0)) = parseLengths data := by
  simp [parseLengths, readNat_append_zeros]

/-- Padding the call data with zeros does not change the gas. -/
theorem requiredGas_append_zeros (fork : Fork) (data : ByteArray) (n : Nat) (l : Lengths) :
    requiredGas fork (data ++ ByteArray.mk (Array.replicate n 0)) l = requiredGas fork data l := by
  simp [requiredGas, exponentHead, readNat_append_zeros]

/-- Padding the call data with zeros does not change the output. -/
theorem compute_append_zeros (data : ByteArray) (n : Nat) (l : Lengths) :
    compute (data ++ ByteArray.mk (Array.replicate n 0)) l = compute data l := by
  simp [compute, readNat_append_zeros]

/-- Padding the call data with zeros does not change the result of the precompile.

EIP-198: "Call data is assumed to be infinitely right-padded with zero bytes". -/
theorem modexp_append_zeros (fork : Fork) (data : ByteArray) (n gas : Nat) :
    modexp fork (data ++ ByteArray.mk (Array.replicate n 0)) gas = modexp fork data gas := by
  simp [modexp, parseLengths_append_zeros, requiredGas_append_zeros, compute_append_zeros]

/-- Two inputs that agree on the bytes the lengths describe give the same result.

The bytes described are the three headers, `BASE`, `EXPONENT` and `MODULUS`.
A byte past the end counts as zero.
This covers excess data, which EIP-198 says "is ignored", and short input. -/
theorem modexp_congr (fork : Fork) {d₁ d₂ : ByteArray} (gas : Nat)
    (h : ∀ i, i < BASE_OFFSET + (parseLengths d₁).base + (parseLengths d₁).exponent
                + (parseLengths d₁).modulus → byteAt d₁ i = byteAt d₂ i) :
    modexp fork d₁ gas = modexp fork d₂ gas := by
  -- The lengths come from the first 96 bytes, which lie inside the covered range.
  have hl : parseLengths d₁ = parseLengths d₂ := by
    have hh : ∀ i, i < 96 → byteAt d₁ i = byteAt d₂ i := fun i hi => h i (by
      unfold BASE_OFFSET LENGTH_HEADER_BYTES; omega)
    simp only [parseLengths, LENGTH_HEADER_BYTES]
    have e : ∀ s, s + 32 ≤ 96 → readNat d₁ s 32 = readNat d₂ s 32 := fun s hs =>
      readNat_congr fun i h1 h2 => hh i (by omega)
    simp [e 0 (by omega), e 32 (by omega), e 64 (by omega)]
  -- Compare each window the output depends on.
  have hb : readNat d₁ BASE_OFFSET (parseLengths d₁).base
      = readNat d₂ BASE_OFFSET (parseLengths d₁).base :=
    readNat_congr fun i h1 h2 => h i (by unfold BASE_OFFSET LENGTH_HEADER_BYTES at *; omega)
  have he : readNat d₁ (parseLengths d₁).exponentStart (parseLengths d₁).exponent
      = readNat d₂ (parseLengths d₁).exponentStart (parseLengths d₁).exponent :=
    readNat_congr fun i h1 h2 => h i (by
      unfold Lengths.exponentStart BASE_OFFSET LENGTH_HEADER_BYTES at *; omega)
  have hm : readNat d₁ (parseLengths d₁).modulusStart (parseLengths d₁).modulus
      = readNat d₂ (parseLengths d₁).modulusStart (parseLengths d₁).modulus :=
    readNat_congr fun i h1 h2 => h i (by
      unfold Lengths.modulusStart Lengths.exponentStart BASE_OFFSET LENGTH_HEADER_BYTES at *; omega)
  have hx : exponentHead d₁ (parseLengths d₁) = exponentHead d₂ (parseLengths d₁) :=
    readNat_congr fun i h1 h2 => h i (by
      unfold Lengths.exponentStart BASE_OFFSET LENGTH_HEADER_BYTES EXPONENT_HEAD_BYTES at *
      omega)
  have hg : requiredGas fork d₁ (parseLengths d₁) = requiredGas fork d₂ (parseLengths d₁) := by
    simp [requiredGas, hx]
  have hc : compute d₁ (parseLengths d₁) = compute d₂ (parseLengths d₁) := by
    simp [compute, hb, he, hm]
  unfold modexp
  dsimp only
  rw [← hl, hg, hc]

/-- Data after the last byte the lengths describe is ignored.

EIP-198: "excess data is ignored". -/
theorem modexp_append_excess (fork : Fork) (data extra : ByteArray) (gas : Nat)
    (h : BASE_OFFSET + (parseLengths data).base + (parseLengths data).exponent
          + (parseLengths data).modulus ≤ data.size) :
    modexp fork (data ++ extra) gas = modexp fork data gas := by
  symm
  apply modexp_congr
  intro i hi
  -- Every covered byte lies inside the original data, before the excess.
  have hi' : i < data.size := Nat.lt_of_lt_of_le hi h
  simp [byteAt_eq_getD, ByteArray.data_append, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left hi']

/-! ## Bounds and gas -/

/-- From Fusaka, the bound of EIP-7823 fails on the first length above 1024. -/
private theorem checkLengthsAt_eq_error_iff {fork : Fork} {l : Lengths} {e : ModexpError} :
    checkLengthsAt fork l = .error e ↔
      (fork ≥ .fusaka ∧ MAX_LENGTH_BYTES < l.base ∧ e = .lengthTooLarge .base l.base) ∨
      (fork ≥ .fusaka ∧ l.base ≤ MAX_LENGTH_BYTES ∧ MAX_LENGTH_BYTES < l.exponent ∧
        e = .lengthTooLarge .exponent l.exponent) ∨
      (fork ≥ .fusaka ∧ l.base ≤ MAX_LENGTH_BYTES ∧ l.exponent ≤ MAX_LENGTH_BYTES ∧
        MAX_LENGTH_BYTES < l.modulus ∧ e = .lengthTooLarge .modulus l.modulus) := by
  unfold checkLengthsAt checkLengths
  by_cases hf : fork ≥ .fusaka <;>
    by_cases hb : MAX_LENGTH_BYTES < l.base <;>
    by_cases he : MAX_LENGTH_BYTES < l.exponent <;>
    by_cases hm : MAX_LENGTH_BYTES < l.modulus <;>
    simp_all [Nat.not_le_of_lt, Nat.not_lt_of_le, eq_comm]

/-- The bound of EIP-7823 passes exactly when, from Fusaka, each length is at most 1024. -/
private theorem checkLengthsAt_eq_ok_iff {fork : Fork} {l : Lengths} :
    checkLengthsAt fork l = .ok () ↔
      (fork ≥ .fusaka →
        l.base ≤ MAX_LENGTH_BYTES ∧ l.exponent ≤ MAX_LENGTH_BYTES ∧
          l.modulus ≤ MAX_LENGTH_BYTES) := by
  -- The check passes exactly when it raises none of its errors.
  cases h : checkLengthsAt fork l with
  | error e =>
    have herr := checkLengthsAt_eq_error_iff.mp h
    simp only [reduceCtorEq, false_iff]
    intro hall
    rcases herr with ⟨hf, hb, -⟩ | ⟨hf, -, he, -⟩ | ⟨hf, -, -, hm, -⟩ <;> have := hall hf <;> omega
  | ok u =>
    simp only [true_iff]
    intro hf
    have hn (e : ModexpError) : checkLengthsAt fork l ≠ .error e := by rw [h]; exact nofun
    have hb : l.base ≤ MAX_LENGTH_BYTES := Nat.not_lt.mp fun hb =>
      hn _ (checkLengthsAt_eq_error_iff.mpr (.inl ⟨hf, hb, rfl⟩))
    have he : l.exponent ≤ MAX_LENGTH_BYTES := Nat.not_lt.mp fun he =>
      hn _ (checkLengthsAt_eq_error_iff.mpr (.inr (.inl ⟨hf, hb, he, rfl⟩)))
    have hm : l.modulus ≤ MAX_LENGTH_BYTES := Nat.not_lt.mp fun hm =>
      hn _ (checkLengthsAt_eq_error_iff.mpr (.inr (.inr ⟨hf, hb, he, hm, rfl⟩)))
    exact ⟨hb, he, hm⟩

/--
A call succeeds exactly when the lengths pass the bound of EIP-7823 and the gas covers the price.

The bound applies from Fusaka only: each of the three lengths must then be at most 1024 bytes.

The price is the one that the input sets at the fork.

The output is then the computed one.
-/
theorem modexp_eq_ok_iff {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray} :
    modexp fork data gas = .ok out ↔
      (fork ≥ .fusaka →
        (parseLengths data).base ≤ MAX_LENGTH_BYTES ∧
          (parseLengths data).exponent ≤ MAX_LENGTH_BYTES ∧
          (parseLengths data).modulus ≤ MAX_LENGTH_BYTES) ∧
        requiredGas fork data (parseLengths data) ≤ gas ∧
        out = compute data (parseLengths data) := by
  rw [← checkLengthsAt_eq_ok_iff]
  unfold modexp
  dsimp only
  split
  · next e he => simp [he]
  · next he =>
    by_cases hg : gas < requiredGas fork data (parseLengths data)
    · simp [he, hg, Nat.not_le.mpr hg]
    · simp [he, Nat.not_lt.mp hg, hg, eq_comm]

/--
A call fails exactly in one of these ways, in the order the call checks them.

From Fusaka, the first length above 1024 bytes fails, in the order base, exponent, modulus.

EIP-7823 names no order, so the order fixes only which length the error reports.

Otherwise the call fails when the gas is below the price.
-/
theorem modexp_eq_error_iff {fork : Fork} {data : ByteArray} {gas : Nat} {e : ModexpError} :
    modexp fork data gas = .error e ↔
      (fork ≥ .fusaka ∧ MAX_LENGTH_BYTES < (parseLengths data).base ∧
        e = .lengthTooLarge .base (parseLengths data).base) ∨
      (fork ≥ .fusaka ∧ (parseLengths data).base ≤ MAX_LENGTH_BYTES ∧
        MAX_LENGTH_BYTES < (parseLengths data).exponent ∧
        e = .lengthTooLarge .exponent (parseLengths data).exponent) ∨
      (fork ≥ .fusaka ∧ (parseLengths data).base ≤ MAX_LENGTH_BYTES ∧
        (parseLengths data).exponent ≤ MAX_LENGTH_BYTES ∧
        MAX_LENGTH_BYTES < (parseLengths data).modulus ∧
        e = .lengthTooLarge .modulus (parseLengths data).modulus) ∨
      ((fork ≥ .fusaka →
        (parseLengths data).base ≤ MAX_LENGTH_BYTES ∧
          (parseLengths data).exponent ≤ MAX_LENGTH_BYTES ∧
          (parseLengths data).modulus ≤ MAX_LENGTH_BYTES) ∧
        gas < requiredGas fork data (parseLengths data) ∧
        e = .outOfGas (requiredGas fork data (parseLengths data)) gas) := by
  -- The three length errors are the errors of the bound, and the fourth is the gas.
  have regroup (a b c d : Prop) : (a ∨ b ∨ c ∨ d) ↔ ((a ∨ b ∨ c) ∨ d) := by simp only [or_assoc]
  rw [← checkLengthsAt_eq_ok_iff, regroup, ← checkLengthsAt_eq_error_iff]
  unfold modexp
  dsimp only
  split
  · next e' he => simp [he]
  · next he =>
    by_cases hg : gas < requiredGas fork data (parseLengths data)
    · simp [he, hg, eq_comm]
    · simp [he, hg]

/-- From Fusaka, a base length above 1024 fails before gas is charged, whatever the gas.

EIP-7823: "If any of these inputs are larger than the limit, the precompile execution stops, returns an error, and consumes all gas". -/
theorem modexp_lengthTooLarge_base {fork : Fork} (hfork : fork ≥ .fusaka) (data : ByteArray)
    (gas : Nat) (h : MAX_LENGTH_BYTES < (parseLengths data).base) :
    modexp fork data gas = .error (.lengthTooLarge .base (parseLengths data).base) :=
  modexp_eq_error_iff.mpr (.inl ⟨hfork, h, rfl⟩)

/-- From Fusaka, an exponent length above 1024 fails before gas is charged, whatever the gas.

The base length is in bounds, so its check passes first. -/
theorem modexp_lengthTooLarge_exponent {fork : Fork} (hfork : fork ≥ .fusaka) (data : ByteArray)
    (gas : Nat) (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (h : MAX_LENGTH_BYTES < (parseLengths data).exponent) :
    modexp fork data gas = .error (.lengthTooLarge .exponent (parseLengths data).exponent) :=
  modexp_eq_error_iff.mpr (.inr (.inl ⟨hfork, hb, h, rfl⟩))

/-- From Fusaka, a modulus length above 1024 fails before gas is charged, whatever the gas.

The base and exponent lengths are in bounds, so their checks pass first. -/
theorem modexp_lengthTooLarge_modulus {fork : Fork} (hfork : fork ≥ .fusaka) (data : ByteArray)
    (gas : Nat) (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (h : MAX_LENGTH_BYTES < (parseLengths data).modulus) :
    modexp fork data gas = .error (.lengthTooLarge .modulus (parseLengths data).modulus) :=
  modexp_eq_error_iff.mpr (.inr (.inr (.inl ⟨hfork, hb, he, h, rfl⟩)))

/-- With every length in bounds, the call fails exactly when the gas is below the price.

This holds at every fork, with the bound or without it. -/
theorem modexp_outOfGas (fork : Fork) (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (hm : (parseLengths data).modulus ≤ MAX_LENGTH_BYTES)
    (hg : gas < requiredGas fork data (parseLengths data)) :
    modexp fork data gas = .error (.outOfGas (requiredGas fork data (parseLengths data)) gas) :=
  modexp_eq_error_iff.mpr (.inr (.inr (.inr ⟨fun _ => ⟨hb, he, hm⟩, hg, rfl⟩)))

/-- With every length in bounds and enough gas, the call returns the computed output. -/
theorem modexp_ok (fork : Fork) (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (hm : (parseLengths data).modulus ≤ MAX_LENGTH_BYTES)
    (hg : requiredGas fork data (parseLengths data) ≤ gas) :
    modexp fork data gas = .ok (compute data (parseLengths data)) :=
  modexp_eq_ok_iff.mpr ⟨fun _ => ⟨hb, he, hm⟩, hg, rfl⟩

/-- A successful call returns exactly `len_mod` bytes. -/
theorem modexp_ok_size {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : modexp fork data gas = .ok out) : out.size = (parseLengths data).modulus := by
  rw [(modexp_eq_ok_iff.mp h).2.2]
  exact compute_size _ _

/-- The first 32 bytes of the exponent hold less than `2 ^ 256`. -/
theorem exponentHead_lt (data : ByteArray) (l : Lengths) : exponentHead data l < 2 ^ 256 := by
  -- At most 32 bytes are read, and 32 bytes hold less than `256 ^ 32 = 2 ^ 256`.
  have h := readNat_lt data l.exponentStart (min EXPONENT_HEAD_BYTES l.exponent)
  have hle : 256 ^ min EXPONENT_HEAD_BYTES l.exponent ≤ 2 ^ 256 :=
    calc 256 ^ min EXPONENT_HEAD_BYTES l.exponent ≤ 256 ^ 32 :=
          Nat.pow_le_pow_right (by decide) (by unfold EXPONENT_HEAD_BYTES; omega)
      _ = 2 ^ 256 := by decide
  exact Nat.lt_of_lt_of_le h hle

/-- From Fusaka, a price is charged only for lengths in bounds, and it is at most 528449536.

So the price always fits in a 64-bit integer, the width of EVM gas. -/
theorem chargedGas_le {fork : Fork} (hfork : fork ≥ .fusaka) {data : ByteArray} {cost : Nat}
    (h : chargedGas fork data = .ok cost) : cost ≤ 528449536 := by
  unfold chargedGas checkLengthsAt at h
  simp only [hfork, ite_true] at h
  -- The only success path is the one where every length passed its check.
  split at h
  · cases h
  · next hc =>
    cases h
    unfold checkLengths at hc
    split at hc
    · cases hc
    next h1 =>
    split at hc
    · cases hc
    next h2 =>
    split at hc
    · cases hc
    next h3 =>
    exact gasCost_le hfork (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h3) (Nat.le_of_not_lt h2)
      (exponentHead_lt _ _)

end EthLib.Execution.Evm.Precompiles.Modexp
