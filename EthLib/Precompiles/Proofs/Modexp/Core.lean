import EthLib.Precompiles.Proofs.Modexp.Bytes
import EthLib.Precompiles.Proofs.Modexp.PowMod
import EthLib.Precompiles.Proofs.Modexp.Gas
import EthLib.Precompiles.Modexp.Core

/-!
# Proofs: `Core`

The precompile does what EIP-198 and EIP-7823 say.

- The output is `base ^ exponent mod modulus`, or `0` when the modulus is `0`.
- The output has exactly `len_mod` bytes.
- A short input reads as if padded with zeros.
- Data past the last field is ignored.
- A length above 1024 fails before gas is charged.
- Otherwise the call fails exactly when the gas given is below the price.
- The price always fits in 64 bits.

The known answers at the end run the worked examples of EIP-198 through the whole precompile.
-/

namespace EthLib.Precompiles.Modexp

open EthLib.Precompiles.Modexp.Constants

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
It is the `modulus == 0` branch of `modexp` in the execution-specs module. -/
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
  -- Zero written on any width is that many zero bytes.
  have h1 : natToBytes l.modulus 0 = List.replicate l.modulus 0 := by
    generalize l.modulus = len
    induction len with
    | zero => rfl
    | succ len ih => simp [natToBytes, ih, List.replicate_succ']
  have := compute_data data l
  rw [ite_eq_left h, h1] at this
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
theorem requiredGas_append_zeros (data : ByteArray) (n : Nat) (l : Lengths) :
    requiredGas (data ++ ByteArray.mk (Array.replicate n 0)) l = requiredGas data l := by
  simp [requiredGas, exponentHead, readNat_append_zeros]

/-- Padding the call data with zeros does not change the output. -/
theorem compute_append_zeros (data : ByteArray) (n : Nat) (l : Lengths) :
    compute (data ++ ByteArray.mk (Array.replicate n 0)) l = compute data l := by
  simp [compute, readNat_append_zeros]

/-- Padding the call data with zeros does not change the result of the precompile.

EIP-198: "Call data is assumed to be infinitely right-padded with zero bytes". -/
theorem modexp_append_zeros (data : ByteArray) (n gas : Nat) :
    modexp (data ++ ByteArray.mk (Array.replicate n 0)) gas = modexp data gas := by
  simp [modexp, parseLengths_append_zeros, requiredGas_append_zeros, compute_append_zeros]

/-- Two inputs that agree on the bytes the lengths describe give the same result.

The bytes described are the three headers, `BASE`, `EXPONENT` and `MODULUS`.
A byte past the end counts as zero.
This covers excess data, which EIP-198 says "is ignored", and short input. -/
theorem modexp_congr {d₁ d₂ : ByteArray} (gas : Nat)
    (h : ∀ i, i < BASE_OFFSET + (parseLengths d₁).base + (parseLengths d₁).exponent
                + (parseLengths d₁).modulus → byteAt d₁ i = byteAt d₂ i) :
    modexp d₁ gas = modexp d₂ gas := by
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
  have hg : requiredGas d₁ (parseLengths d₁) = requiredGas d₂ (parseLengths d₁) := by
    simp [requiredGas, hx]
  have hc : compute d₁ (parseLengths d₁) = compute d₂ (parseLengths d₁) := by
    simp [compute, hb, he, hm]
  unfold modexp
  dsimp only
  rw [← hl, hg, hc]

/-- Data after the last byte the lengths describe is ignored.

EIP-198: "excess data is ignored". -/
theorem modexp_append_excess (data extra : ByteArray) (gas : Nat)
    (h : BASE_OFFSET + (parseLengths data).base + (parseLengths data).exponent
          + (parseLengths data).modulus ≤ data.size) :
    modexp (data ++ extra) gas = modexp data gas := by
  symm
  apply modexp_congr
  intro i hi
  -- Every covered byte lies inside the original data, before the excess.
  have hi' : i < data.size := Nat.lt_of_lt_of_le hi h
  simp [byteAt, ByteArray.data_append, Array.getD_eq_getD_getElem?,
    Array.getElem?_append_left hi']

/-! ## Bounds and gas -/

/-- A base length above 1024 fails before gas is charged, whatever the gas.

EIP-7823: "If any of these inputs are larger than the limit, the precompile execution stops, returns an error, and consumes all gas". -/
theorem modexp_base_too_large (data : ByteArray) (gas : Nat)
    (h : MAX_LENGTH_BYTES < (parseLengths data).base) :
    modexp data gas = .error (.lengthTooLarge .base (parseLengths data).base) := by
  simp [modexp, checkLengths, h]

/-- An exponent length above 1024 fails before gas is charged, whatever the gas.

The base length is in bounds, so its check passes first. -/
theorem modexp_exponent_too_large (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (h : MAX_LENGTH_BYTES < (parseLengths data).exponent) :
    modexp data gas = .error (.lengthTooLarge .exponent (parseLengths data).exponent) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, h]

/-- A modulus length above 1024 fails before gas is charged, whatever the gas.

The base and exponent lengths are in bounds, so their checks pass first. -/
theorem modexp_modulus_too_large (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (h : MAX_LENGTH_BYTES < (parseLengths data).modulus) :
    modexp data gas = .error (.lengthTooLarge .modulus (parseLengths data).modulus) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, Nat.not_lt.mpr he, h]

/-- With every length in bounds, the call fails exactly when the gas is below the price. -/
theorem modexp_out_of_gas (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (hm : (parseLengths data).modulus ≤ MAX_LENGTH_BYTES)
    (hg : gas < requiredGas data (parseLengths data)) :
    modexp data gas = .error (.outOfGas (requiredGas data (parseLengths data)) gas) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, Nat.not_lt.mpr he, Nat.not_lt.mpr hm, hg]

/-- With every length in bounds and enough gas, the call returns the computed output. -/
theorem modexp_ok (data : ByteArray) (gas : Nat)
    (hb : (parseLengths data).base ≤ MAX_LENGTH_BYTES)
    (he : (parseLengths data).exponent ≤ MAX_LENGTH_BYTES)
    (hm : (parseLengths data).modulus ≤ MAX_LENGTH_BYTES)
    (hg : requiredGas data (parseLengths data) ≤ gas) :
    modexp data gas = .ok (compute data (parseLengths data)) := by
  simp [modexp, checkLengths, Nat.not_lt.mpr hb, Nat.not_lt.mpr he, Nat.not_lt.mpr hm,
    Nat.not_lt.mpr hg]

/-- A successful call returns exactly `len_mod` bytes. -/
theorem modexp_ok_size {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : modexp data gas = .ok out) : out.size = (parseLengths data).modulus := by
  unfold modexp at h
  dsimp only at h
  -- The only success path returns the computed output.
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact compute_size _ _

/-- The first 32 bytes of the exponent hold less than `2 ^ 256`. -/
theorem exponentHead_lt (data : ByteArray) (l : Lengths) : exponentHead data l < 2 ^ 256 := by
  -- At most 32 bytes are read, and 32 bytes hold less than `256 ^ 32 = 2 ^ 256`.
  have h := readNat_lt data l.exponentStart (min EXPONENT_HEAD_BYTES l.exponent)
  have hle : 256 ^ min EXPONENT_HEAD_BYTES l.exponent ≤ 2 ^ 256 :=
    calc 256 ^ min EXPONENT_HEAD_BYTES l.exponent ≤ 256 ^ 32 :=
          Nat.pow_le_pow_right (by decide) (by unfold EXPONENT_HEAD_BYTES; omega)
      _ = 2 ^ 256 := by norm_num
  exact Nat.lt_of_lt_of_le h hle

/-- A price is charged only for lengths in bounds, and it is at most 528449536.

So the price always fits in a 64-bit integer, the width of EVM gas. -/
theorem chargedGas_le {data : ByteArray} {cost : Nat} (h : chargedGas data = .ok cost) :
    cost ≤ 528449536 := by
  unfold chargedGas at h
  dsimp only at h
  -- The only success path is the one where every length passed its check.
  split at h
  · cases h
  · next hc =>
    cases h
    unfold checkLengths at hc
    split_ifs at hc with h1 h2 h3
    exact gasCost_le (Nat.le_of_not_lt h1) (Nat.le_of_not_lt h3) (Nat.le_of_not_lt h2)
      (exponentHead_lt _ _)

/-! ## Known answers

The worked examples of EIP-198, Specification, run through the whole precompile.

EIP-198 writes each input as 32-byte words followed by the raw fields.
The helpers below build the same bytes.

The expected outputs are the ones EIP-198 states.

When EIP-198 gives no output, the output comes from execution-specs at `2c0c8e7`.
The file is `tests/byzantium/eip198_modexp_precompile/test_modexp.py`.
A named case below keeps its name from that file.

`decide +kernel` has the kernel itself evaluate each claim.
It adds no axiom, unlike `native_decide`. -/

/-- `n` as one 32-byte big-endian word. -/
private def word (n : Nat) : List UInt8 := natToBytes 32 n

/-- Call data made of the given bytes. -/
private def callData (bytes : List UInt8) : ByteArray := ByteArray.mk bytes.toArray

/-- The error of a failed call, or nothing for a success. -/
private def errorOf : Except ModexpError ByteArray → Option ModexpError
  | .error e => some e
  | .ok _ => none

/-- `2 ^ 256 - 2 ^ 32 - 977`, the modulus of the first two examples. -/
private def p : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- EIP-198, first example: `3 ^ (p - 1) mod p`.

```text
    [ 1 | 32 | 32 | 03 | p - 1 | p ]
```

By Fermat's little theorem the result is 1, written on 32 bytes. -/
private def example1 : ByteArray :=
  callData (word 1 ++ word 32 ++ word 32 ++ [3] ++ word (p - 1) ++ word p)

-- The output is 1 on 32 bytes.
example : (modexp example1 4080).toOption = some (callData (word 1)) := by decide +kernel

-- EIP-198 gives an `ADJUSTED_EXPONENT_LENGTH` of 255 for this input.
example : iterations (parseLengths example1).exponent (exponentHead example1 (parseLengths example1))
    = 255 := by decide +kernel

-- EIP-7883 prices a 32-byte modulus at the flat complexity 16.
-- So the price is 16 * 255 = 4080, and one gas less runs out.
example : errorOf (modexp example1 4079) = some (.outOfGas 4080 4079) := by decide +kernel

/-- EIP-198, second example: an empty base, the same exponent and modulus.

```text
    [ 0 | 32 | 32 | p - 1 | p ]
```

No byte is read as the base, so the base is 0 and the result is 0. -/
private def example2 : ByteArray :=
  callData (word 0 ++ word 32 ++ word 32 ++ word (p - 1) ++ word p)

-- The output is 0 on 32 bytes.
example : (modexp example2 4080).toOption = some (callData (word 0)) := by decide +kernel

/-- EIP-198, third example: a modulus length of `2 ^ 256 - 1`.

```text
    [ 0 | 32 | 2^256 - 1 | 2^256 - 2 | 2^256 - 3 ]
```

EIP-198 says no gas could pay for it.
EIP-7823 now rejects it before any gas is charged. -/
private def example3 : ByteArray :=
  callData (word 0 ++ word 32 ++ word (2 ^ 256 - 1) ++ word (2 ^ 256 - 2) ++ word (2 ^ 256 - 3))

-- The modulus length fails its bound, whatever the gas.
example (gas : Nat) :
    modexp example3 gas = .error (.lengthTooLarge .modulus (2 ^ 256 - 1)) := by
  have hb : (parseLengths example3).base = 0 := by decide +kernel
  have he : (parseLengths example3).exponent = 32 := by decide +kernel
  have hm : (parseLengths example3).modulus = 2 ^ 256 - 1 := by decide +kernel
  rw [modexp_modulus_too_large example3 gas (by rw [hb]; decide) (by rw [he]; decide)
    (by rw [hm]; decide), hm]

/-- `3 ^ 65535 mod 2 ^ 255`, from `EIP-198-case4-extra-data_07` in execution-specs. -/
private def pow3 : Nat := 0x3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab

/-- EIP-198, fourth example: one byte of excess data.

```text
    [ 1 | 2 | 32 | 03 | ffff | 80 00 .. 00 | 07 ]
```

The base is 3, the exponent 65535 and the modulus `2 ^ 255`.
The trailing `07` is ignored. -/
private def example4 : ByteArray :=
  callData (word 1 ++ word 2 ++ word 32 ++ [3, 0xff, 0xff] ++ word (2 ^ 255) ++ [7])

example : (modexp example4 500).toOption = some (callData (word pow3)) := by decide +kernel

/-- EIP-198, fifth example: the modulus cut short after one byte.

```text
    [ 1 | 2 | 32 | 03 | ffff | 80 ]
```

The missing 31 bytes read as zeros, so the modulus is still `2 ^ 255`. -/
private def example5 : ByteArray :=
  callData (word 1 ++ word 2 ++ word 32 ++ [3, 0xff, 0xff, 0x80])

-- The output matches the fourth example, from `EIP-198-case5-raw-input`.
example : (modexp example5 500).toOption = some (callData (word pow3)) := by decide +kernel

/-! The smallest inputs of the same execution-specs file.

Each has an empty base and exponent.

So the result is `1 mod modulus`, or 0 for a zero modulus. -/

-- Empty call data: every length is 0, and the output is empty.
example : (modexp (callData []) 500).toOption = some (callData []) := by decide +kernel

-- A 1-byte modulus `00`: the zero modulus gives one zero byte.
example : (modexp (callData (word 0 ++ word 0 ++ word 1 ++ [0])) 500).toOption
    = some (callData [0]) := by decide +kernel

-- A 1-byte modulus `01`: `1 mod 1 = 0`, on one byte.
example : (modexp (callData (word 0 ++ word 0 ++ word 1 ++ [1])) 500).toOption
    = some (callData [0]) := by decide +kernel

-- A 2-byte modulus `0001`: `1 mod 1 = 0`, on two bytes.
example : (modexp (callData (word 0 ++ word 0 ++ word 2 ++ [0, 1])) 500).toOption
    = some (callData [0, 0]) := by decide +kernel

end EthLib.Precompiles.Modexp
