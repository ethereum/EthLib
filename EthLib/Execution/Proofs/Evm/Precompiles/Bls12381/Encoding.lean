module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: `Evm.Precompiles.Bls12381.Encoding`

- The decoder removes exactly the padding that the encoder adds.
- The padding check and the field check of Amsterdam reject exactly the inputs that Prague's single field check rejects.
- The known answers state a result as an `Except` and check it through its bytes, which the kernel compares fast.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bytesToNat natToBytes)
open EthLib.Cryptography.Bls (Fp)

/-! ## Padding -/

/-- The decoder gives back the 48 bytes of a padded field element. -/
theorem unpadFp_pad (raw : List UInt8) : unpadFp (zeroPad ++ raw) = .ok raw := by
  simp [unpadFp, zeroPad, PAD_BYTES]

/-- The decoder gives back the 96 bytes of a padded G1 point. -/
theorem unpadG1_padG1 {raw : List UInt8} (hlength : raw.length = 96) : unpadG1 (padG1 raw) = .ok raw := by
  have htake : (raw.take 48).length = 48 := by simp [hlength]
  simp [unpadG1, padG1, zeroPad, PAD_BYTES, unpadFp, htake, bind, Except.bind, pure, Except.pure]
  -- After the first 48 bytes, the other 48 are all that is left.
  rw [List.take_of_length_le (l := List.drop 48 raw) (by simp [hlength]), List.take_append_drop]

/-! ## The field check of Prague -/

/-- A padded field element decodes in two steps exactly when it is below the field modulus as one 64-byte integer.

Prague reads the 64 bytes as one integer and rejects it unless it is below the modulus.

Amsterdam first rejects nonzero padding, then reads the 48 bytes.

Nonzero padding makes the 64-byte integer at least `2^384`, above the modulus, so both reject the same inputs. -/
theorem unpadFp_bytesToFieldElement_isOk {padded : List UInt8} (hlength : padded.length = 64) :
    ((unpadFp padded) >>= bytesToFieldElement).toOption.isSome ↔ bytesToNat padded < Fp.modulus := by
  -- The 64 bytes are 16 high bytes, then 48 low bytes.
  have hsplit := EthLib.Base.bytesToNat_append (padded.take 16) (padded.drop 16)
  rw [List.take_append_drop] at hsplit
  have hlow : (padded.drop 16).length = 48 := by simp [hlength]
  have hhigh : (padded.take 16).length = 16 := by simp [hlength]
  have hlt := EthLib.Base.bytesToNat_lt (padded.drop 16)
  rw [hlow] at hlt
  have hmodulus : Fp.modulus < 256 ^ 48 := by decide
  by_cases hpad : padded.take 16 = List.replicate 16 0
  · -- Zero padding: the 64-byte integer is the 48-byte integer.
    have hzero : bytesToNat (padded.take 16) = 0 := by
      rw [hpad]
      rfl
    simp only [unpadFp, PAD_BYTES, hpad, ↓reduceIte, bind, Except.bind, bytesToFieldElement]
    rw [hsplit, hzero, Nat.zero_mul, Nat.zero_add]
    split
    · rename_i hlt'
      simp [Except.toOption, hlt']
    · rename_i hge
      simp [Except.toOption, hge]
  · -- Nonzero padding: the 64-byte integer is at least `2^384`.
    have hpos : 0 < bytesToNat (padded.take 16) := by
      rcases Nat.eq_zero_or_pos (bytesToNat (padded.take 16)) with h | h
      · exfalso
        apply hpad
        have hround := EthLib.Base.natToBytes_bytesToNat (padded.take 16)
        rw [hhigh, h] at hround
        rw [← hround]
        decide
      · exact h
    simp only [unpadFp, PAD_BYTES, hpad, ↓reduceIte, bind, Except.bind, Except.toOption, Option.isSome_none,
      Bool.false_eq_true, false_iff, Nat.not_lt]
    rw [hsplit, hlow]
    calc Fp.modulus ≤ 256 ^ 48 := Nat.le_of_lt hmodulus
      _ ≤ bytesToNat (padded.take 16) * 256 ^ 48 := Nat.le_mul_of_pos_left _ hpos
      _ ≤ _ := Nat.le_add_right _ _

/-! ## Results -/

/-- A chain of steps that succeeds succeeded at its first step. -/
theorem bind_eq_ok {α β : Type} {x : Except Bls12381Error α} {f : α → Except Bls12381Error β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Known answers through bytes -/

/-- A result that the kernel computes as the bytes `out` is `.ok out`. -/
theorem eq_ok_of_kernel {result : Except Bls12381Error ByteArray} {out : ByteArray}
    (h : (result.toOption.map fun bytes => bytes.data.toList) = some out.data.toList) : result = .ok out := by
  cases result with
  | error => simp [Except.toOption] at h
  | ok bytes =>
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at h
    cases bytes; cases out
    simp_all

/-- The error of a result, or `none` when it succeeds. -/
def errorOf (result : Except Bls12381Error ByteArray) : Option Bls12381Error :=
  match result with
  | .error e => some e
  | .ok _ => none

/-- A result whose error the kernel computes as `e` is `.error e`. -/
theorem eq_error_of_kernel {result : Except Bls12381Error ByteArray} {e : Bls12381Error}
    (h : errorOf result = some e) : result = .error e := by
  cases result <;> simp_all [errorOf]

end EthLib.Execution.Evm.Precompiles.Bls12381
