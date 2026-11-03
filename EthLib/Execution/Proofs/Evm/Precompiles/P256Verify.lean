module

public import EthLib.Execution.Evm.Precompiles.P256Verify

/-!
# Proofs: `Evm.Precompiles.P256Verify`

- The call fails exactly when the gas is below 6900.
- With enough gas, a wrong length gives empty output, and every output is the word 1 or empty.
- A signature component outside `(0, n)` never verifies.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.P256Verify

open EthLib.Cryptography.Secp256r1

/-- The call fails exactly when the gas is below the price. -/
theorem p256Verify_eq_error_iff (data : ByteArray) (gas : Nat) (e : P256VerifyError) :
    p256Verify data gas = .error e ↔ gas < GAS_P256VERIFY ∧ e = .outOfGas GAS_P256VERIFY gas := by
  unfold p256Verify
  by_cases hgas : gas < GAS_P256VERIFY
  · simp only [hgas, ↓reduceIte, Except.error.injEq, true_and]
    exact eq_comm
  · simp only [hgas, ↓reduceIte, false_and, iff_false]
    split
    · simp
    · split <;> simp

/-- With enough gas, a length other than 160 bytes gives empty output. -/
theorem p256Verify_invalidInputLength {data : ByteArray} (hsize : data.size ≠ INPUT_BYTES) {gas : Nat}
    (hgas : GAS_P256VERIFY ≤ gas) : p256Verify data gas = .ok .empty := by
  simp [p256Verify, hsize, Nat.not_lt.mpr hgas]

/-- Every output is the word 1 or empty. -/
theorem p256Verify_ok {data : ByteArray} {gas : Nat} {out : ByteArray} (h : p256Verify data gas = .ok out) :
    out = VALID ∨ out = .empty := by
  unfold p256Verify at h
  split at h
  · cases h
  split at h
  · exact .inr (Except.ok.inj h).symm
  split at h
  · exact .inl (Except.ok.inj h).symm
  · exact .inr (Except.ok.inj h).symm

/-- A signature with `r` outside `(0, n)` never verifies, whatever the key and the hash. -/
theorem verify_of_r_out (q : Point) (e : Nat) {r : Nat} (hr : ¬(0 < r ∧ r < Fn.modulus)) (s : Nat) :
    verify q e r s = false := by
  simp [verify, hr]

/-- A signature with `s` outside `(0, n)` never verifies, whatever the key and the hash. -/
theorem verify_of_s_out (q : Point) (e r : Nat) {s : Nat} (hs : ¬(0 < s ∧ s < Fn.modulus)) :
    verify q e r s = false := by
  unfold verify
  split <;> simp_all

/-- A result that the kernel computes as the bytes `out` is `.ok out`. -/
theorem eq_ok_of_kernel {result : Except P256VerifyError ByteArray} {out : ByteArray}
    (h : (result.toOption.map fun bytes => bytes.data.toList) = some out.data.toList) : result = .ok out := by
  cases result with
  | error => simp [Except.toOption] at h
  | ok bytes =>
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at h
    cases bytes; cases out
    simp_all

end EthLib.Execution.Evm.Precompiles.P256Verify
