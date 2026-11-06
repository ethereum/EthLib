module

public import EthLib.Execution.Evm.Precompiles.P256Verify
import EthLib.Base.Proofs.BigEndian
import EthLib.Cryptography.Proofs.Secp256r1.Ecdsa

/-!
# Proofs: `Evm.Precompiles.P256Verify`

- The call fails exactly when the gas is below 6900.
- With enough gas, a wrong length gives empty output, and every output is the word 1 or empty.
- With enough gas, the call returns the word 1 on 160 valid bytes, and empty output otherwise.
- On the 160-byte call data of EIP-7951, the input check gives the result of ECDSA verification.
- A valid signature under an affine public key returns the word 1, and so does a SEC 1 signature.
- `(r, s)` and `(r, n - s)` give the same result at every gas limit.
- A signature component outside `(0, n)` never verifies.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.P256Verify

open EthLib.Base (bytesToNat bytesToNat_natToBytes bytesToNat_natToBytes_of_lt natToBytes
  natToBytes_length)
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
theorem p256Verify_invalidInputLength {data : ByteArray} (hsize : data.size ≠ INPUT_BYTES)
    {gas : Nat} (hgas : GAS_P256VERIFY ≤ gas) : p256Verify data gas = .ok .empty := by
  simp [p256Verify, hsize, Nat.not_lt.mpr hgas]

/-- Every output is the word 1 or empty. -/
theorem p256Verify_ok {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : p256Verify data gas = .ok out) : out = VALID ∨ out = .empty := by
  unfold p256Verify at h
  split at h
  · cases h
  split at h
  · exact .inr (Except.ok.inj h).symm
  split at h
  · exact .inl (Except.ok.inj h).symm
  · exact .inr (Except.ok.inj h).symm

/-- A signature with `r` outside `(0, n)` never verifies, whatever the key and the hash. -/
theorem verify_of_r_out (q : Point) (e : Nat) {r : Nat} (hr : ¬(0 < r ∧ r < Fn.modulus))
    (s : Nat) : verify q e r s = false := by
  simp [verify, hr]

/-- A signature with `s` outside `(0, n)` never verifies, whatever the key and the hash. -/
theorem verify_of_s_out (q : Point) (e r : Nat) {s : Nat} (hs : ¬(0 < s ∧ s < Fn.modulus)) :
    verify q e r s = false := by
  unfold verify
  split <;> simp_all

/-! ## Call data and signature verification -/

/-- The 160-byte call data of EIP-7951, Input.

It concatenates `e`, `r`, `s`, `qx` and `qy` as 32-byte big-endian words.

Each value is written modulo 2^256. -/
def callData (e r s qx qy : Nat) : ByteArray :=
  ⟨(natToBytes 32 e ++ natToBytes 32 r ++ natToBytes 32 s ++ natToBytes 32 qx
    ++ natToBytes 32 qy).toArray⟩

/-- The call data of a signature has 160 bytes. -/
theorem callData_size (e r s qx qy : Nat) : (callData e r s qx qy).size = INPUT_BYTES := by
  simp [callData, INPUT_BYTES, ByteArray.size, natToBytes_length]

/-- A key that verifies passes the check of the input against `(0, 0)`. -/
private theorem not_zero_of_verify {qx qy : Fp} {e r s : Nat}
    (hv : verify (.affine qx qy) e r s = true) : (!decide (qx.val = 0 ∧ qy.val = 0)) = true := by
  simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using verify_affine_ne_zero hv

/-- The input check of EIP-7951 accepts the bytes exactly when two conditions hold.

Both coordinates of the key lie below `p`.

The signature verifies under that key.

A key that verifies is never `(0, 0)`, since that point is off the curve. -/
theorem isValid_eq_true_iff (bytes : List UInt8) :
    isValid bytes = true ↔
      ∃ (hx : bytesToNat ((bytes.drop 96).take 32) < Fp.modulus)
        (hy : bytesToNat (bytes.drop 128) < Fp.modulus),
        verify (.affine ⟨_, hx⟩ ⟨_, hy⟩) (bytesToNat (bytes.take 32))
          (bytesToNat ((bytes.drop 32).take 32))
          (bytesToNat ((bytes.drop 64).take 32)) = true := by
  unfold isValid
  dsimp only
  split_ifs with hx hy
  · constructor
    · intro h
      rw [Bool.and_eq_true] at h
      exact ⟨hx, hy, h.2⟩
    · rintro ⟨hx', hy', hv⟩
      rw [Bool.and_eq_true]
      exact ⟨not_zero_of_verify hv, hv⟩
  · constructor
    · intro h
      cases h
    · rintro ⟨_, hy', _⟩
      exact absurd hy' hy
  · constructor
    · intro h
      cases h
    · rintro ⟨hx', _, _⟩
      exact absurd hx' hx

private theorem valid_ne_empty : VALID ≠ ByteArray.empty := by
  decide

/-- A call returns the word 1 exactly when three conditions hold.

It has at least 6900 gas, its input has 160 bytes, and the input check accepts them. -/
theorem p256Verify_eq_ok_valid_iff (data : ByteArray) (gas : Nat) :
    p256Verify data gas = .ok VALID ↔
      GAS_P256VERIFY ≤ gas ∧ data.size = INPUT_BYTES ∧ isValid data.data.toList = true := by
  unfold p256Verify
  by_cases hgas : gas < GAS_P256VERIFY
  · simp [hgas, Nat.not_le.mpr hgas]
  · simp only [hgas, Nat.not_lt.mp hgas, ↓reduceIte, true_and]
    by_cases hsize : data.size = INPUT_BYTES
    · simp only [hsize, ne_eq, not_true_eq_false, ↓reduceIte, true_and]
      by_cases hv : isValid data.data.toList = true
      · simp [hv]
      · simp [hv, valid_ne_empty.symm]
    · simp [hsize, valid_ne_empty.symm]

/-- A call returns empty output exactly when it has at least 6900 gas and rejects its input.

It rejects the input when its length is not 160 or the input check fails. -/
theorem p256Verify_eq_ok_empty_iff (data : ByteArray) (gas : Nat) :
    p256Verify data gas = .ok .empty ↔
      GAS_P256VERIFY ≤ gas ∧ (data.size ≠ INPUT_BYTES ∨ isValid data.data.toList = false) := by
  unfold p256Verify
  by_cases hgas : gas < GAS_P256VERIFY
  · simp [hgas, Nat.not_le.mpr hgas]
  · simp only [hgas, Nat.not_lt.mp hgas, ↓reduceIte, true_and]
    by_cases hsize : data.size = INPUT_BYTES
    · simp only [hsize, ne_eq, not_true_eq_false, ↓reduceIte, false_or]
      cases hv : isValid data.data.toList
      · simp
      · simp [valid_ne_empty]
    · simp [hsize]

private theorem callData_list (e r s qx qy : Nat) :
    (callData e r s qx qy).data.toList =
      natToBytes 32 e ++ (natToBytes 32 r ++ (natToBytes 32 s ++
        (natToBytes 32 qx ++ natToBytes 32 qy))) := by
  simp [callData, List.append_assoc]

private theorem isValid_callData_mod (e r s qx qy : Nat) :
    isValid (callData e r s qx qy).data.toList =
      if hx : qx % 2 ^ 256 < Fp.modulus then
        if hy : qy % 2 ^ 256 < Fp.modulus then
          !(qx % 2 ^ 256 = 0 ∧ qy % 2 ^ 256 = 0)
            && verify (.affine ⟨qx % 2 ^ 256, hx⟩ ⟨qy % 2 ^ 256, hy⟩)
              (e % 2 ^ 256) (r % 2 ^ 256) (s % 2 ^ 256)
        else false
      else false := by
  rw [callData_list]
  unfold isValid
  simp [List.drop_append, natToBytes_length, List.drop_eq_nil_of_le, bytesToNat_natToBytes]

/-- On call data with an affine key, the input check gives the result of ECDSA verification.

The hash, `r` and `s` each fit in 32 bytes. -/
theorem isValid_callData {e r s : Nat} (he : e < 2 ^ 256) (hr : r < 2 ^ 256) (hs : s < 2 ^ 256)
    (qx qy : Fp) :
    isValid (callData e r s qx.val qy.val).data.toList = verify (.affine qx qy) e r s := by
  have hqx : qx.val < 2 ^ 256 := Nat.lt_trans qx.isLt (by decide)
  have hqy : qy.val < 2 ^ 256 := Nat.lt_trans qy.isLt (by decide)
  rw [isValid_callData_mod, Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs,
    Nat.mod_eq_of_lt hqx, Nat.mod_eq_of_lt hqy]
  have hx : qx.val < Fp.modulus := qx.isLt
  have hy : qy.val < Fp.modulus := qy.isLt
  rw [dite_eq_left hx, dite_eq_left hy]
  simp only [Fin.eta]
  cases hv : verify (.affine qx qy) e r s
  · simp
  · rw [Bool.and_true]
    exact not_zero_of_verify hv

/-- A call on five words returns the word 1 exactly when three conditions hold.

The call has at least 6900 gas.

Both coordinates of the key lie below `p`.

The signature verifies under that key.

The hash, `r`, `s` and the two coordinates each fit in 32 bytes, from EIP-7951, Input. -/
theorem p256Verify_callData_eq_ok_valid_iff {e r s qx qy : Nat} (he : e < 2 ^ 256)
    (hr : r < 2 ^ 256) (hs : s < 2 ^ 256) (hqx : qx < 2 ^ 256) (hqy : qy < 2 ^ 256) (gas : Nat) :
    p256Verify (callData e r s qx qy) gas = .ok VALID ↔
      GAS_P256VERIFY ≤ gas ∧
        ∃ (hx : qx < Fp.modulus) (hy : qy < Fp.modulus),
          verify (.affine ⟨qx, hx⟩ ⟨qy, hy⟩) e r s = true := by
  rw [p256Verify_eq_ok_valid_iff, callData_size, isValid_callData_mod, Nat.mod_eq_of_lt he,
    Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hqx, Nat.mod_eq_of_lt hqy]
  simp only [true_and]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    by_cases hx : qx < Fp.modulus
    · by_cases hy : qy < Fp.modulus
      · rw [dite_eq_left hx, dite_eq_left hy, Bool.and_eq_true] at h
        exact ⟨hx, hy, h.2⟩
      · rw [dite_eq_left hx, dite_eq_right hy] at h
        cases h
    · rw [dite_eq_right hx] at h
      cases h
  · rintro ⟨hx, hy, hv⟩
    rw [dite_eq_left hx, dite_eq_left hy, Bool.and_eq_true]
    exact ⟨not_zero_of_verify hv, hv⟩

/-- A call returns the word 1 when the signature verifies under an affine key.

The hash fits in 32 bytes, and the call has at least 6900 gas.

A valid signature already has `r` and `s` below `n`, so both fit in 32 bytes. -/
theorem p256Verify_callData_of_verify {qx qy : Fp} {e r s gas : Nat} (he : e < 2 ^ 256)
    (hgas : GAS_P256VERIFY ≤ gas) (hv : verify (.affine qx qy) e r s = true) :
    p256Verify (callData e r s qx.val qy.val) gas = .ok VALID := by
  have hrng := verify_range hv
  have hr : r < 2 ^ 256 := Nat.lt_trans hrng.1.2 (by decide)
  have hs : s < 2 ^ 256 := Nat.lt_trans hrng.2.2 (by decide)
  rw [p256Verify_callData_eq_ok_valid_iff he hr hs (Nat.lt_trans qx.isLt (by decide))
    (Nat.lt_trans qy.isLt (by decide))]
  exact ⟨hgas, qx.isLt, qy.isLt, by simpa [Fin.eta] using hv⟩

/-- A signature from SEC 1 v2 §4.1.3 returns the word 1 under its public key.

`d` is nonzero, and `k G` is an affine point with x-coordinate `rx`, so `k` is nonzero.

The hash `e` fits in 32 bytes, `r = rx mod n`, and `s = k^(-1) (e + r d)`.

Neither `r` nor `s` is zero, and `Q = d G` is the affine key `(qx, qy)`.

The call has at least 6900 gas. -/
theorem p256Verify_callData_sign (d k : Fn) {e : Nat} (he : e < 2 ^ 256) (hd : d ≠ 0)
    {rx ry qx qy : Fp} (hR : Point.mul k Point.generator = .affine rx ry)
    (hr : rx.val % Fn.modulus ≠ 0)
    (hs : Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (rx.val % Fn.modulus) * d) ≠ 0)
    (hQ : Point.mul d Point.generator = .affine qx qy) {gas : Nat} (hgas : GAS_P256VERIFY ≤ gas) :
    p256Verify (callData e (rx.val % Fn.modulus)
      (Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (rx.val % Fn.modulus) * d)).val
      qx.val qy.val) gas = .ok VALID :=
  p256Verify_callData_of_verify he hgas (hQ ▸ verify_sign d k e hd hR hr hs)

/-- For `s` in `(0, n)`, `(r, s)` and `(r, n - s)` give the same result at every gas limit.

EIP-7951 states this in its Malleability section.

Either both signatures are valid or neither is, so the call does not require a low `s`. -/
theorem p256Verify_callData_neg_s (e r qx qy : Nat) {s : Nat} (hs : 0 < s ∧ s < Fn.modulus)
    (gas : Nat) :
    p256Verify (callData e r (Fn.modulus - s) qx qy) gas =
      p256Verify (callData e r s qx qy) gas := by
  have hs' : Fn.modulus - s < 2 ^ 256 := by
    have : Fn.modulus - s ≤ Fn.modulus := Nat.sub_le _ _
    exact Nat.lt_of_le_of_lt this (by decide)
  have hs256 : s < 2 ^ 256 := Nat.lt_trans hs.2 (by decide)
  unfold p256Verify
  split
  · rfl
  simp only [callData_size, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [isValid_callData_mod, isValid_callData_mod, Nat.mod_eq_of_lt hs', Nat.mod_eq_of_lt hs256]
  congr 1
  by_cases hx : qx % 2 ^ 256 < Fp.modulus
  · by_cases hy : qy % 2 ^ 256 < Fp.modulus
    · rw [dite_eq_left hx, dite_eq_left hy, dite_eq_left hx, dite_eq_left hy]
      rw [verify_neg_s _ _ _ hs]
    · rw [dite_eq_left hx, dite_eq_right hy, dite_eq_left hx, dite_eq_right hy]
  · rw [dite_eq_right hx, dite_eq_right hx]

/-- Some call data returns the word 1 with 6900 gas.

The witness signs the hash 0 with the private key 1 and the nonce 1.

So the key and `R` are both the base point. -/
theorem exists_p256Verify_eq_ok_valid :
    ∃ data : ByteArray, p256Verify data GAS_P256VERIFY = .ok VALID := by
  let d : Fn := 1
  let k : Fn := 1
  let gx : Fp := match Point.generator with | .affine x _ => x | .infinity => 0
  let gy : Fp := match Point.generator with | .affine _ y => y | .infinity => 0
  have hG : Point.generator = .affine gx gy := rfl
  -- `1 G = G` in the group, so the proof does not run the 256-step scalar multiplication.
  have hmul : Point.mul k Point.generator = Point.generator := by
    apply (Point.toPoint_inj (Point.isOnCurve_mul k Point.isOnCurve_generator)
      Point.isOnCurve_generator).mp
    rw [Point.toPoint_mul' k Point.isOnCurve_generator]
    change Fn.toZMod 1 • Point.toPoint Point.generator = Point.toPoint Point.generator
    rw [Fn.toZMod_one, one_smul]
  have hR : Point.mul k Point.generator = .affine gx gy := hmul.trans hG
  have hr : gx.val % Fn.modulus ≠ 0 := by decide
  have hs : Fn.inv k * (Fin.ofNat _ 0 + Fin.ofNat _ (gx.val % Fn.modulus) * d) ≠ 0 := by
    intro h
    have h0 := congrArg Fn.toZMod h
    simp only [k, d, map_mul, map_add, Fn.toZMod_inv, Fn.toZMod_one, inv_one, one_mul,
      mul_one] at h0
    have h0' : Fn.toZMod (Fin.ofNat Fn.modulus (gx.val % Fn.modulus)) = 0 := by
      simpa using h0
    have hfin : (Fin.ofNat Fn.modulus (gx.val % Fn.modulus) : Fn) = 0 :=
      Fn.toZMod.injective (h0'.trans Fn.toZMod_zero.symm)
    have hval : (gx.val % Fn.modulus) % Fn.modulus = 0 := congrArg Fin.val hfin
    rw [Nat.mod_mod] at hval
    exact hr hval
  exact ⟨_, p256Verify_callData_sign d k (by decide) (by decide) hR hr hs hR (Nat.le_refl _)⟩

/-- Two errors with one code come from one constructor. -/
theorem P256VerifyError.code_injective (e₁ e₂ : P256VerifyError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- The error type has one constructor, so both errors have its index.
  cases e₁
  cases e₂
  rfl

end EthLib.Execution.Evm.Precompiles.P256Verify
