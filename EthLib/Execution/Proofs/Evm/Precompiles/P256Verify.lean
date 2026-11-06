module

public import EthLib.Execution.Evm.Precompiles.P256Verify
import EthLib.Base.Proofs.BigEndian
import EthLib.Cryptography.Proofs.Secp256r1.Ecdsa

/-!
# Proofs: `Evm.Precompiles.P256Verify`

- The call fails exactly when the gas is below 6900.
- With enough gas, a wrong length gives empty output, and every output is the word 1 or empty.
- With enough gas, the call returns the word 1 on 160 valid bytes, and empty output otherwise.
- The 160-byte call data of EIP-7951 reads back as its hash, signature and public key.
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

It concatenates `e`, `r`, `s`, `qx` and `qy` as 32-byte big-endian words. -/
def callData (e r s qx qy : Nat) : ByteArray :=
  ⟨(natToBytes 32 e ++ natToBytes 32 r ++ natToBytes 32 s ++ natToBytes 32 qx
    ++ natToBytes 32 qy).toArray⟩

/-- The call data of a signature has 160 bytes. -/
theorem callData_size (e r s qx qy : Nat) : (callData e r s qx qy).size = INPUT_BYTES := by
  simp [callData, INPUT_BYTES, ByteArray.size, natToBytes_length]

/-- `(0, 0)` does not lie on secp256r1, so EIP-7951 uses it for the point at infinity. -/
theorem isOnCurve_zero : (Point.affine 0 0).isOnCurve = false := by
  decide

/-- `(0, 0)` verifies no signature, since it does not lie on the curve. -/
theorem verify_ne_zero {qx qy : Fp} {e r s : Nat} (h : verify (.affine qx qy) e r s = true) :
    ¬(qx.val = 0 ∧ qy.val = 0) := by
  rintro ⟨hx, hy⟩
  have hqx : qx = 0 := Fin.ext hx
  have hqy : qy = 0 := Fin.ext hy
  have h0 : (Point.affine qx qy).isOnCurve = false := by
    rw [hqx, hqy]
    exact isOnCurve_zero
  rw [verify_of_not_isOnCurve h0] at h
  cases h

/-- The input check of EIP-7951, Signature Verification Algorithm, accepts valid keys.

The coordinates of the key lie below `p`, are not both 0, and pass `verify`. -/
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
      exact ⟨decide_eq_false_iff_not.mpr (verify_ne_zero hv) ▸ rfl, hv⟩
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

/-- A call returns the word 1 on 160 valid bytes with 6900 gas, from EIP-7951, Gas Schedule. -/
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

/-- With enough gas, a call returns empty output when the length is not 160 or the check fails. -/
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
  have h32 : ∀ n, (natToBytes 32 n).length = 32 := natToBytes_length 32
  have hp256 : (256 : Nat) ^ 32 = 2 ^ 256 := by decide
  rw [callData_list]
  unfold isValid
  have ht0 : (natToBytes 32 e ++ (natToBytes 32 r ++ (natToBytes 32 s ++
      (natToBytes 32 qx ++ natToBytes 32 qy)))).take 32 = natToBytes 32 e :=
    List.take_left' (h32 e)
  have hd32 : (natToBytes 32 e ++ (natToBytes 32 r ++ (natToBytes 32 s ++
      (natToBytes 32 qx ++ natToBytes 32 qy)))).drop 32 =
      natToBytes 32 r ++ (natToBytes 32 s ++ (natToBytes 32 qx ++ natToBytes 32 qy)) :=
    List.drop_left' (h32 e)
  have hd64 : (natToBytes 32 e ++ (natToBytes 32 r ++ (natToBytes 32 s ++
      (natToBytes 32 qx ++ natToBytes 32 qy)))).drop 64 =
      natToBytes 32 s ++ (natToBytes 32 qx ++ natToBytes 32 qy) := by
    rw [show (64 : Nat) = 32 + 32 from rfl, ← List.drop_drop, hd32, List.drop_left' (h32 r)]
  have hd96 : (natToBytes 32 e ++ (natToBytes 32 r ++ (natToBytes 32 s ++
      (natToBytes 32 qx ++ natToBytes 32 qy)))).drop 96 =
      natToBytes 32 qx ++ natToBytes 32 qy := by
    rw [show (96 : Nat) = 64 + 32 from rfl, ← List.drop_drop, hd64, List.drop_left' (h32 s)]
  have hd128 : (natToBytes 32 e ++ (natToBytes 32 r ++ (natToBytes 32 s ++
      (natToBytes 32 qx ++ natToBytes 32 qy)))).drop 128 = natToBytes 32 qy := by
    rw [show (128 : Nat) = 96 + 32 from rfl, ← List.drop_drop, hd96, List.drop_left' (h32 qx)]
  rw [ht0, hd32, hd64, hd96, hd128, List.take_left' (h32 r), List.take_left' (h32 s),
    List.take_left' (h32 qx)]
  dsimp only
  simp only [bytesToNat_natToBytes, hp256]

/-- On the 160 bytes of a public key, `isValid` runs `verify`, from EIP-7951, Input.

The hash and the signature fit in 32 bytes.

The key `(0, 0)` fails both sides, since it does not lie on the curve. -/
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
  · exact decide_eq_false_iff_not.mpr (verify_ne_zero hv) ▸ rfl

/-- A call of five 32-byte words returns the word 1 with 6900 gas when `verify` accepts the key.

The words are the hash, the signature and the two coordinates, from EIP-7951, Input. -/
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
    exact ⟨decide_eq_false_iff_not.mpr (verify_ne_zero hv) ▸ rfl, hv⟩

/-- A call returns the word 1 when `verify` accepts the public key, from EIP-7951, Input.

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

/-- A nonzero scalar gives an affine public key: `d G` is not the point at infinity. -/
theorem exists_mul_generator_eq_affine {d : Fn} (hd : d ≠ 0) :
    ∃ qx qy : Fp, Point.mul d Point.generator = .affine qx qy := by
  have hne : Point.mul d Point.generator ≠ .infinity := by
    intro h
    have h0 := congrArg Point.toPoint h
    rw [Point.toPoint_mul' d Point.isOnCurve_generator, Point.toPoint_infinity, smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact hd (Fn.toZMod.injective (h0.trans (map_zero _).symm))
    · exact Point.toPoint_generator_ne_zero h0
  cases hq : Point.mul d Point.generator with
  | infinity => exact absurd hq hne
  | affine qx qy => exact ⟨qx, qy, rfl⟩

/-- A signature from SEC 1 v2 §4.1.3 returns the word 1 under its public key.

The private key `d` and the nonce `k` are nonzero, and the hash `e` fits in 32 bytes.

`R = k G` has coordinate `rx`, `r = rx mod n`, and `s = k^(-1) (e + r d)`.

Neither `r` nor `s` is zero, `Q = d G` is the affine key `(qx, qy)`, and the call has 6900 gas. -/
theorem p256Verify_callData_sign (d k : Fn) {e : Nat} (he : e < 2 ^ 256) (hd : d ≠ 0)
    {rx ry qx qy : Fp} (hR : Point.mul k Point.generator = .affine rx ry)
    (hr : rx.val % Fn.modulus ≠ 0)
    (hs : Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (rx.val % Fn.modulus) * d) ≠ 0)
    (hQ : Point.mul d Point.generator = .affine qx qy) {gas : Nat} (hgas : GAS_P256VERIFY ≤ gas) :
    p256Verify (callData e (rx.val % Fn.modulus)
      (Fn.inv k * (Fin.ofNat _ e + Fin.ofNat _ (rx.val % Fn.modulus) * d)).val
      qx.val qy.val) gas = .ok VALID :=
  p256Verify_callData_of_verify he hgas (hQ ▸ verify_sign d k e hd hR hr hs)

/-- `(r, s)` and `(r, n - s)` give the same result at every gas limit, from EIP-7951, Malleability.

Both signatures are valid together, so the call does not choose the low one. -/
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

/-- The hypotheses of a valid call are reachable: `d = k = 1` and `e = 0` sign `G` under `G`.

`1 • G = G`, so the witness does not run the 256-step scalar multiplication.

The call returns the word 1, so the valid branch is not vacuous. -/
theorem exists_p256Verify_eq_ok_valid :
    ∃ data : ByteArray, p256Verify data GAS_P256VERIFY = .ok VALID := by
  let d : Fn := 1
  let k : Fn := 1
  let gx : Fp := match Point.generator with | .affine x _ => x | .infinity => 0
  let gy : Fp := match Point.generator with | .affine _ y => y | .infinity => 0
  have hG : Point.generator = .affine gx gy := rfl
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
  -- The only constructor is `outOfGas`, so both errors have its index.
  cases e₁
  cases e₂
  rfl

end EthLib.Execution.Evm.Precompiles.P256Verify
