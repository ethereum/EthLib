module

public import EthLib.Execution.Evm.Precompiles.AltBn128
public import EthLib.Execution.Proofs.Evm.Memory
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: `Evm.Precompiles.AltBn128`

- ECADD and ECMUL fail exactly when the gas is below the price or a point is invalid.
- ECPAIRING succeeds exactly when the gas covers the price and every pair decodes.
- Every decoded point is on the curve.
- Every output of ECADD and ECMUL has 64 bytes, and every output of ECPAIRING is the word 0 or 1.
- ECPAIRING charges its gas before it checks that the call data is a whole number of 192-byte pairs.

The Python suite checks the outputs against py_ecc.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.AltBn128

open EthLib.Cryptography.AltBn128
open EthLib.Base (Fork)
open EthLib.Execution.Evm (bufferRead gasSchedule)

/-- ECADD runs out of gas below its price. -/
theorem ecadd_outOfGas (fork : Fork) (data : ByteArray) {gas : Nat}
    (hgas : gas < (gasSchedule fork).PRECOMPILE_ECADD) :
    ecadd fork data gas = .error (.outOfGas (gasSchedule fork).PRECOMPILE_ECADD gas) := by
  simp [ecadd, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- ECMUL runs out of gas below its price. -/
theorem ecmul_outOfGas (fork : Fork) (data : ByteArray) {gas : Nat}
    (hgas : gas < (gasSchedule fork).PRECOMPILE_ECMUL) :
    ecmul fork data gas = .error (.outOfGas (gasSchedule fork).PRECOMPILE_ECMUL gas) := by
  simp [ecmul, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- The 64 bytes of a point. -/
theorem length_g1ToBytes : (point : Point) → (g1ToBytes point).length = 64
  | .infinity => by simp [g1ToBytes]
  | .affine _ _ => by simp [g1ToBytes, EthLib.Base.natToBytes_length]

/-- A chain of steps that succeeds succeeded at its first step. -/
theorem bind_eq_ok {α β : Type} {x : Except AltBn128Error α} {f : α → Except AltBn128Error β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- Every output of ECADD has 64 bytes. -/
theorem ecadd_size {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecadd fork data gas = .ok out) :
    out.size = 64 := by
  simp only [ecadd, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_g1ToBytes]

/-- Every output of ECMUL has 64 bytes. -/
theorem ecmul_size {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecmul fork data gas = .ok out) :
    out.size = 64 := by
  simp only [ecmul, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  simp [ByteArray.size, length_g1ToBytes]

/-- A coordinate at or above `p` is rejected. -/
theorem bytesToG1_invalidFieldElement {raw : List UInt8}
    (hx : Fp.modulus ≤ EthLib.Base.bytesToNat (raw.take 32)) :
    bytesToG1 raw = .error .invalidFieldElement := by
  simp [bytesToG1, Nat.not_lt.mpr hx, throw, throwThe, MonadExceptOf.throw]

/-! ## Success -/

/-- A decoded point is on the curve. -/
theorem bytesToG1_isOnCurve {raw : List UInt8} {p : Point} (h : bytesToG1 raw = .ok p) :
    p.isOnCurve = true := by
  simp only [bytesToG1, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · split at h
    · split at h
      · cases h
        rfl
      · split at h
        · cases h
          assumption
        · cases h
    · cases h
  · cases h

/-- ECADD succeeds exactly when the gas covers the price and both points decode. -/
theorem ecadd_eq_ok_iff (fork : Fork) (data : ByteArray) (gas : Nat) (out : ByteArray) :
    ecadd fork data gas = .ok out ↔ (gasSchedule fork).PRECOMPILE_ECADD ≤ gas ∧ ∃ p0 p1,
      bytesToG1 (bufferRead data 0 64) = .ok p0 ∧ bytesToG1 (bufferRead data 64 64) = .ok p1 ∧
      out = ⟨(g1ToBytes (p0 + p1)).toArray⟩ := by
  by_cases hgas : gas < (gasSchedule fork).PRECOMPILE_ECADD
  · simp [ecadd_outOfGas fork data hgas, Nat.not_le.mpr hgas]
  · simp only [ecadd, hgas, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]
    cases h0 : bytesToG1 (bufferRead data 0 64) <;>
      cases h1 : bytesToG1 (bufferRead data 64 64) <;> simp [Nat.not_lt.mp hgas, eq_comm]

/-- ECMUL succeeds exactly when the gas covers the price and the point decodes. -/
theorem ecmul_eq_ok_iff (fork : Fork) (data : ByteArray) (gas : Nat) (out : ByteArray) :
    ecmul fork data gas = .ok out ↔ (gasSchedule fork).PRECOMPILE_ECMUL ≤ gas ∧ ∃ p0,
      bytesToG1 (bufferRead data 0 64) = .ok p0 ∧
      out = ⟨(g1ToBytes
        (Point.mulBits 256 (Base.bytesToNat (bufferRead data 64 32)) p0)).toArray⟩ := by
  by_cases hgas : gas < (gasSchedule fork).PRECOMPILE_ECMUL
  · simp [ecmul_outOfGas fork data hgas, Nat.not_le.mpr hgas]
  · simp only [ecmul, hgas, bind, Except.bind, pure, Except.pure, throw, throwThe,
      MonadExceptOf.throw]
    cases h0 : bytesToG1 (bufferRead data 0 64) <;> simp [Nat.not_lt.mp hgas, eq_comm]

/-! ## ECPAIRING -/

/-- ECPAIRING runs out of gas below its price, before it checks the length. -/
theorem ecpairing_outOfGas (fork : Fork) (data : ByteArray) {gas : Nat}
    (hgas : gas < ecpairingGas fork data.size) :
    ecpairing fork data gas = .error (.outOfGas (ecpairingGas fork data.size) gas) := by
  simp [ecpairing, hgas, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- With enough gas, a length that is not a whole number of pairs fails. -/
theorem ecpairing_invalidInputLength {fork : Fork} {data : ByteArray} {gas : Nat}
    (hgas : ecpairingGas fork data.size ≤ gas)
    (hsize : data.size % 192 ≠ 0) :
    ecpairing fork data gas = .error (.invalidInputLength data.size) := by
  simp [ecpairing, Nat.not_lt.mpr hgas, hsize, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- Every output of ECPAIRING is the word 0 or 1. -/
theorem ecpairing_ok {fork : Fork} {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : ecpairing fork data gas = .ok out) :
    ∃ result : Bool, out = ⟨(List.replicate 31 (0 : UInt8) ++ [if result then 1 else 0]).toArray⟩ := by
  simp only [ecpairing, bind, throw, throwThe, MonadExceptOf.throw] at h
  split at h
  · cases h
  split at h
  · cases h
  obtain ⟨_, _, h⟩ := bind_eq_ok h
  cases h
  exact ⟨_, rfl⟩

/-- ECPAIRING succeeds exactly when the gas covers the price and every pair decodes.

The call data must be a whole number of pairs. -/
theorem ecpairing_eq_ok_iff (fork : Fork) (data : ByteArray) (gas : Nat) (out : ByteArray) :
    ecpairing fork data gas = .ok out ↔ ecpairingGas fork data.size ≤ gas ∧ data.size % 192 = 0 ∧
      ∃ pairs, (List.range (data.size / 192)).mapM (decodePair data) = .ok pairs ∧
        out = ⟨(List.replicate 31 (0 : UInt8) ++
          [if pairingCheck pairs then 1 else 0]).toArray⟩ := by
  by_cases hgas : gas < ecpairingGas fork data.size
  · simp [ecpairing_outOfGas fork data hgas, Nat.not_le.mpr hgas]
  by_cases hsize : data.size % 192 ≠ 0
  · simp [ecpairing_invalidInputLength (Nat.not_lt.mp hgas) hsize, hsize]
  · have hwhole : data.size % 192 = 0 := Decidable.not_not.mp hsize
    simp only [ecpairing, hgas, hsize, bind, Except.bind, pure, Except.pure, ↓reduceIte]
    cases h : (List.range (data.size / 192)).mapM (decodePair data) with
    | error e =>
      constructor
      · intro hok
        cases hok
      · rintro ⟨_, _, _, hpairs, _⟩
        cases hpairs
    | ok pairs =>
      constructor
      · intro hok
        cases hok
        exact ⟨Nat.not_lt.mp hgas, hwhole, pairs, rfl, rfl⟩
      · rintro ⟨_, _, _, hpairs, rfl⟩
        cases hpairs
        rfl

/-- The price of no pair is the base price alone. -/
theorem ecpairingGas_empty : ecpairingGas .istanbul 0 = 45000 := rfl

/-- One pair costs `34000 + 45000 = 79000`. -/
theorem ecpairingGas_one : ecpairingGas .istanbul 192 = 79000 := rfl

end EthLib.Execution.Evm.Precompiles.AltBn128
