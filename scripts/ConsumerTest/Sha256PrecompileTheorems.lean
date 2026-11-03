import Lean
import EthLib.Execution.Proofs.Evm.Precompiles.Sha256

/-!
A theorem consumer of the SHA-256 precompile.

Each theorem holds for every call data and gas, and uses only the public theorems.

The last command lists the axioms of every declaration in the precompile namespace and in this file.
It fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

`scripts/test_module_system.sh` checks this file with warnings as errors.
-/

namespace ConsumerTest.Sha256PrecompileTheorems

open EthLib.Execution.Evm.Precompiles.Sha256

/-- A successful call had enough gas, and returned the digest. -/
theorem ok_forward (data : ByteArray) (gas : Nat) (out : ByteArray) (h : sha256 data gas = .ok out) :
    gasCost data.size ≤ gas ∧ out = EthLib.Cryptography.Hash.sha256 data :=
  (sha256_eq_ok_iff data gas out).mp h

/-- Exactly the price succeeds, for every call data. -/
theorem exact_price_succeeds (data : ByteArray) :
    sha256 data (gasCost data.size) = .ok (EthLib.Cryptography.Hash.sha256 data) :=
  (sha256_eq_ok_iff _ _ _).mpr ⟨Nat.le_refl _, rfl⟩

/-- One gas below the price fails, for every call data. -/
theorem one_below_fails (data : ByteArray) :
    sha256 data (gasCost data.size - 1) =
      .error (.outOfGas (gasCost data.size) (gasCost data.size - 1)) := by
  -- The price is at least 60, so one less is strictly below it.
  have positive : 0 < gasCost data.size := by rw [gasCost_eq]; omega
  exact (sha256_eq_error_iff _ _ _).mpr ⟨by omega, rfl⟩

/-- Every call either returns an output or runs out of gas. -/
theorem ok_or_error (data : ByteArray) (gas : Nat) :
    (∃ out, sha256 data gas = .ok out) ∨ sha256 data gas = .error (.outOfGas (gasCost data.size) gas) := by
  by_cases enough : gasCost data.size ≤ gas
  · exact .inl ⟨_, (sha256_eq_ok_iff _ _ _).mpr ⟨enough, rfl⟩⟩
  · exact .inr ((sha256_eq_error_iff _ _ _).mpr ⟨by omega, rfl⟩)

/-- A call with less gas than the price returns no output. -/
theorem short_gas_no_output (data : ByteArray) (gas : Nat) (short : gas < gasCost data.size)
    (out : ByteArray) : sha256 data gas ≠ .ok out := fun h => by
  have := ((sha256_eq_ok_iff _ _ _).mp h).1
  omega

/-- More gas never turns a success into a failure, and keeps the output. -/
theorem more_gas (data : ByteArray) (gas extra : Nat) (out : ByteArray) (h : sha256 data gas = .ok out) :
    sha256 data (gas + extra) = .ok out := by
  obtain ⟨enough, same⟩ := (sha256_eq_ok_iff _ _ _).mp h
  exact (sha256_eq_ok_iff _ _ _).mpr ⟨by omega, same⟩

/-- Below `60 + 12 * 2^56` gas, every output is a 32-byte FIPS 180-4 digest. -/
theorem ok_fips (data : ByteArray) (gas : Nat) (out : ByteArray) (h : sha256 data gas = .ok out)
    (bounded : gas < 864691128455135292) :
    out.size = 32 ∧ out = EthLib.Cryptography.Hash.Sha256.Spec.hash data :=
  ⟨sha256_ok_size h, sha256_ok_eq_spec_of_gas h (by rw [gasCost_admitted]; exact bounded)⟩

/-- The word count is the least number of words that covers the call data. -/
theorem words_exact (size words : Nat) : wordCount size ≤ words ↔ size ≤ 32 * words :=
  ⟨fun le => Nat.le_trans (le_wordCount size) (Nat.mul_le_mul_left 32 le), wordCount_le⟩

end ConsumerTest.Sha256PrecompileTheorems

open Lean Elab Command in
/-- List the axioms of every declaration under the two prefixes, and fail on any non-standard one. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let prefixes := [`EthLib.Execution.Evm.Precompiles.Sha256, `ConsumerTest.Sha256PrecompileTheorems]
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let names := env.constants.toList.filterMap fun (n, _) =>
    if prefixes.any (·.isPrefixOf n) && !n.isInternal then some n else none
  let names := names.toArray.qsort (·.toString < ·.toString)
  let mut bad : Nat := 0
  for n in names do
    let axioms ← liftCoreM (collectAxioms n)
    unless (axioms.filter (!allowed.contains ·)).isEmpty do bad := bad + 1
    logInfo m!"{n}: {axioms.toList}"
  logInfo m!"audited {names.size} declarations, {bad} with non-standard axioms"
  if bad > 0 then throwError "non-standard axioms found"

#audit_axioms
