import Lean
import EthLib.Execution.Proofs.Evm.Precompiles.Identity
import EthLib.Execution.Exports.Identity

/-!
A theorem consumer of the IDENTITY precompile.

Each theorem holds for all values of its arguments, such as call data, gas or a length.
Each proof uses only the public theorems.
The consumer applies both directions of `identity_eq_ok_iff` and of `identity_eq_error_iff`.
It also applies each public theorem of the word count and of the price.
`known_answers` applies the eight known answers, which are closed statements.

The last command checks the consumer and audits the axioms:

- Each public theorem of the two proof modules must occur in the proof of a theorem of this file.
- Each declaration of the five IDENTITY and word-count modules, and of this file, may use only `propext`, `Classical.choice` and `Quot.sound`.
- The five modules include the C exports, which this file imports for the audit only.

`scripts/test_module_system.sh` checks this file with warnings as errors.
-/

namespace ConsumerTest.IdentityTheorems

open EthLib.Execution.Evm
open EthLib.Execution.Evm.Precompiles.Identity

/-- A successful call had enough gas, and returned the call data. -/
theorem ok_forward (data : ByteArray) (gas : Nat) (out : ByteArray) (h : identity data gas = .ok out) :
    gasCost data.size ≤ gas ∧ out = data :=
  (identity_eq_ok_iff data gas out).mp h

/-- Every call with at least the price returns the call data. -/
theorem ok_backward (data : ByteArray) (gas : Nat) (enough : gasCost data.size ≤ gas) :
    identity data gas = .ok data :=
  (identity_eq_ok_iff data gas data).mpr ⟨enough, rfl⟩

/-- A failed call had less gas than the price, and its error carries both. -/
theorem error_forward (data : ByteArray) (gas : Nat) (e : IdentityError) (h : identity data gas = .error e) :
    gas < gasCost data.size ∧ e = .outOfGas (gasCost data.size) gas :=
  (identity_eq_error_iff data gas e).mp h

/-- Exactly the price succeeds, for all call data. -/
theorem exact_price_succeeds (data : ByteArray) : identity data (gasCost data.size) = .ok data :=
  ok_backward data _ (Nat.le_refl _)

/-- One gas below the price fails, for all call data. -/
theorem one_below_fails (data : ByteArray) :
    identity data (gasCost data.size - 1) =
      .error (.outOfGas (gasCost data.size) (gasCost data.size - 1)) := by
  -- The price is at least 15, so one less is strictly below it.
  have := gasCost_base_le data.size
  exact (identity_eq_error_iff _ _ _).mpr ⟨by simp only [GAS_BASE] at this; omega, rfl⟩

/-- Every call either returns the call data or runs out of gas, and never both. -/
theorem ok_xor_error (data : ByteArray) (gas : Nat) :
    (identity data gas = .ok data ∧ gasCost data.size ≤ gas) ∨
      (identity data gas = .error (.outOfGas (gasCost data.size) gas) ∧ gas < gasCost data.size) := by
  by_cases enough : gasCost data.size ≤ gas
  · exact .inl ⟨ok_backward data gas enough, enough⟩
  · exact .inr ⟨(identity_eq_error_iff _ _ _).mpr ⟨by omega, rfl⟩, by omega⟩

/-- Success is decided by the gas alone: the call succeeds exactly when the gas covers the price. -/
theorem succeeds_iff (data : ByteArray) (gas : Nat) :
    (∃ out, identity data gas = .ok out) ↔ gasCost data.size ≤ gas :=
  ⟨fun ⟨out, h⟩ => (ok_forward data gas out h).1, fun enough => ⟨data, ok_backward data gas enough⟩⟩

/-- A call with less gas than the price returns no output. -/
theorem short_gas_no_output (data : ByteArray) (gas : Nat) (short : gas < gasCost data.size)
    (out : ByteArray) : identity data gas ≠ .ok out := fun h => by
  have := (ok_forward data gas out h).1
  omega

/-- More gas never turns a success into a failure, and keeps the output. -/
theorem more_gas (data : ByteArray) (gas extra : Nat) (out : ByteArray) (h : identity data gas = .ok out) :
    identity data (gas + extra) = .ok out := by
  obtain ⟨enough, same⟩ := ok_forward data gas out h
  exact (identity_eq_ok_iff _ _ _).mpr ⟨by omega, same⟩

/-- Every output keeps the length and each byte of the call data. -/
theorem bytes_preserved (data : ByteArray) (gas : Nat) (out : ByteArray) (h : identity data gas = .ok out) :
    out.size = data.size ∧ ∀ i : Nat, out[i]? = data[i]? :=
  ⟨identity_ok_size h, identity_ok_getElem? h⟩

/-- The word count is the least number of EVM words that covers the call data. -/
theorem words_exact (size words : Nat) : wordCount size ≤ words ↔ size ≤ 32 * words :=
  wordCount_le_iff size words

/-- At every EVM word boundary, the next byte raises the price by exactly 3. -/
theorem boundary_step (k : Nat) : gasCost (32 * k + 1) = gasCost (32 * k) + 3 := by
  rw [gasCost_mul, gasCost_mul_add_one]
  omega

/-- For call data shorter than 2^64 bytes, the price that the C export returns as `UInt64` is exact. -/
theorem export_price_exact (data : ByteArray) (bounded : data.size < 2 ^ 64) :
    (UInt64.ofNat (gasCost data.size)).toNat = gasCost data.size :=
  toNat_ofNat_gasCost bounded

/-- `ceil32` is a multiple of 32, at least its argument, less than 32 above it, and the least such multiple. -/
theorem ceil32_spec (value : Nat) :
    ceil32 value % 32 = 0 ∧ value ≤ ceil32 value ∧ ceil32 value < value + 32 ∧
      ∀ bound, bound % 32 = 0 → value ≤ bound → ceil32 value ≤ bound :=
  ⟨ceil32_mod value, le_ceil32 value, ceil32_lt value, fun _ multiple above => ceil32_le multiple above⟩

/-- The word count times 32 is `ceil32`, by the closed forms of both. -/
theorem wordCount_closed (size : Nat) : 32 * wordCount size = ceil32 size := by
  rw [wordCount_eq, ceil32_eq]

/-- The EVM words of the call data cover it, and every cover has at least as many words. -/
theorem words_cover_least (data : ByteArray) (words : Nat) (covers : data.size ≤ 32 * words) :
    data.size ≤ 32 * wordCount data.size ∧ wordCount data.size ≤ words :=
  ⟨le_wordCount data.size, wordCount_le covers⟩

/-- Empty call data has no EVM word, and costs the base price alone. -/
theorem empty_base : wordCount ByteArray.empty.size = 0 ∧ gasCost ByteArray.empty.size = GAS_BASE :=
  ⟨wordCount_zero, by rw [gasCost_eq]; rfl⟩

/-- The price of all call data is the source formula, `15 + 3 * ceil(len / 32)`. -/
theorem price_formula (data : ByteArray) :
    gasCost data.size = GAS_BASE + GAS_PER_WORD * ((data.size + 31) / 32) := by
  rw [gasCost_eq]
  rfl

/-- Appending bytes never lowers the word count or the price. -/
theorem append_monotone (data more : ByteArray) :
    wordCount data.size ≤ wordCount (data ++ more).size ∧ gasCost data.size ≤ gasCost (data ++ more).size := by
  have le : data.size ≤ (data ++ more).size := by
    rw [ByteArray.size_append]
    omega
  exact ⟨wordCount_mono le, gasCost_mono le⟩

/-- If a call succeeds, each prefix of its call data also succeeds with the same gas. -/
theorem prefix_succeeds (data more : ByteArray) (gas : Nat) (out : ByteArray)
    (h : identity (data ++ more) gas = .ok out) : identity data gas = .ok data :=
  ok_backward data gas (Nat.le_trans (append_monotone data more).2 (ok_forward _ _ _ h).1)

/-- At every EVM word boundary, the next byte starts exactly one more EVM word. -/
theorem word_boundary (k : Nat) : wordCount (32 * k + 1) = wordCount (32 * k) + 1 := by
  rw [wordCount_mul, wordCount_mul_add_one]

/-- The price of call data shorter than 2^64 bytes is below 2^64. -/
theorem price_fits (data : ByteArray) (bounded : data.size < 2 ^ 64) : gasCost data.size < 2 ^ 64 :=
  gasCost_lt_two_pow_64 bounded

/-- For all call data, exactly the price succeeds and one gas less fails. -/
theorem threshold (data : ByteArray) :
    identity data (gasCost data.size) = .ok data ∧
      identity data (gasCost data.size - 1) =
        .error (.outOfGas (gasCost data.size) (gasCost data.size - 1)) := by
  -- The price is at least 15, so one less is strictly below it.
  have := gasCost_base_le data.size
  exact ⟨identity_ok data _ (Nat.le_refl _),
    identity_out_of_gas data _ (by simp only [GAS_BASE] at this; omega)⟩

/-- The known answers at 0, 1, 32 and 33 bytes, each at exactly the price and at one gas less. -/
theorem known_answers :
    identity ByteArray.empty 15 = .ok ByteArray.empty ∧
      identity ByteArray.empty 14 = .error (.outOfGas 15 14) ∧
      identity ⟨#[0xff]⟩ 18 = .ok ⟨#[0xff]⟩ ∧ identity ⟨#[0xff]⟩ 17 = .error (.outOfGas 18 17) ∧
      identity bytes32 18 = .ok bytes32 ∧ identity bytes32 17 = .error (.outOfGas 18 17) ∧
      identity bytes33 21 = .ok bytes33 ∧ identity bytes33 20 = .error (.outOfGas 21 20) :=
  ⟨identity_empty, identity_empty_out_of_gas, identity_one, identity_one_out_of_gas,
    identity_32, identity_32_out_of_gas, identity_33, identity_33_out_of_gas⟩

end ConsumerTest.IdentityTheorems

open Lean Elab Command in
/-- Check that the consumer applies each public theorem, then audit the axioms of every declaration. -/
elab "#audit_axioms" : command => do
  let env ← getEnv
  let consumer := `ConsumerTest.IdentityTheorems
  -- The modules of the IDENTITY precompile and of the word count, with the C exports.
  let modules := [`EthLib.Execution.Evm.Words, `EthLib.Execution.Evm.Precompiles.Identity,
    `EthLib.Execution.Proofs.Evm.Words, `EthLib.Execution.Proofs.Evm.Precompiles.Identity,
    `EthLib.Execution.Exports.Identity]
  let proofModules := [`EthLib.Execution.Proofs.Evm.Words, `EthLib.Execution.Proofs.Evm.Precompiles.Identity]
  let moduleOf (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!
  -- Lean generates these theorems for definitions and constructors, so no consumer must apply them.
  let generated (n : Name) : Bool :=
    n.isInternal || match n with
      | .str _ s => ["eq_1", "eq_def", "inj", "injEq", "sizeOf_spec"].contains s
      | _ => false
  -- Every constant that a proof in this file names, including its auxiliary proofs.
  let mut used : NameSet := {}
  for (n, info) in env.constants.toList do
    if consumer.isPrefixOf n then
      let value : Option Expr := match info with
        | .thmInfo v => some v.value
        | .defnInfo v => some v.value
        | _ => none
      for c in (value.map Expr.getUsedConstants).getD #[] do used := used.insert c
  let mut required : Array Name := #[]
  let mut audited : Array Name := #[]
  for (n, info) in env.constants.toList do
    let inModules := (moduleOf n).any modules.contains
    if (inModules || consumer.isPrefixOf n) && !n.isInternal then audited := audited.push n
    if (moduleOf n).any proofModules.contains && info matches .thmInfo _ && !generated n then
      required := required.push n
  let publicTheorems := required.qsort (·.toString < ·.toString)
  let unused := publicTheorems.filter (!used.contains ·)
  for n in publicTheorems do
    logInfo m!"applied {n}: {used.contains n}"
  logInfo m!"{publicTheorems.size} public theorems, {unused.size} not applied by a consumer theorem"
  if !unused.isEmpty then throwError "public theorems not applied: {unused.toList}"
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let auditedSorted := audited.qsort (·.toString < ·.toString)
  let mut bad : Nat := 0
  for n in auditedSorted do
    let axioms ← liftCoreM (collectAxioms n)
    unless (axioms.filter (!allowed.contains ·)).isEmpty do bad := bad + 1
    logInfo m!"{n}: {axioms.toList}"
  logInfo m!"audited {auditedSorted.size} declarations, {bad} with non-standard axioms"
  if bad > 0 then throwError "non-standard axioms found"

#audit_axioms
