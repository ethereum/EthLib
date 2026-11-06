module

public import EthLib.Execution.Exports.Evm

/-!
# Proofs: `Execution.Exports.Evm`

Each export that reads a word, an address or a list of memory ranges checks the length first.

An argument of the wrong length gives the error of that argument.

Arguments of the right lengths give the result that the operation computes from them.

The codes of these errors never meet the codes of an RLP error, so one Python class carries both.

The library of the exports holds this module, since a proof module fails to load compiled exports.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Exports

open EthLib.Base (bytesToNat readBytes)
open EthLib.Serialization.Rlp (RlpError)

/-! ## Error codes -/

/-- Two errors with one code are the same error. -/
theorem ArgumentError.code_injective (e₁ e₂ : ArgumentError) (h : e₁.code = e₂.code) :
    e₁ = e₂ := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ArgumentError.code] at h; exact absurd h (by decide))

/-- An argument error never has the code of an RLP error. -/
theorem ArgumentError.code_ne_rlp (e : ArgumentError) (r : RlpError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [ArgumentError.code, RlpError.code] <;> decide

/-! ## Operands of an instruction -/

/-- An operand of any length but 32 bytes gives the error of an operand. -/
theorem wordOpExport_eq_error_of_size_ne {opcode : UInt8} {a b c : ByteArray}
    (h : a.size ≠ 32 ∨ b.size ≠ 32 ∨ c.size ≠ 32) :
    wordOpExport opcode a b c = .error ArgumentError.operandLength.toResult := by
  by_cases ha : a.size = 32 <;> by_cases hb : b.size = 32 <;> by_cases hc : c.size = 32 <;>
    simp_all [wordOpExport, readWord, bind, Except.bind]

/-- Operands of 32 bytes give the word that the instruction pushes for them. -/
theorem wordOpExport_eq_of_size_eq {opcode : UInt8} {a b c : ByteArray} (ha : a.size = 32)
    (hb : b.size = 32) (hc : c.size = 32) :
    wordOpExport opcode a b c =
      match (Op.decode opcode).bind fun op => wordOp op (wordOf a) (wordOf b) (wordOf c) with
      | some w => .ok (bytesOfWord w)
      | none => .error (0, s!"opcode {opcode} does not push a word of its operands alone") := by
  -- The two sides match on one value with two copies of one matcher.
  simp only [wordOpExport, readWord, ha, hb, hc, ite_true, bind, Except.bind]
  split <;> rename_i h <;> rw [h]

/-! ## Ranges of a memory access -/

/-- Ranges whose length is not a multiple of 64 bytes give the error of the ranges. -/
theorem extendMemoryCostExport_eq_error_of_size {size ranges : ByteArray}
    (h : ranges.size % 64 ≠ 0) :
    extendMemoryCostExport size ranges = .error ArgumentError.rangesLength.toResult := by
  simp [extendMemoryCostExport, readRanges, h, bind, Except.bind]

/-- Ranges of a multiple of 64 bytes give the price of growing the memory for them. -/
theorem extendMemoryCostExport_eq_of_size {size ranges : ByteArray}
    (h : ranges.size % 64 = 0) :
    extendMemoryCostExport size ranges =
      .ok (bytesOfNat (extendMemory (bytesToNat size.toList) (rangesOf ranges)).cost) := by
  simp [extendMemoryCostExport, readRanges, h, bind, Except.bind, pure, Except.pure]

/-- Ranges whose length is not a multiple of 64 bytes give the error of the ranges. -/
theorem extendMemoryExpandByExport_eq_error_of_size {size ranges : ByteArray}
    (h : ranges.size % 64 ≠ 0) :
    extendMemoryExpandByExport size ranges = .error ArgumentError.rangesLength.toResult := by
  simp [extendMemoryExpandByExport, readRanges, h, bind, Except.bind]

/-- Ranges of a multiple of 64 bytes give the number of bytes that the memory grows by. -/
theorem extendMemoryExpandByExport_eq_of_size {size ranges : ByteArray}
    (h : ranges.size % 64 = 0) :
    extendMemoryExpandByExport size ranges =
      .ok (bytesOfNat (extendMemory (bytesToNat size.toList) (rangesOf ranges)).expandBy) := by
  simp [extendMemoryExpandByExport, readRanges, h, bind, Except.bind, pure, Except.pure]

/-! ## Created addresses -/

/-- A sender of any length but 20 bytes gives the error of a sender, for CREATE. -/
theorem createAddressExport_eq_error_of_size_ne {sender nonce : ByteArray}
    (h : sender.size ≠ 20) :
    createAddressExport sender nonce = .error ArgumentError.senderLength.toResult := by
  simp [createAddressExport, readAddress, h, bind, Except.bind]

/-- A sender of 20 bytes gives the CREATE address of that sender, or the error of its preimage. -/
theorem createAddressExport_eq_of_size_eq {sender nonce : ByteArray} (h : sender.size = 20) :
    createAddressExport sender nonce =
      ((createAddress (readBytes sender 0 20 (by omega)) (bytesToNat nonce.toList)).map
        (fun a => ⟨a.toArray⟩)).mapError
        fun e => (e.code, s!"create preimage rejected: {reprStr e}") := by
  simp [createAddressExport, readAddress, h, bind, Except.bind]

/-- With a sender of 20 bytes, CREATE never fails with the code of a sender of a wrong length. -/
theorem createAddressExport_code_ne_of_size_eq {sender nonce : ByteArray} {code : UInt32}
    {message : String} (h : sender.size = 20)
    (he : createAddressExport sender nonce = .error (code, message)) :
    code ≠ ArgumentError.senderLength.code := by
  rw [createAddressExport_eq_of_size_eq h] at he
  cases hc : createAddress (readBytes sender 0 20 (by omega)) (bytesToNat nonce.toList) with
  | error r =>
    simp only [hc, Except.map, Except.mapError, Except.error.injEq, Prod.mk.injEq] at he
    rw [← he.1]
    exact (ArgumentError.code_ne_rlp _ r).symm
  | ok a => simp [hc, Except.map, Except.mapError] at he

/-- A sender of any length but 20 bytes gives the error of a sender, for CREATE2. -/
theorem create2AddressExport_eq_error_of_size_ne {sender salt initCode : ByteArray}
    (h : sender.size ≠ 20) :
    create2AddressExport sender salt initCode = .error ArgumentError.senderLength.toResult := by
  simp [create2AddressExport, readAddress, h, bind, Except.bind]

/-- A sender of 20 bytes and a salt of any length but 32 bytes give the error of a salt. -/
theorem create2AddressExport_eq_error_of_salt_size_ne {sender salt initCode : ByteArray}
    (hs : sender.size = 20) (h : salt.size ≠ 32) :
    create2AddressExport sender salt initCode = .error ArgumentError.saltLength.toResult := by
  simp [create2AddressExport, readAddress, readWord, hs, h, bind, Except.bind]

/-- A sender of 20 bytes and a salt of 32 bytes give the CREATE2 address of the three inputs. -/
theorem create2AddressExport_eq_of_size_eq {sender salt initCode : ByteArray}
    (hs : sender.size = 20) (h : salt.size = 32) :
    create2AddressExport sender salt initCode =
      .ok ⟨(create2Address (readBytes sender 0 20 (by omega)) (wordOf salt) initCode).toArray⟩ := by
  simp [create2AddressExport, readAddress, readWord, hs, h, bind, Except.bind, pure, Except.pure]

end EthLib.Execution.Evm.Exports
