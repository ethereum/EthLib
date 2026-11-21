module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Execution.Exports.Evm
import all EthLib.Base.Exports.Result

/-!
# Proofs: `Execution.Exports.Evm`

Each export that reads an address or a salt as bytes checks the length first.

An argument of the wrong length gives the error of that argument, and too many operands fail.

Arguments of the right lengths or counts give the result that the operation computes from them.

The codes of these errors never meet the codes of an RLP error, so one Python class carries both.

-/

@[expose] public section

namespace EthLib.Execution.Evm.Exports

open EthLib.Base (U256 readBytes)
open EthLib.Serialization.Rlp (RlpError)

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem ArgumentError.code_injective (e₁ e₂ : ArgumentError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ArgumentError.code] at h; exact absurd h (by decide))

/-- An argument error never has the code of an RLP error. -/
theorem ArgumentError.code_ne_rlp (e : ArgumentError) (r : RlpError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [ArgumentError.code, RlpError.code] <;> decide

/-! ## Operands of an instruction -/

/-- More than three operands give an error with code 0, whatever the opcode. -/
theorem wordOpOf_eq_error_of_length {opcode : UInt8} {operands : List U256}
    (h : 3 < operands.length) :
    wordOpOf (opcode, operands) = .error (0, "an instruction takes at most 3 operands") := by
  simp [wordOpOf, h, bind, Except.bind, EthLib.Exports.rejectArgument, EthLib.Exports.toResult,
    Except.mapError]
  exact ⟨rfl, rfl⟩

/-- At most three operands give the word that the instruction pushes, with 0 for a missing one. -/
theorem wordOpOf_eq_of_length_le {opcode : UInt8} {operands : List U256}
    (h : operands.length ≤ 3) :
    wordOpOf (opcode, operands) =
      match (Op.decode opcode).bind fun op =>
          wordOp op (operands.getD 0 0) (operands.getD 1 0) (operands.getD 2 0) with
      | some w => .ok w
      | none => .error (0, s!"opcode {opcode} does not push a word of its operands alone") := by
  simp only [wordOpOf, show ¬operands.length > 3 by omega, ite_false]
  rfl

/-! ## Ranges of a memory access -/

/-- The price of growing a memory for some ranges, and the bytes it grows by, come from one step. -/
theorem extendMemoryOf_eq {size : Nat} {ranges : List (U256 × U256)} :
    extendMemoryOf (size, ranges) =
      .ok ((extendMemory size ranges).cost, (extendMemory size ranges).expandBy) := rfl

/-! ## Created addresses -/

/-- A sender of any length but 20 bytes gives the error of a sender. -/
private theorem readAddress_of_size_ne {sender : ByteArray} (h : sender.size ≠ 20) :
    readAddress sender = .error (ArgumentError.senderLength sender.size).toResult := by
  rw [readAddress, Base.exactBytes_of_size_ne _ h]
  rfl

/-- A sender of 20 bytes gives the address of those bytes. -/
private theorem readAddress_of_size_eq {sender : ByteArray} (h : sender.size = 20) :
    readAddress sender = .ok (readBytes sender 0 20 (by omega)) := by
  -- Reading the buffer in place gives back the vector of its bytes.
  rw [readAddress, Base.exactBytes_of_size_eq _ h]
  exact congrArg Except.ok (Base.readBytes_packBytes (⟨sender.data, h⟩ : Base.Address) _).symm

/-- A sender of any length but 20 bytes gives the error of a sender, for CREATE. -/
theorem createAddressOf_eq_error_of_size_ne {sender : ByteArray} {nonce : Nat}
    (h : sender.size ≠ 20) :
    createAddressOf (sender, nonce) = .error (ArgumentError.senderLength sender.size).toResult := by
  simp [createAddressOf, readAddress_of_size_ne h, bind, Except.bind]

/-- A sender of 20 bytes gives the CREATE address of that sender, or the error of its preimage. -/
theorem createAddressOf_eq_of_size_eq {sender : ByteArray} {nonce : Nat} (h : sender.size = 20) :
    createAddressOf (sender, nonce) =
      ((createAddress (readBytes sender 0 20 (by omega)) nonce).map
        (fun a => ⟨a.toArray⟩)).mapError
        fun e => (e.code, s!"create preimage rejected: {reprStr e}") := by
  simp [createAddressOf, readAddress_of_size_eq h, bind, Except.bind, EthLib.Exports.toResult]
  -- The conversion writes the code and the message of the error as the statement does.
  rfl

/-- With a sender of 20 bytes, CREATE never fails with the code of a sender of a wrong length. -/
theorem createAddressOf_code_ne_of_size_eq {sender : ByteArray} {nonce : Nat} {code : UInt32}
    {message : String} (h : sender.size = 20)
    (he : createAddressOf (sender, nonce) = .error (code, message)) :
    code ≠ (ArgumentError.senderLength sender.size).code := by
  rw [createAddressOf_eq_of_size_eq h] at he
  cases hc : createAddress (readBytes sender 0 20 (by omega)) nonce with
  | error r =>
    simp only [hc, Except.map, Except.mapError, Except.error.injEq, Prod.mk.injEq] at he
    rw [← he.1]
    exact (ArgumentError.code_ne_rlp _ r).symm
  | ok a => simp [hc, Except.map, Except.mapError] at he

/-- A sender of any length but 20 bytes gives the error of a sender, for CREATE2. -/
theorem create2AddressExport_eq_error_of_size_ne {sender salt initCode : ByteArray}
    (h : sender.size ≠ 20) :
    create2AddressExport sender salt initCode =
      .error (ArgumentError.senderLength sender.size).toResult := by
  simp [create2AddressExport, readAddress_of_size_ne h, bind, Except.bind]

/-- A sender of 20 bytes and a salt of any length but 32 bytes give the error of a salt. -/
theorem create2AddressExport_eq_error_of_salt_size_ne {sender salt initCode : ByteArray}
    (hs : sender.size = 20) (h : salt.size ≠ 32) :
    create2AddressExport sender salt initCode =
      .error (ArgumentError.saltLength salt.size).toResult := by
  simp [create2AddressExport, readAddress_of_size_eq hs, readWord, h, bind, Except.bind,
    EthLib.Exports.toResult, Except.mapError]
  rfl

/-- A sender of 20 bytes and a salt of 32 bytes give the CREATE2 address of the three inputs. -/
theorem create2AddressExport_eq_of_size_eq {sender salt initCode : ByteArray}
    (hs : sender.size = 20) (h : salt.size = 32) :
    create2AddressExport sender salt initCode =
      .ok ⟨(create2Address (readBytes sender 0 20 (by omega)) (wordOf salt) initCode).toArray⟩ := by
  simp [create2AddressExport, readAddress_of_size_eq hs, readWord, h, bind, Except.bind, pure,
    Except.pure]

end EthLib.Execution.Evm.Exports
