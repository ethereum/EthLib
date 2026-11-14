module

public import EthLib.Base.BigEndian

/-!
# Readers of byte fields

A reader consumes a prefix of a byte list and returns the bytes after it.

Each wire format supplies its own error type, and the error it reports for a truncated field.
-/

@[expose] public section

namespace EthLib.Base.ByteReader

/-- A reader of a byte list, failing with an error of the given type. -/
abbrev Reader (ε α : Type) := StateT (List UInt8) (Except ε) α

/-- Read exactly `n` bytes, without padding a truncated field. -/
def bytes {ε : Type} (truncated : ε) (n : Nat) : Reader ε (List UInt8) := fun input =>
  let field := input.take n
  if field.length = n then .ok (field, input.drop n) else .error truncated

/-- Read a big-endian integer of the given byte width. -/
def uint {ε : Type} (truncated : ε) (n : Nat) : Reader ε Nat := do
  return bytesToNat (← bytes truncated n)

/-- Reject a field that does not meet its format constraint, without consuming input. -/
def require {ε : Type} (condition : Prop) [Decidable condition] (error : ε) : Reader ε Unit :=
  fun input => if condition then .ok ((), input) else .error error

end EthLib.Base.ByteReader
