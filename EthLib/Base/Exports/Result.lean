module

/-!
# The result of a C export

The result type that the C layer of the Python bindings reads.

Each error type that reaches Python gives its code and its message in one place.

One conversion then turns the result of an operation into the result of an export.
-/

public section

namespace EthLib.Exports

/-- The result of an export: the value, or the code and the message of an error.

`Except.error` is the first constructor, so the C layer reads it as tag 0.

The fields of the pair are boxed, because the pair type is polymorphic. -/
abbrev Result (α : Type) := Except (UInt32 × String) α

/-- An error type that an export reports to Python: the code and the message of each error.

The code comes from the error type, so it means the same thing in every export.

Code 0 is left for an argument that does not read.

Some cases of specification error types have code 0 too, when no code of theirs covers them. -/
class ExportError (ε : Type) where
  /-- The code of an error. -/
  code : ε → UInt32
  /-- The message of an error, before the context of the export. -/
  message : ε → String

/-- The result of an export, from the result of an operation.

An error keeps its code, and its message comes after the context of the export, a colon and a space.

Without a context, the message stands alone. -/
def toResult {ε α : Type} [ExportError ε] (context : Option String) (result : Except ε α) :
    Result α :=
  result.mapError fun e =>
    let message := ExportError.message e
    (ExportError.code e, match context with
      | some context => s!"{context}: {message}"
      | none => message)

/-- A Python argument that does not read, with the reason.

No error type of the specification describes it. -/
structure UnreadArgument where
  /-- Why the argument does not read. -/
  reason : String

/-- An argument that does not read has code 0, the code that is left for it. -/
instance : ExportError UnreadArgument where
  code _ := 0
  message e := e.reason

/-- The result of an export that refuses an argument: code 0, and the reason after the context. -/
def rejectArgument {α : Type} (context : Option String) (reason : String) : Result α :=
  toResult context (Except.error (UnreadArgument.mk reason) : Except UnreadArgument α)

end EthLib.Exports
