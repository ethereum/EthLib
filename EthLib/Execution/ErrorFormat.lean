module

public import EthLib.Base.Hex

/-!
# `Execution.ErrorFormat`

The form of an execution error in its message: a constructor, named in full, and its arguments.

Each value an error carries has its name, so a reader can tell the numbers apart.

A hash, an address or a byte string shows in hex, as `0x` and two digits per byte.
-/

@[expose] public section

namespace EthLib.Execution

open EthLib.Base

/-- How a value that an error carries shows in its message. -/
class ErrorArg (α : Type) where
  /-- The value, in a form that reads in a message. -/
  format : α → Std.Format

/-- A value shows as Lean prints it, unless its type has a form of its own. -/
instance (priority := low) instErrorArgOfRepr {α : Type} [Repr α] : ErrorArg α :=
  ⟨fun a => repr a⟩

/-- A fixed run of bytes, such as a hash or an address, shows in hex. -/
instance instErrorArgVector {n : Nat} : ErrorArg (Vector UInt8 n) :=
  ⟨fun bytes => hexString bytes.toList⟩

/-- A byte string shows in hex. -/
instance instErrorArgByteArray : ErrorArg ByteArray :=
  ⟨fun bytes => hexString bytes.toList⟩

/-- An optional value shows as `none`, or as `some` before the value. -/
instance instErrorArgOption {α : Type} [ErrorArg α] : ErrorArg (Option α) :=
  ⟨fun | none => "none" | some a => "some " ++ ErrorArg.format a⟩

/-- A named argument, `(name := value)`, as Lean writes one. -/
def namedArg {α : Type} [ErrorArg α] (name : String) (value : α) : Std.Format :=
  .text ("(" ++ name ++ " := ") ++ ErrorArg.format value ++ .text ")"

/-- A constructor, named in full, applied to its arguments, in Lean syntax. -/
def constructorFormat (name : String) (args : List Std.Format) (prec : Nat) : Std.Format :=
  let applied : Std.Format := .group (.nest 2 (args.foldl (fun f a => f ++ .line ++ a) name))
  -- An argument position puts the application in parentheses, as `Repr.addAppParen` does.
  if prec ≥ max_prec then .group (.nest 1 (.text "(" ++ applied ++ .text ")")) else applied

end EthLib.Execution
