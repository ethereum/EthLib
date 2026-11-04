module

public import EthLib.Base.Fork

/-!
# `EthLib.Base.Exports`

The result type that every fallible C export returns.

The C layer of the bindings reads this type, so its layout is part of the binary interface.

A caller names a fork as its case is written, such as `bellatrix`.

An unknown name has code 0, since no error type of the specification covers it.
-/

public section

namespace EthLib.Exports

/-- The result of an export: the value, or the code and the message of an error.

`Except.error` is the first constructor, so the C layer reads it as tag 0.

The fields of the pair are boxed, because the pair type is polymorphic. -/
abbrev Result (α : Type) := Except (UInt32 × String) α

/-- The fork with a name given as UTF-8 bytes. -/
def forkOfName (name : ByteArray) : Result Base.Fork := do
  let some name := String.fromUTF8? name | throw (0, "fork name is not UTF-8")
  match Base.Fork.ofName? name with
  | some fork => pure fork
  | none => throw (0, s!"no fork named {name}")

end EthLib.Exports
