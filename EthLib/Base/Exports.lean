module

public import EthLib.Base.Fork

/-!
# `EthLib.Base.Exports`

The result type that every fallible C export returns.

The C layer of the bindings reads this type, so its layout is part of the binary interface.

A caller names a fork as its case is written, such as `bellatrix`.

An unknown name has code 0, since no error type of the specification covers it.

EthLib does not hold every rule of Glamsterdam and Hegotá yet.

So each export names the last fork whose rules it holds, and rejects any later fork.

The rejection also has code 0, and its message says that the fork is not yet specified.

Without it, a later fork would silently get the rules of the fork before it.
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

/-- The fork with a name given as UTF-8 bytes, if it comes no later than `last`.

`last` is the last fork whose rules the export holds. -/
def forkUpTo (last : Base.Fork) (name : ByteArray) : Result Base.Fork := do
  let fork ← forkOfName name
  if fork ≤ last then pure fork
  else throw (0, s!"fork {fork.name} not yet specified")

end EthLib.Exports
