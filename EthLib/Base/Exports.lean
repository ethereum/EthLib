module

public import EthLib.Base.Exports.Result
public import EthLib.Base.Fork

/-!
# `EthLib.Base.Exports`

The result type of the fallible C exports, and the fork readers that several exports share.

The C layer of the bindings reads the result type, so its layout is part of the binary interface.
-/

public section

namespace EthLib.Exports

/-- The fork with a name given as UTF-8 bytes, written as its case is, such as `bellatrix`.

An unknown name has code 0, since no error type of the specification covers it. -/
def forkOfName (name : ByteArray) : Result Base.Fork := do
  -- Bytes that are not UTF-8 name no fork.
  let some name := String.fromUTF8? name | rejectArgument none "fork name is not UTF-8"
  -- The name must be the case of a fork, letter for letter.
  match Base.Fork.ofName? name with
  | some fork => pure fork
  | none => rejectArgument none s!"no fork named {name}"

/-- The fork with a name given as UTF-8 bytes, if it comes no later than `last`.

`last` is the last fork whose rules the export holds.

EthLib does not hold every rule of Glamsterdam and Hegotá yet.

Without this bound, a later fork would silently get the rules of the fork before it. -/
def forkUpTo (last : Base.Fork) (name : ByteArray) : Result Base.Fork := do
  let fork ← forkOfName name
  -- A later fork fails with code 0, and a message that it is not yet specified.
  if fork ≤ last then pure fork
  else rejectArgument none s!"fork {fork.name} not yet specified"

end EthLib.Exports
