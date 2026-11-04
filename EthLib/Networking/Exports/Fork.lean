module

public import EthLib.Base.Fork

/-!
# `Exports.Fork`

The fork that a C caller names, for the networking exports.

A caller names a fork as the timeline does, such as `bellatrix` or `fusaka`.
-/

public section

namespace EthLib.Networking.Exports

/-- The fork with a name, such as `bellatrix`, as the constructor of the timeline writes it. -/
def forkAt (name : ByteArray) : IO Base.Fork := do
  let some name := String.fromUTF8? name | throw (IO.userError "fork name is not UTF-8")
  -- The timeline has fewer than 64 forks, and each index reads back as its fork.
  let forks := (List.range 64).map Base.Fork.ofNat
  match forks.find? (fun fork => ((reprStr fork).splitOn ".").getLast? == some name) with
  | some fork => pure fork
  | none => throw (IO.userError s!"no fork named {name}")

end EthLib.Networking.Exports
