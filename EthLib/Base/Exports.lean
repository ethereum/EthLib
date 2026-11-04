module

/-!
# `EthLib.Base.Exports`

The result type that every fallible C export returns.

The C layer of the bindings reads this type, so its layout is part of the binary interface.
-/

public section

namespace EthLib.Exports

/-- The result of an export: the value, or the code and the message of an error.

`Except.error` is the first constructor, so the C layer reads it as tag 0.

The fields of the pair are boxed, because the pair type is polymorphic. -/
abbrev Result (α : Type) := Except (UInt32 × String) α

end EthLib.Exports
