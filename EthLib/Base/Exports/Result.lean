module

/-!
# The result of a C export

The result type that the C layer of the Python bindings reads.
-/

public section

namespace EthLib.Exports

/-- The result of an export: the value, or the code and the message of an error.

`Except.error` is the first constructor, so the C layer reads it as tag 0.

The fields of the pair are boxed, because the pair type is polymorphic. -/
abbrev Result (α : Type) := Except (UInt32 × String) α

end EthLib.Exports
