module

public import EthLib.Base.Exports.Proofs.PyValue

/-!
# `EthLib.Base.Exports.Echo`

An export that sends a Python value back to Python, to test the converter of the C layer.

A tuple of the text `failure`, a code and a message comes back as an error of the method.
-/

public section

namespace EthLib.Exports

/-- The value with each tuple of the text `failure`, a code and a message replaced by a failure.

A tuple whose code does not fit in 32 bits stays a tuple.

The converter tests use it to send a failure from Python, at any depth. -/
partial def PyValue.withFailures : PyValue → PyValue
  | .tuple #[.str "failure", .int code, .str message] =>
    if code < UInt32.size then .failure (code.toUInt32, message)
    else .tuple #[.str "failure", .int code, .str message]
  | .list items => .list (items.map withFailures)
  | .tuple items => .tuple (items.map withFailures)
  | .dict entries => .dict (entries.map fun (key, value) => (key, withFailures value))
  | v => v

/-- The value that Python passes, back to Python, with each failure tuple read as a failure.

It tests the converter of the C layer in both directions. -/
@[export eth_pyvalue_echo]
def pyValueEcho (args : PyValue) : Result PyValue :=
  pyExport (α := PyValue) (fun v => .ok v.withFailures) args

end EthLib.Exports
