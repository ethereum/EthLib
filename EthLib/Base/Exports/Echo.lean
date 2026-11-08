module

public import EthLib.Base.Exports.Proofs.PyValue

/-!
# `EthLib.Base.Exports.Echo`

An export that sends a Python value back to Python, to test the converter of the C layer.

A tuple of the text `failure`, a code and a message comes back as an error of the method.
-/

public section

namespace EthLib.Exports

mutual

/-- The value with each tuple of the text `failure`, a code and a message replaced by a failure.

A tuple whose code does not fit in 32 bits stays a tuple.

The converter tests use it to send a failure from Python, at any depth. -/
def PyValue.withFailures : PyValue → PyValue
  | .list items => .list (withFailuresArray items)
  | .tuple items => tupleWithFailures items
  | .dict entries => .dict (withFailuresEntries entries)
  | v => v
termination_by structural v => v

/-- A tuple of the text `failure`, a code and a message as a failure, or each item with failures.

A tuple whose code does not fit in 32 bits stays a tuple. -/
def PyValue.tupleWithFailures : Array PyValue → PyValue
  | ⟨items⟩ => match items with
    | [.str "failure", .int code, .str message] =>
      if code < UInt32.size then .failure (code.toUInt32, message)
      else .tuple #[.str "failure", .int code, .str message]
    | _ => .tuple (withFailuresList items #[])

/-- The items of a sequence, each with its failures. -/
def PyValue.withFailuresArray : Array PyValue → Array PyValue
  | ⟨items⟩ => withFailuresList items #[]

/-- The items of a list, each with its failures, pushed after the items already done.

The recursive call is the last step, so a long sequence needs no deep stack. -/
def PyValue.withFailuresList : List PyValue → Array PyValue → Array PyValue
  | [], done => done
  | v :: vs, done => withFailuresList vs (done.push (withFailures v))

/-- The entries of a `dict`, each value with its failures. -/
def PyValue.withFailuresEntries : Array (String × PyValue) → Array (String × PyValue)
  | ⟨entries⟩ => withFailuresPairs entries #[]

/-- The entries of a list, each value with its failures, pushed after the entries already done.

The recursive call is the last step, so a long `dict` needs no deep stack. -/
def PyValue.withFailuresPairs : List (String × PyValue) → Array (String × PyValue) →
    Array (String × PyValue)
  | [], done => done
  | (key, v) :: rest, done => withFailuresPairs rest (done.push (key, withFailures v))

end

/-- The value that Python passes, back to Python, with each failure tuple read as a failure.

It tests the converter of the C layer in both directions. -/
@[export eth_pyvalue_echo]
def pyValueEcho (args : PyValue) : Result PyValue :=
  pyExport (α := PyValue) (fun v => .ok v.withFailures) args

end EthLib.Exports
