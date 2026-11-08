module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Base.Address
public import EthLib.Serialization.Rlp

/-!
# `Exports.Rlp`

C-ABI exports for RLP, callable from the Python C extension.

An item crosses the boundary as itself: a byte string, or a list of items.

The typed decoder takes the type as a short name, and returns the value as a typed Python value.

A rejected input comes back as the code of its error and a message that names the fault.

An unknown type name has code 0, which no error of RLP has.
-/

public section

namespace EthLib.Serialization.Rlp.Exports

open EthLib.Exports (Result PyValue ToPy toPy pyExport)

open EthLib.Base

/-- Run a fallible decoding or encoding, with the code of its error and a message. -/
def runRlp {α : Type} (what : String) (act : Except RlpError α) : Result α :=
  act.mapError fun e => (e.code, s!"{what}: {reprStr e}")

/-- The RLP encoding of an item. -/
@[export eth_rlp_encode]
def encodeExport (item : Item) : Result ByteArray :=
  runRlp "item has no encoding" (encode item)

/-- The item that the bytes encode, if they encode exactly one. -/
@[export eth_rlp_decode]
def decodeExport (data : ByteArray) : Result Item :=
  runRlp "input rejected" (decode data)

/-- Decode a value of one type, and return it as a Python value. -/
def decodeAs (α : Type) [Codec α] [ToPy α] (data : ByteArray) : Result PyValue := do
  let x : α ← runRlp "input rejected" (Codec.decode data)
  return toPy x

/-- The value of the named type that the bytes encode, as a Python value.

An unbounded integer goes through the scalar decoder itself.

A recipient is an address, or `None` for a contract creation. -/
def decodeAsOf (args : String × ByteArray) : Result PyValue := do
  let (kind, data) := args
  match kind with
  | "nat" => return toPy (← runRlp "input rejected" (decodeScalar data))
  | "u256" => decodeAs U256 data
  | "uint64" => decodeAs UInt64 data
  | "bool" => decodeAs Bool data
  | "address" => decodeAs Address data
  | "recipient" => decodeAs (Option Address) data
  | "list_nat" => decodeAs (List Nat) data
  | _ => throw (0, "unknown RLP type")

/-- The value of the named type that the bytes encode, as a Python value.

The arguments are the name of the type and the bytes.

The names are `nat`, `u256`, `uint64`, `bool`, `address`, `recipient` and `list_nat`.

A recipient is an address, or `None` for a contract creation. -/
@[export eth_rlp_decode_as]
def decodeAsExport (args : PyValue) : Result PyValue :=
  pyExport decodeAsOf args

end EthLib.Serialization.Rlp.Exports
