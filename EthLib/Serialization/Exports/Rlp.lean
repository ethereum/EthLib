module

public import EthLib.Base.Exports
public import EthLib.Base.Address
public import EthLib.Serialization.Rlp

/-!
# `Exports.Rlp`

C-ABI exports for RLP, callable from the Python C extension.

An item crosses the boundary as itself: a byte string, or a list of items.

A typed value crosses it as the item of the value, and its type as a short name.

A rejected input comes back as the code of its error and a message that names the fault.

An unknown type name has code 0, which no error of RLP has.
-/

public section

namespace EthLib.Serialization.Rlp.Exports

open EthLib.Exports (Result)

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

/-- Decode a value of one type, and return the item of the value. -/
def decodeAs (α : Type) [Codec α] (data : ByteArray) : Result Item := do
  let x : α ← runRlp "input rejected" (Codec.decode data)
  return Codec.toItem x

/-- The value of the named type that the bytes encode, given as the item of the value.

An unbounded integer goes through the scalar decoder itself. -/
@[export eth_rlp_decode_as]
def decodeAsExport (kind data : ByteArray) : Result Item := do
  match String.fromUTF8? kind with
  | some "nat" => return .scalar (← runRlp "input rejected" (decodeScalar data))
  | some "u256" => decodeAs U256 data
  | some "uint64" => decodeAs UInt64 data
  | some "bool" => decodeAs Bool data
  | some "address" => decodeAs Address data
  | some "recipient" => decodeAs (Option Address) data
  | some "list_nat" => decodeAs (List Nat) data
  | _ => throw (0, "unknown RLP type")

end EthLib.Serialization.Rlp.Exports
