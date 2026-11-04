module

public import EthLib.Base.Address
public import EthLib.Serialization.Rlp.Scalar

/-!
# `Serialization.Rlp.Codec`

Typed values as RLP items.

Source: Appendix B of the Yellow Paper, Shanghai version, in
[`Paper.tex` at `efc5f9a`](https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex).

A codec writes a value as an item, and reads an item back as a value.

- An integer is the scalar `BE(n)`, and its type bounds its value.
- A boolean is the scalar 0 or 1.
- A byte string of a fixed length must have exactly that length.
- A list holds the item of each element.
- A structure is a list of its fields, in order, with exactly one item per field.
- An optional value is the empty byte string for none, if no value has that item.
- So the recipient of a transaction is 20 bytes, or the empty byte string for a contract creation.

Decoding a value is strict: it accepts exactly the items that the codec writes.
-/

@[expose] public section

namespace EthLib.Serialization.Rlp

open EthLib.Base

/-- A type with an RLP form: each value is an item, and some items read back as values. -/
class Codec (α : Type) where
  /-- The item of a value. -/
  toItem : α → Item
  /-- The value of an item, or why the item holds no value of the type. -/
  ofItem : Item → Except RlpError α

namespace Codec

variable {α : Type} [Codec α]

/-- The RLP encoding of a value: the encoding of its item. -/
def encode (x : α) : Except RlpError ByteArray := Rlp.encode (toItem x)

/-- The value that `input` encodes.

It fails unless `input` is exactly the encoding of one item, and that item holds a value. -/
def decode (input : ByteArray) : Except RlpError α := do
  ofItem (← Rlp.decode input)

end Codec

/-- The bytes of a byte string, or an error for a list. -/
def Item.toBytes : Item → Except RlpError ByteArray
  | .bytes data => .ok data
  | .list _ => .error .listAsBytes

/-- The items of a list, or an error for a byte string. -/
def Item.toItems : Item → Except RlpError (List Item)
  | .bytes _ => .error .bytesAsList
  | .list items => .ok items

/-- The fields of a structure with `count` fields: a list of exactly `count` items. -/
def Item.fields (count : Nat) (item : Item) : Except RlpError (List Item) := do
  let items ← item.toItems
  if items.length = count then .ok items else .error (.wrongFieldCount count items.length)

/-- The value of field `index` of a structure, with the index in its error. -/
def Item.field {α : Type} [Codec α] (index : Nat) (item : Item) : Except RlpError α :=
  (Codec.ofItem item).mapError (.inField index)

/-- The scalar that an item holds, if it is below `2 ^ bits`. -/
def Item.toScalarBelow (bits : Nat) (item : Item) : Except RlpError Nat := do
  let n ← item.toScalar
  if n < 2 ^ bits then .ok n else .error (.scalarTooLarge n bits)

/-- An unbounded integer is a scalar. -/
instance : Codec Nat where
  toItem := Item.scalar
  ofItem := Item.toScalar

/-- A word is a scalar below 2^256, so it has at most 32 bytes. -/
instance : Codec U256 where
  toItem w := .scalar w.toNat
  ofItem item := do return BitVec.ofNat 256 (← item.toScalarBelow 256)

/-- A 64-bit integer is a scalar below 2^64, so it has at most 8 bytes. -/
instance : Codec UInt64 where
  toItem x := .scalar x.toNat
  ofItem item := do return UInt64.ofNat (← item.toScalarBelow 64)

/-- A byte is a scalar below 2^8, so it has at most 1 byte. -/
instance : Codec UInt8 where
  toItem x := .scalar x.toNat
  ofItem item := do return UInt8.ofNat (← item.toScalarBelow 8)

/-- A boolean is the scalar 1 for true and 0 for false, so false is the empty byte string. -/
instance : Codec Bool where
  toItem b := .scalar b.toNat
  ofItem item := do return (← item.toScalarBelow 1) == 1

/-- A byte string of any length is itself. -/
instance : Codec ByteArray where
  toItem := .bytes
  ofItem := Item.toBytes

/-- A byte string of `n` bytes, such as an address or a 32-byte hash.

Any other length is an error. -/
instance {n : Nat} : Codec (Vector UInt8 n) where
  toItem v := .bytes ⟨v.toArray⟩
  ofItem item := do
    let data ← item.toBytes
    if h : data.size = n then .ok ⟨data.data, h⟩ else .error (.wrongLength n data.size)

/-- A list is the list of the items of its elements. -/
instance {α : Type} [Codec α] : Codec (List α) where
  toItem xs := .list (xs.map Codec.toItem)
  ofItem item := do (← item.toItems).mapM Codec.ofItem

/-- A type none of whose values has the empty byte string as its item.

Only such a type can use the empty byte string for a missing value. -/
class NeverEmpty (α : Type) [Codec α] : Prop where
  /-- No value is written as the empty byte string. -/
  toItem_ne_empty (x : α) : Codec.toItem x ≠ .bytes .empty

/-- A byte string of a fixed nonzero length is never empty. -/
instance {n : Nat} [NeZero n] : NeverEmpty (Vector UInt8 n) where
  toItem_ne_empty v h := by
    have hSize := congrArg ByteArray.size (Item.bytes.inj h)
    simp [ByteArray.size] at hSize
    exact NeZero.ne n hSize

/-- An optional value: the empty byte string for none, and the item of the value otherwise.

The type must never write a value as the empty byte string, so the two cases do not overlap.

The recipient of a transaction is an example: none is a contract creation.

The Yellow Paper writes the recipient as a member of `B_20`, or of `B_0` for a creation. -/
instance {α : Type} [Codec α] [NeverEmpty α] : Codec (Option α) where
  toItem
    | none => .bytes .empty
    | some x => Codec.toItem x
  ofItem item := if item = .bytes .empty then .ok none else some <$> Codec.ofItem item

end EthLib.Serialization.Rlp
