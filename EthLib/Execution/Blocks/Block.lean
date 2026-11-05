module

public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Blocks.Block`

A block: its header, its transactions, its ommer headers and, from Shapella, its withdrawals.

The RLP form of a block is the list of these parts, each part a list.

The type of a transaction is a parameter, so a block can hold any transaction form.

Each ommer is a header at the fork of its own number on the chain.

So the first blocks of a fork can hold ommers in the header form of the fork before it.

Sections 4.4 and 4.4.3 of the Yellow Paper, Shanghai version, define the block: [`Paper.tex`][yp].

[EIP-4895][eip-4895] appends the withdrawals at Shapella.

[EIP-3675][eip-3675] fixes the ommers to the empty list from Paris.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-3675]: https://eips.ethereum.org/EIPS/eip-3675#block-structure
[eip-4895]: https://eips.ethereum.org/EIPS/eip-4895#new-field-in-the-execution-payload-withdrawals
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

namespace Header

/-- The index of the number among the fields of a header, at every fork. -/
def NUMBER_FIELD : Nat := 8

/-- The number that the item of a header holds, read before the header is decoded at a fork.

The number is the ninth field at every fork, and every fork has at least 15 fields. -/
def numberOfItem (item : Item) : Except RlpError Nat := do
  let items ← item.toItems
  match items[NUMBER_FIELD]? with
  | some field => Item.field NUMBER_FIELD field
  | none => .error (.wrongFieldCount (fieldCount .frontier) items.length)

/-- The header that an item holds, with its fork: the fork of its own number on the chain.

The chain gives the fork of each block number. -/
def ofItemAtNumber (forkOf : Nat → Fork) (item : Item) :
    Except RlpError ((f : Fork) × Header f) := do
  let f := forkOf (← numberOfItem item)
  return ⟨f, ← Codec.ofItem item⟩

end Header

/-- A block at fork `fork`, with transactions of type `Tx`. -/
structure Block (fork : Fork) (Tx : Type) : Type where
  /-- The header. -/
  header : Header fork
  /-- The transactions, in the order that they run. -/
  transactions : List Tx
  /-- The headers of the ommers, each with the fork of its own number.

  EIP-3675 fixes the ommers to the empty list from Paris. -/
  ommers : List ((f : Fork) × Header f)
  /-- The withdrawals, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)

/-- The item of a list of ommers: the list of their headers, each in the form of its own fork. -/
def ommersItem (ommers : List ((f : Fork) × Header f)) : Item :=
  .list (ommers.map fun ommer => Codec.toItem ommer.2)

namespace Block

variable {fork : Fork} {Tx : Type} [Codec Tx]

/-- The item of a block: `[header, transactions, ommers]`, then the withdrawals from Shapella. -/
def toItem (b : Block fork Tx) : Item :=
  .list ([Codec.toItem b.header, Codec.toItem b.transactions, ommersItem b.ommers]
    ++ Item.ofSince b.withdrawals)

/-- The block that an item holds: a list of its parts, in order.

The chain gives the fork of each block number, and each ommer decodes at the fork of its number. -/
def ofItem (forkOf : Nat → Fork) (item : Item) : Except RlpError (Block fork Tx) := do
  let n := 3 + Item.sinceCount .shapella fork
  let items ← item.fields n
  let (header, items) ← Item.readField (α := Header fork) n items
  let (transactions, items) ← Item.readField (α := List Tx) n items
  let (ommerItems, items) ← Item.readField (α := List Item) n items
  let ommers ← (ommerItems.mapM (Header.ofItemAtNumber forkOf)).mapError (.inField 2)
  let (withdrawals, _) ← Item.readSince (f := .shapella) (α := List Withdrawal) n items
  return ⟨header, transactions, ommers, withdrawals⟩

/-- The RLP encoding of a block: the encoding of its item. -/
def encode (b : Block fork Tx) : Except RlpError ByteArray := Serialization.Rlp.encode b.toItem

/-- The block that `input` encodes, with each ommer at the fork of its number on the chain. -/
def decode (forkOf : Nat → Fork) (input : ByteArray) : Except RlpError (Block fork Tx) := do
  ofItem forkOf (← Serialization.Rlp.decode input)

end Block

end EthLib.Execution.Blocks
