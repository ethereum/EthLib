module

public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Blocks.Block`

A block: its header, its transactions, its ommer headers and, from Shapella, its withdrawals.

Sections 4.4 and 4.4.3 of the [Yellow Paper][yp], Shanghai version, define it.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A block at fork `fork`, with transactions of type `Tx`.

The type of a transaction is a parameter, so a block can hold any transaction form. -/
structure Block (fork : Fork) (Tx : Type) : Type where
  /-- The header. -/
  header : Header fork
  /-- The transactions, in the order that they run. -/
  transactions : List Tx
  /-- The headers of the ommers, each with the fork of its own number on the chain.

  So the first blocks of a fork can hold ommers in the header form of the fork before it.

  [EIP-3675][eip-3675] fixes the ommers to the empty list from Paris.

  [eip-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#block-structure
  -/
  ommers : List ((f : Fork) × Header f)
  /-- The withdrawals, which [EIP-4895][eip-4895] appends at Shapella.

  [eip-4895]: https://eips.ethereum.org/EIPS/eip-4895#new-field-in-the-execution-payload-withdrawals
  -/
  withdrawals : Since .shapella fork (List Withdrawal)

/-- The item of a list of ommers: the list of their headers, each in the form of its own fork. -/
def ommersItem (ommers : List ((f : Fork) × Header f)) : Item :=
  -- `L_H*(B_U)`: each ommer header as `L_H` of its own fork.
  .list (ommers.map fun ommer => Codec.toItem ommer.2)

namespace Block

variable {fork : Fork} {Tx : Type} [Codec Tx]

/-- The item of a block: `[header, transactions, ommers]`, then the withdrawals from Shapella. -/
def toItem (b : Block fork Tx) : Item :=
  -- Yellow Paper §4.4.3: `L_B(B) = (L_H(B_H), ~L_T*(B_T), L_H*(B_U), L_W*(B_W))`.
  --
  -- `L_W*(B_W)` comes only from Shapella, by EIP-4895.
  --
  -- The encoding of the type of the transactions gives `~L_T`: the RLP list, or the typed bytes.
  .list ([Codec.toItem b.header, Codec.toItem b.transactions, ommersItem b.ommers]
    ++ Item.ofSince b.withdrawals)

/-- The block that an item holds: a list of its parts, in order.

The chain gives the fork of each block number, and each ommer decodes at the fork of its number. -/
def ofItem (forkOf : Nat → Fork) (item : Item) : Except RlpError (Block fork Tx) := do
  -- The parts of `L_B`, in order: three, and a fourth from Shapella.
  let n := 3 + Item.sinceCount .shapella fork
  let items ← item.fields n
  let (header, items) ← Item.readField (α := Header fork) n items
  let (transactions, items) ← Item.readField (α := List Tx) n items
  -- The ommers stay items until each one's number gives its fork.
  let (ommerItems, items) ← Item.readField (α := List Item) n items
  -- An ommer that fails reports the field of the ommers, at index 2.
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
