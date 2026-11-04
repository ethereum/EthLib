module

public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.Blocks.Withdrawal

/-!
# `Blocks.Block`

A block: its header, its transactions, its ommer headers and, from Shapella, its withdrawals.

The RLP form of a block is the list of these parts, each part a list.

The type of a transaction is a parameter, so a block can hold any transaction form.

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

/-- A block at fork `fork`, with transactions of type `Tx`. -/
structure Block (fork : Fork) (Tx : Type) : Type where
  /-- The header. -/
  header : Header fork
  /-- The transactions, in the order that they run. -/
  transactions : List Tx
  /-- The headers of the ommers, which EIP-3675 fixes to the empty list from Paris. -/
  ommers : List (Header fork)
  /-- The withdrawals, from Shapella. -/
  withdrawals : Since .shapella fork (List Withdrawal)

namespace Block

variable {fork : Fork} {Tx : Type} [Codec Tx]

/-- The item of a block: `[header, transactions, ommers]`, then the withdrawals from Shapella. -/
def toItem (b : Block fork Tx) : Item :=
  .list ([Codec.toItem b.header, Codec.toItem b.transactions, Codec.toItem b.ommers]
    ++ Item.ofSince b.withdrawals)

/-- The block that an item holds: a list of its parts, in order. -/
def ofItem (item : Item) : Except RlpError (Block fork Tx) := do
  let n := 3 + Item.sinceCount .shapella fork
  let items ← item.fields n
  let (header, items) ← Item.readField (α := Header fork) n items
  let (transactions, items) ← Item.readField (α := List Tx) n items
  let (ommers, items) ← Item.readField (α := List (Header fork)) n items
  let (withdrawals, _) ← Item.readSince (f := .shapella) (α := List Withdrawal) n items
  return ⟨header, transactions, ommers, withdrawals⟩

end Block

instance {fork : Fork} {Tx : Type} [Codec Tx] : Codec (Block fork Tx) :=
  ⟨Block.toItem, Block.ofItem⟩

end EthLib.Execution.Blocks
