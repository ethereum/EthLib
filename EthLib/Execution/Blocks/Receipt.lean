module

public import EthLib.Base.Bytes
public import EthLib.Base.Fork
public import EthLib.Execution.Blocks.Log
public import EthLib.Execution.Transactions.Envelope

/-!
# `Blocks.Receipt`

The receipt of a transaction, at each fork.

A receipt records the outcome of a transaction, the gas used so far, and the logs.

Its RLP form is the list `[outcome, cumulative_gas_used, bloom, logs]`.

Before Byzantium, the outcome is the state root after the transaction.

From Byzantium, [EIP-658][eip-658] makes it a status: 1 for success, 0 for failure.

From Berlin, [EIP-2718][eip-2718] puts the type of a typed transaction before its receipt.

The receipt of a legacy transaction stays the RLP form, whose first byte is at least `0xc0`.

Section 4.4.1 of the Yellow Paper, Shanghai version, defines the receipt: [`Paper.tex`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-658]: https://eips.ethereum.org/EIPS/eip-658#specification
[eip-2718]: https://eips.ethereum.org/EIPS/eip-2718#receipts
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Transactions

/-- The outcome of a transaction at fork `fork`: a state root before Byzantium, a status from it.

Each case holds a proof of its range of forks, so a receipt has the outcome of its fork. -/
inductive Outcome : Fork → Type where
  /-- The state root after the transaction, before Byzantium. -/
  | postState {fork : Fork} (before : fork < .byzantium) (root : Hash32) : Outcome fork
  /-- Whether the transaction succeeded, from Byzantium. -/
  | status {fork : Fork} (since : Fork.byzantium ≤ fork) (succeeded : Bool) : Outcome fork

namespace Outcome

variable {fork : Fork}

/-- The item of an outcome: the 32 bytes of a state root, or the scalar 1 or 0 of a status. -/
def toItem : Outcome fork → Item
  | .postState _ root => Codec.toItem root
  | .status _ succeeded => Codec.toItem succeeded

/-- The outcome that an item holds at `fork`: a status from Byzantium, a state root before. -/
def ofItem (item : Item) : Except RlpError (Outcome fork) :=
  if h : Fork.byzantium ≤ fork then .status h <$> Codec.ofItem item
  else .postState (Nat.lt_of_not_le h) <$> Codec.ofItem item

end Outcome

instance {fork : Fork} : Codec (Outcome fork) := ⟨Outcome.toItem, Outcome.ofItem⟩

/-- The receipt of a transaction at fork `fork`. -/
structure Receipt (fork : Fork) : Type where
  /-- The outcome of the transaction. -/
  outcome : Outcome fork
  /-- The gas that the block used up to and with the transaction. -/
  cumulativeGasUsed : Nat
  /-- The Bloom filter of the logs. -/
  bloom : Bytes256
  /-- The logs that the transaction wrote. -/
  logs : List Log

/-- A receipt is the list of its four fields, in order. -/
instance {fork : Fork} : Codec (Receipt fork) where
  toItem r := .list [Codec.toItem r.outcome, Codec.toItem r.cumulativeGasUsed,
    Codec.toItem r.bloom, Codec.toItem r.logs]
  ofItem item := do
    match ← item.fields 4 with
    | [outcome, cumulativeGasUsed, bloom, logs] =>
      return {
        outcome := ← Item.field 0 outcome
        cumulativeGasUsed := ← Item.field 1 cumulativeGasUsed
        bloom := ← Item.field 2 bloom
        logs := ← Item.field 3 logs }
    | items => .error (.wrongFieldCount 4 items.length)

/-- Why some bytes hold no receipt. -/
inductive ReceiptError where
  /-- The input is empty. -/
  | emptyReceipt
  /-- The first byte names a type of transaction that the fork does not have. -/
  | unsupportedType (type : UInt8)
  /-- The RLP form holds no receipt. -/
  | decoding (error : RlpError)
  deriving DecidableEq, Repr

/-- The bytes of the receipt of a transaction of type `type`, where type 0 is a legacy transaction.

The receipt of a legacy transaction is its RLP form.

The receipt of a typed transaction is the type, then the RLP form.

It fails only when an RLP payload has `2^64` bytes or more. -/
def encodeReceipt {fork : Fork} (type : UInt8) (r : Receipt fork) : Except RlpError ByteArray :=
  if type = 0 then Codec.encode r else typedBytes type <$> Codec.encode r

/-- The type of the transaction and the receipt that `bytes` hold at `fork`.

A first byte of at least `0xc0` starts the receipt of a legacy transaction, of type 0.

Any other first byte is the type of a transaction, which the fork must have. -/
def decodeReceipt (fork : Fork) (bytes : ByteArray) :
    Except ReceiptError (UInt8 × Receipt fork) :=
  if h : 0 < bytes.size then
    let first := bytes[0]
    if 0xc0 ≤ first then
      ((0, ·) <$> Codec.decode bytes).mapError .decoding
    else
      match typeFork first with
      | some since =>
        if since ≤ fork then
          ((first, ·) <$> Codec.decode (bytes.extract 1 bytes.size)).mapError .decoding
        else .error (.unsupportedType first)
      | none => .error (.unsupportedType first)
  else .error .emptyReceipt

end EthLib.Execution.Blocks
