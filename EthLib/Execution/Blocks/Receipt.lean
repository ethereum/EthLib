module

public import EthLib.Base.Bytes
public import EthLib.Base.Fork
public import EthLib.Execution.Blocks.Bloom
public import EthLib.Execution.Evm.Log
public import EthLib.Execution.Transactions.Envelope

/-!
# `Blocks.Receipt`

The receipt of a transaction, at each fork.

A receipt records the outcome of a transaction, the gas used so far, and the logs.

Its RLP form is `L_R(R) = (R_z, R_u, R_b, R_l)`.

Those are the outcome, the gas used so far, the Bloom filter of the logs and the logs.

Before Byzantium, the outcome is the state root after the transaction.

From Byzantium, [EIP-658][eip-658] makes it a status: 1 for success, 0 for failure.

From Berlin, [EIP-2718][eip-2718] puts the type of a typed transaction before its receipt.

The receipt of a legacy transaction stays the RLP form, whose first byte is at least `0xc0`.

The receipts of a block count the gas cumulatively, so each holds the gas of the block so far.

From Glamsterdam, that gas is the gas that the senders pay, after the refunds and the floor.

The block counts its own gas apart, before the refunds.

[EIP-7778][eip-7778] and [EIP-8037][eip-8037] make this change.

Section 4.4.1 of the Yellow Paper, Shanghai version, defines the receipt: [`Paper.tex`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-658]: https://eips.ethereum.org/EIPS/eip-658#specification
[eip-2718]: https://eips.ethereum.org/EIPS/eip-2718#receipts
[eip-7778]: https://eips.ethereum.org/EIPS/eip-7778#specification
[eip-8037]: https://eips.ethereum.org/EIPS/eip-8037#receipt-semantics
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
  -- Before Byzantium, the first item of `L_R` is the intermediate state root, 32 bytes.
  | .postState _ root => Codec.toItem root
  -- From Byzantium, EIP-658 makes it the status, the scalar 1 or 0.
  | .status _ succeeded => Codec.toItem succeeded

/-- The outcome that an item holds at `fork`: a status from Byzantium, a state root before. -/
def ofItem (item : Item) : Except RlpError (Outcome fork) :=
  -- EIP-658: the status from Byzantium, the state root before.
  if h : Fork.byzantium ≤ fork then .status h <$> Codec.ofItem item
  else .postState (Nat.lt_of_not_le h) <$> Codec.ofItem item

end Outcome

instance {fork : Fork} : Codec (Outcome fork) := ⟨Outcome.toItem, Outcome.ofItem⟩

/-- The receipt of a transaction at fork `fork`. -/
structure Receipt (fork : Fork) : Type where
  /-- The outcome of the transaction. -/
  outcome : Outcome fork
  /-- The gas that the block used up to and with the transaction.

  From Glamsterdam, it is the gas that the senders paid up to and with the transaction. -/
  cumulativeGasUsed : Nat
  /-- The Bloom filter of the logs. -/
  bloom : Bytes256
  /-- The logs that the transaction wrote. -/
  logs : List Log

/-- A receipt is the list of its four fields, in order. -/
instance {fork : Fork} : Codec (Receipt fork) where
  -- Yellow Paper §4.4.1: `L_R(R) = (R_z, R_u, R_b, R_l)`.
  toItem r := .list [Codec.toItem r.outcome, Codec.toItem r.cumulativeGasUsed,
    Codec.toItem r.bloom, Codec.toItem r.logs]
  ofItem item := do
    -- A list of exactly four items, read in the order of `L_R`.
    match ← item.fields 4 with
    | [outcome, cumulativeGasUsed, bloom, logs] =>
      return {
        outcome := ← Item.field 0 outcome
        cumulativeGasUsed := ← Item.field 1 cumulativeGasUsed
        bloom := ← Item.field 2 bloom
        logs := ← Item.field 3 logs }
    | items => .error (.wrongFieldCount 4 items.length)

/-! ## Making the receipts of a block -/

/-- The outcome of a transaction at `fork`: the status, or the state root before Byzantium.

The state root after the transaction is computed only before Byzantium. -/
def Outcome.make (fork : Fork) (succeeded : Bool) (postStateRoot : Unit → Hash32) :
    Outcome fork :=
  -- EIP-658: from Byzantium, the status replaces the intermediate state root.
  --
  -- The root is computed only in the other branch, where it is needed.
  if h : Fork.byzantium ≤ fork then .status h succeeded
  else .postState (Nat.lt_of_not_le h) (postStateRoot ())

/-- The receipt of a transaction, from its outcome, the gas of the block so far and its logs.

Its Bloom filter is the filter of its logs. -/
def makeReceipt {fork : Fork} (outcome : Outcome fork) (cumulativeGasUsed : Nat)
    (logs : List Log) : Receipt fork :=
  -- `R_b` is the filter of the logs `R_l`: the OR of `M(O)` over each log `O`.
  ⟨outcome, cumulativeGasUsed, logsBloom logs, logs⟩

/-- The receipts of some transactions, after `gasUsed` gas of their block.

Each transaction gives its outcome, the gas it used and its logs.

From Glamsterdam, the gas it used is the gas that its sender paid. -/
def makeReceiptsFrom {fork : Fork} (gasUsed : Nat) :
    List (Outcome fork × Nat × List Log) → List (Receipt fork)
  | [] => []
  -- Yellow Paper §12.3: `R[n]_u = Upsilon^g(sigma[n - 1], B_T[n]) + R[n - 1]_u`.
  --
  -- Each result carries its `Upsilon^g`.
  --
  -- From Glamsterdam, it is the gas that its sender pays, by EIP-7778.
  | (outcome, gas, logs) :: rest =>
    makeReceipt outcome (gasUsed + gas) logs :: makeReceiptsFrom (gasUsed + gas) rest

/-- The receipts of the transactions of a block, in order.

Each transaction gives its outcome, the gas it used and its logs.

From Glamsterdam, the gas it used is the gas that its sender paid. -/
def makeReceipts {fork : Fork} (results : List (Outcome fork × Nat × List Log)) :
    List (Receipt fork) :=
  -- `R[n]_u = 0` for `n < 0`.
  makeReceiptsFrom 0 results

/-- Why some bytes hold no receipt. -/
inductive ReceiptError where
  /-- The input is empty. -/
  | emptyReceipt
  /-- The first byte names a type of transaction that the fork does not have. -/
  | unsupportedType (type : UInt8)
  /-- The RLP form holds no receipt. -/
  | decoding (error : RlpError)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

The codes start at 101, above every code of an RLP error, so that the two never meet.


A new constructor takes a new code, so that each code keeps its meaning. -/
def ReceiptError.code : ReceiptError → UInt32
  | .emptyReceipt => 101
  | .unsupportedType _ => 102
  | .decoding _ => 103

/-- The bytes of the receipt of a transaction of type `type`, where type 0 is a legacy transaction.

The receipt of a legacy transaction is its RLP form.

The receipt of a typed transaction is the type, then the RLP form.

It fails only when an RLP payload has `2^64` bytes or more. -/
def encodeReceipt {fork : Fork} (type : UInt8) (r : Receipt fork) : Except RlpError ByteArray :=
  -- Yellow Paper §4.4.2, the value of `p_R`: `RLP(L_R(R))` for `R_x = 0`.
  --
  -- And `(R_x) · RLP(L_R(R))` otherwise.
  if type = 0 then Codec.encode r else typedBytes type <$> Codec.encode r

/-- The type of the transaction and the receipt that `bytes` hold at `fork`.

A first byte of at least `0xc0` starts the receipt of a legacy transaction, of type 0.

Any other first byte is the type of a transaction, which the fork must have. -/
def decodeReceipt (fork : Fork) (bytes : ByteArray) :
    Except ReceiptError (UInt8 × Receipt fork) :=
  if h : 0 < bytes.size then
    let first := bytes[0]
    -- EIP-2718: a legacy receipt is an RLP list, whose first byte is at least `0xc0`.
    if 0xc0 ≤ first then
      ((0, ·) <$> Codec.decode bytes).mapError .decoding
    else
      -- Else the first byte is the type `R_x`, at most `0x7f` by EIP-2718.
      --
      -- The rest is `RLP(L_R(R))`.
      --
      -- The fork must have that type of transaction.
      match typeFork first with
      | some since =>
        if since ≤ fork then
          ((first, ·) <$> Codec.decode (bytes.extract 1 bytes.size)).mapError .decoding
        else .error (.unsupportedType first)
      | none => .error (.unsupportedType first)
  else .error .emptyReceipt

end EthLib.Execution.Blocks
