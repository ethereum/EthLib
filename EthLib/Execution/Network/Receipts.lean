module

public import EthLib.Execution.Blocks.Roots
public import EthLib.Execution.Network.Protocol

/-!
# `Execution.Network.Receipts`

The receipt exchange of the eth capability, from two sections of [`caps/eth.md`][eth].

They are "Receipt Encoding and Validity" and "Protocol Messages".

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md#receipt-encoding-and-validity

- GetReceipts (0x0f) asks for the receipts of blocks by hash.
- Receipts (0x10) answers with one list of receipts for each block.

On eth/68, a receipt has its consensus form, with its Bloom filter.

From eth/69 on, it is `[tx-type, post-state-or-status, cumulative-gas, logs]`, without the filter.

[EIP-7642][eip-7642] says so.

From eth/70 on, a peer may send part of the receipts of a block, as [EIP-7975][eip-7975] says.

- GetReceipts gains `firstBlockReceiptIndex`, the first receipt to send of the first block.
- Receipts gains `lastBlockIncomplete`, set when the list of the last block is cut short.

The fields of a receipt depend on the fork of its block.

So the messages carry each receipt as its RLP item.

A node checks the receipts of a whole block against the receipts root of its header.

To do so, it computes the Bloom filter of each receipt again.

It then encodes each receipt in its consensus form.

[eip-7642]: https://eips.ethereum.org/EIPS/eip-7642#receipts-message-changes
[eip-7975]: https://eips.ethereum.org/EIPS/eip-7975#specification
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks

/-- The message ID of GetReceipts. -/
def GET_RECEIPTS_ID : Nat := 0x0f

/-- The message ID of Receipts. -/
def RECEIPTS_ID : Nat := 0x10

/-- A receipt at fork `fork` as eth/69 sends it, without its Bloom filter. -/
structure WireReceipt (fork : Fork) where
  /-- The type of the transaction, 0 for a legacy transaction. -/
  txType : UInt8
  /-- The state root after the transaction before Byzantium, its status from Byzantium. -/
  outcome : Outcome fork
  /-- The gas that the block used up to and with the transaction. -/
  cumulativeGasUsed : Nat
  /-- The logs that the transaction wrote. -/
  logs : List Log

namespace WireReceipt

variable {fork : Fork}

/-- A receipt as the RLP list `[tx-type, post-state-or-status, cumulative-gas, logs]`. -/
def toItem (r : WireReceipt fork) : Item :=
  .list [Codec.toItem r.txType, Codec.toItem r.outcome, Codec.toItem r.cumulativeGasUsed,
    Codec.toItem r.logs]

/-- The receipt in the RLP list `[tx-type, post-state-or-status, cumulative-gas, logs]`.

The type is a scalar below 256. -/
def ofItem (item : Item) : Except RlpError (WireReceipt fork) := do
  match ← item.fields 4 with
  | [t, o, g, l] => return ⟨← t.field 0, ← o.field 1, ← g.field 2, ← l.field 3⟩
  | items => throw (.wrongFieldCount 4 items.length)

instance : Codec (WireReceipt fork) := ⟨toItem, ofItem⟩

/-- The consensus form of a receipt.

It is its type, and the receipt with the Bloom filter of its logs. -/
def toConsensus (r : WireReceipt fork) : UInt8 × Receipt fork :=
  (r.txType, makeReceipt r.outcome r.cumulativeGasUsed r.logs)

/-- The receipt that eth/69 sends for a receipt in consensus form: the filter left out. -/
def ofConsensus : UInt8 × Receipt fork → WireReceipt fork
  | (t, r) => ⟨t, r.outcome, r.cumulativeGasUsed, r.logs⟩

end WireReceipt

/--
The consensus form of a receipt as a version sends it, at fork `fork`.

On eth/68, a legacy receipt is its RLP list, and a typed one the byte string `type || rlp`.

From eth/69 on, the receipt gets the Bloom filter of its logs back.
-/
def consensusOfItem (version : EthVersion) (fork : Fork) (item : Item) :
    Except ReceiptError (UInt8 × Receipt fork) :=
  if version = .eth68 then
    match item with
    | .list _ => ((0, ·) <$> Codec.ofItem item).mapError .decoding
    | .bytes b =>
      -- A legacy receipt crosses the wire as a list, so a byte string must hold a typed one.
      if b.data.toList.head?.all (· < 0xc0) then decodeReceipt fork b
      else .error (.decoding .bytesAsList)
  else ((WireReceipt.toConsensus (fork := fork)) <$> Codec.ofItem item).mapError .decoding

/--
Whether the receipts of a block, as a version sends them, match the receipts root of its header.

The root is computed over the consensus forms, as "Receipt Encoding and Validity" says.

Receipts that do not read, or that have no root, do not match.
-/
def receiptsMatch (version : EthVersion) (fork : Fork) (receiptsRoot : Hash32)
    (receipts : List Item) : Bool :=
  match receipts.mapM (consensusOfItem version fork) with
  | .ok rs =>
    match Blocks.receiptsRoot rs with
    | .ok root => root = receiptsRoot
    | .error _ => false
  | .error _ => false

/-! ## Partial receipt lists of eth/70 -/

/-- Why a partial list of receipts fails the checks of EIP-7975. -/
inductive PartialReceiptsError where
  /-- More receipts were delivered than the block has transactions. -/
  | tooMany (delivered transactions : Nat)
  /-- A receipt is larger than the gas limit of its transaction divided by 8. -/
  | receiptTooLarge (index size bound : Nat)
  /-- The receipts are larger in total than the gas limit of the block divided by 8. -/
  | totalTooLarge (size bound : Nat)
  deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 501, above every code of the other eth errors.

A new constructor takes a new code, so that each code keeps its meaning. -/
def PartialReceiptsError.code : PartialReceiptsError → UInt32
  | .tooMany .. => 501
  | .receiptTooLarge .. => 502
  | .totalTooLarge .. => 503

/--
The checks that EIP-7975 asks of the receipts of a block that arrive in parts.

`gasLimits` holds the gas limit of each transaction of the block, in order.

`sizes` holds the size in bytes of each receipt delivered so far, from the first one.

- No more receipts than transactions; the list is complete when there are as many.

The EIP asks that the count of receipts "matches" the count of transactions.

A list still in parts has fewer, so EthLib reads the rule as "at most" until the list is complete.

- Each receipt is at most the gas limit of its transaction divided by 8.
- All the receipts together are at most the gas limit of the block divided by 8.

The EIP says only "allowed by the block gas limit" for the total.

So EthLib applies the bound of one transaction to the whole block.

The Rationale of the EIP derives that bound from the gas.

The source is the specification of [EIP-7975][eip-7975].

[eip-7975]: https://eips.ethereum.org/EIPS/eip-7975#specification
-/
def checkPartialReceipts (gasLimits : List Nat) (blockGasLimit : Nat) (sizes : List Nat) :
    Except PartialReceiptsError Unit := do
  if gasLimits.length < sizes.length then throw (.tooMany sizes.length gasLimits.length)
  let indexed := (List.range sizes.length).zip (sizes.zip gasLimits)
  if let some (i, size, gas) := indexed.find? (fun (_, size, gas) => gas / 8 < size) then
    throw (.receiptTooLarge i size (gas / 8))
  if blockGasLimit / 8 < sizes.sum then throw (.totalTooLarge sizes.sum (blockGasLimit / 8))

end EthLib.Execution.Network
