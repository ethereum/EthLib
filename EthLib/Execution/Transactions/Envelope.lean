module

public import EthLib.Base.Hash32
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Transactions.Types
public import EthLib.Serialization.Rlp.Codec

/-!
# `Transactions.Envelope`

The bytes of a transaction, and its hash.

A legacy transaction is the RLP list of its fields, so its first byte is at least `0xc0`.

A typed transaction is its type, then the RLP list of its fields.

[EIP-2718](https://eips.ethereum.org/EIPS/eip-2718#transactions) keeps each type at most `0x7f`.

So the first byte tells the two forms apart.

A fork accepts only the types that it or an earlier fork added.

The hash of a transaction is the Keccak-256 hash of its bytes.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Serialization.Rlp

/-! ## The RLP form of each kind -/

/-- An access list entry is the list of its account and its storage slots. -/
instance : Codec Access where
  toItem a := .list [Codec.toItem a.account, Codec.toItem a.slots]
  ofItem item := do
    match ← item.fields 2 with
    | [account, slots] =>
      return { account := ← Item.field 0 account, slots := ← Item.field 1 slots }
    | items => .error (.wrongFieldCount 2 items.length)

/-- An authorization is the list of its six fields, in order. -/
instance : Codec Authorization where
  toItem a := .list [Codec.toItem a.chainId, Codec.toItem a.address, Codec.toItem a.nonce,
    Codec.toItem a.yParity, Codec.toItem a.r, Codec.toItem a.s]
  ofItem item := do
    match ← item.fields 6 with
    | [chainId, address, nonce, yParity, r, s] =>
      return {
        chainId := ← Item.field 0 chainId
        address := ← Item.field 1 address
        nonce := ← Item.field 2 nonce
        yParity := ← Item.field 3 yParity
        r := ← Item.field 4 r
        s := ← Item.field 5 s }
    | items => .error (.wrongFieldCount 6 items.length)

/-- A legacy transaction is the list of its nine fields, in order. -/
instance : Codec LegacyTransaction where
  toItem tx := .list [Codec.toItem tx.nonce, Codec.toItem tx.gasPrice, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.v,
    Codec.toItem tx.r, Codec.toItem tx.s]
  ofItem item := do
    match ← item.fields 9 with
    | [nonce, gasPrice, gas, to, value, data, v, r, s] =>
      return {
        nonce := ← Item.field 0 nonce
        gasPrice := ← Item.field 1 gasPrice
        gas := ← Item.field 2 gas
        to := ← Item.field 3 to
        value := ← Item.field 4 value
        data := ← Item.field 5 data
        v := ← Item.field 6 v
        r := ← Item.field 7 r
        s := ← Item.field 8 s }
    | items => .error (.wrongFieldCount 9 items.length)

/-- The payload of a transaction of type 1 is the list of its eleven fields, in order. -/
instance : Codec AccessListTransaction where
  toItem tx := .list [Codec.toItem tx.chainId, Codec.toItem tx.nonce, Codec.toItem tx.gasPrice,
    Codec.toItem tx.gas, Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data,
    Codec.toItem tx.accessList, Codec.toItem tx.yParity, Codec.toItem tx.r, Codec.toItem tx.s]
  ofItem item := do
    match ← item.fields 11 with
    | [chainId, nonce, gasPrice, gas, to, value, data, accessList, yParity, r, s] =>
      return {
        chainId := ← Item.field 0 chainId
        nonce := ← Item.field 1 nonce
        gasPrice := ← Item.field 2 gasPrice
        gas := ← Item.field 3 gas
        to := ← Item.field 4 to
        value := ← Item.field 5 value
        data := ← Item.field 6 data
        accessList := ← Item.field 7 accessList
        yParity := ← Item.field 8 yParity
        r := ← Item.field 9 r
        s := ← Item.field 10 s }
    | items => .error (.wrongFieldCount 11 items.length)

/-- The payload of a transaction of type 2 is the list of its twelve fields, in order. -/
instance : Codec FeeMarketTransaction where
  toItem tx := .list [Codec.toItem tx.chainId, Codec.toItem tx.nonce,
    Codec.toItem tx.maxPriorityFeePerGas, Codec.toItem tx.maxFeePerGas, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.accessList,
    Codec.toItem tx.yParity, Codec.toItem tx.r, Codec.toItem tx.s]
  ofItem item := do
    match ← item.fields 12 with
    | [chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data, accessList,
        yParity, r, s] =>
      return {
        chainId := ← Item.field 0 chainId
        nonce := ← Item.field 1 nonce
        maxPriorityFeePerGas := ← Item.field 2 maxPriorityFeePerGas
        maxFeePerGas := ← Item.field 3 maxFeePerGas
        gas := ← Item.field 4 gas
        to := ← Item.field 5 to
        value := ← Item.field 6 value
        data := ← Item.field 7 data
        accessList := ← Item.field 8 accessList
        yParity := ← Item.field 9 yParity
        r := ← Item.field 10 r
        s := ← Item.field 11 s }
    | items => .error (.wrongFieldCount 12 items.length)

/-- The payload of a transaction of type 3 is the list of its fourteen fields, in order. -/
instance : Codec BlobTransaction where
  toItem tx := .list [Codec.toItem tx.chainId, Codec.toItem tx.nonce,
    Codec.toItem tx.maxPriorityFeePerGas, Codec.toItem tx.maxFeePerGas, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.accessList,
    Codec.toItem tx.maxFeePerBlobGas, Codec.toItem tx.blobVersionedHashes,
    Codec.toItem tx.yParity, Codec.toItem tx.r, Codec.toItem tx.s]
  ofItem item := do
    match ← item.fields 14 with
    | [chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data, accessList,
        maxFeePerBlobGas, blobVersionedHashes, yParity, r, s] =>
      return {
        chainId := ← Item.field 0 chainId
        nonce := ← Item.field 1 nonce
        maxPriorityFeePerGas := ← Item.field 2 maxPriorityFeePerGas
        maxFeePerGas := ← Item.field 3 maxFeePerGas
        gas := ← Item.field 4 gas
        to := ← Item.field 5 to
        value := ← Item.field 6 value
        data := ← Item.field 7 data
        accessList := ← Item.field 8 accessList
        maxFeePerBlobGas := ← Item.field 9 maxFeePerBlobGas
        blobVersionedHashes := ← Item.field 10 blobVersionedHashes
        yParity := ← Item.field 11 yParity
        r := ← Item.field 12 r
        s := ← Item.field 13 s }
    | items => .error (.wrongFieldCount 14 items.length)

/-- The payload of a transaction of type 4 is the list of its thirteen fields, in order. -/
instance : Codec SetCodeTransaction where
  toItem tx := .list [Codec.toItem tx.chainId, Codec.toItem tx.nonce,
    Codec.toItem tx.maxPriorityFeePerGas, Codec.toItem tx.maxFeePerGas, Codec.toItem tx.gas,
    Codec.toItem tx.to, Codec.toItem tx.value, Codec.toItem tx.data, Codec.toItem tx.accessList,
    Codec.toItem tx.authorizations, Codec.toItem tx.yParity, Codec.toItem tx.r,
    Codec.toItem tx.s]
  ofItem item := do
    match ← item.fields 13 with
    | [chainId, nonce, maxPriorityFeePerGas, maxFeePerGas, gas, to, value, data, accessList,
        authorizations, yParity, r, s] =>
      return {
        chainId := ← Item.field 0 chainId
        nonce := ← Item.field 1 nonce
        maxPriorityFeePerGas := ← Item.field 2 maxPriorityFeePerGas
        maxFeePerGas := ← Item.field 3 maxFeePerGas
        gas := ← Item.field 4 gas
        to := ← Item.field 5 to
        value := ← Item.field 6 value
        data := ← Item.field 7 data
        accessList := ← Item.field 8 accessList
        authorizations := ← Item.field 9 authorizations
        yParity := ← Item.field 10 yParity
        r := ← Item.field 11 r
        s := ← Item.field 12 s }
    | items => .error (.wrongFieldCount 13 items.length)

/-! ## The envelope -/

/-- The bytes of a typed transaction: its type, then its payload. -/
def typedBytes (type : UInt8) (payload : ByteArray) : ByteArray :=
  ⟨#[type]⟩ ++ payload

/-- The bytes of a transaction.

A legacy transaction is its RLP encoding, and a typed transaction is its type then its payload.

It fails only when an RLP payload has 2^64 bytes or more. -/
def encodeTransaction : Transaction → Except RlpError ByteArray
  | .legacy tx => Codec.encode tx
  | .accessList tx => typedBytes 1 <$> Codec.encode tx
  | .feeMarket tx => typedBytes 2 <$> Codec.encode tx
  | .blob tx => typedBytes 3 <$> Codec.encode tx
  | .setCode tx => typedBytes 4 <$> Codec.encode tx

/-- The typed transaction of type `type` that `payload` encodes.

A type that no fork has holds no transaction. -/
def decodePayload (type : UInt8) (payload : ByteArray) : Except TransactionError Transaction :=
  if type = 1 then (.accessList <$> Codec.decode payload).mapError .decoding
  else if type = 2 then (.feeMarket <$> Codec.decode payload).mapError .decoding
  else if type = 3 then (.blob <$> Codec.decode payload).mapError .decoding
  else if type = 4 then (.setCode <$> Codec.decode payload).mapError .decoding
  else .error (.unsupportedType type)

/-- The transaction that `bytes` encodes at `fork`.

A first byte of at least `0xc0` starts a legacy transaction, which every fork accepts.

Any other first byte is a type, which the fork must have. -/
def decodeTransaction (fork : Fork) (bytes : ByteArray) : Except TransactionError Transaction :=
  if h : 0 < bytes.size then
    let first := bytes[0]
    if 0xc0 ≤ first then
      (.legacy <$> Codec.decode bytes).mapError .decoding
    else
      match typeFork first with
      | some since =>
        if since ≤ fork then decodePayload first (bytes.extract 1 bytes.size)
        else .error (.unsupportedType first)
      | none => .error (.unsupportedType first)
  else .error .emptyTransaction

/-- The hash of a transaction: the Keccak-256 hash of its bytes. -/
def transactionHash (tx : Transaction) : Except RlpError Hash32 := do
  return Cryptography.Hash.Keccak.keccak256 (← encodeTransaction tx)

end EthLib.Execution.Transactions
