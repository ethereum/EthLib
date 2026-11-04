module

public import EthLib.Base.Address
public import EthLib.Base.Fork
public import EthLib.Base.Hash32
public import EthLib.Base.U256
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Serialization.Rlp.Codec

/-!
# `Blocks.Header`

The header of a block, at each fork.

Frontier has 15 fields, and later forks append fields after them.

A field that appears at a fork holds a value only from that fork on.

The RLP form of a header is the list of the fields it holds, in order.

So a London header is a list of 16 items, and a Pectra header a list of 21.

The hash of a header is the Keccak-256 hash of its RLP form.

Sections 4.4 and 4.4.3 of the Yellow Paper, Shanghai version, define the header: [`Paper.tex`][yp].

Each later field names the EIP that adds it:

- [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559#specification), the base fee at London
- [EIP-4895][eip-4895], the withdrawals root at Shapella
- [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#header-extension), the blob gas at Dencun
- [EIP-4788][eip-4788], the parent beacon block root at Dencun
- [EIP-7685](https://eips.ethereum.org/EIPS/eip-7685#block-header), the requests hash at Pectra
- [EIP-7928][eip-7928], the block access list hash at Glamsterdam
- [EIP-7843](https://eips.ethereum.org/EIPS/eip-7843#header-extension), the slot at Glamsterdam

[EIP-3675][eip-3675] fixes the ommers hash, the difficulty and the nonce from Paris.

[EIP-4399][eip-4399] puts the RANDAO mix in the mix digest from Paris.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip-3675]: https://eips.ethereum.org/EIPS/eip-3675#block-structure
[eip-4399]: https://eips.ethereum.org/EIPS/eip-4399#block-structure
[eip-4788]: https://eips.ethereum.org/EIPS/eip-4788#block-structure-and-validity
[eip-4895]: https://eips.ethereum.org/EIPS/eip-4895#new-field-in-the-execution-payload-header-withdrawals-root
[eip-7928]: https://eips.ethereum.org/EIPS/eip-7928#block-structure-modification
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

/-- The header of a block at fork `fork`. -/
structure Header (fork : Fork) : Type where
  /-- The hash of the parent's header. -/
  parentHash : Hash32
  /-- The hash of the list of ommer headers.

  From Paris, EIP-3675 fixes it to the hash of the RLP form of the empty list. -/
  ommersHash : Hash32
  /-- The account that the block pays its fees to, called the beneficiary. -/
  coinbase : Address
  /-- The root of the state trie after the block. -/
  stateRoot : Hash32
  /-- The root of the trie of the transactions. -/
  transactionsRoot : Hash32
  /-- The root of the trie of the receipts. -/
  receiptRoot : Hash32
  /-- The Bloom filter of the logs of the block. -/
  bloom : Bytes256
  /-- The difficulty of proof of work, which EIP-3675 fixes to 0 from Paris. -/
  difficulty : Nat
  /-- The count of ancestors of the block. -/
  number : Nat
  /-- The most gas that the transactions of the block may use. -/
  gasLimit : Nat
  /-- The gas that the transactions of the block use. -/
  gasUsed : Nat
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : U256
  /-- Free bytes that the producer of the block chooses. -/
  extraData : ByteArray
  /-- The mix digest of proof of work before Paris, and the RANDAO mix from Paris. -/
  prevRandao : Bytes32
  /-- The nonce of proof of work, which EIP-3675 fixes to 8 zero bytes from Paris. -/
  nonce : Bytes8
  /-- The base fee per gas, from London. -/
  baseFeePerGas : Since .london fork Nat
  /-- The root of the trie of the withdrawals, from Shapella. -/
  withdrawalsRoot : Since .shapella fork Hash32
  /-- The blob gas that the transactions use, from Dencun. -/
  blobGasUsed : Since .dencun fork UInt64
  /-- The blob gas above the target before the block, from Dencun. -/
  excessBlobGas : Since .dencun fork UInt64
  /-- The root of the parent beacon block, from Dencun. -/
  parentBeaconBlockRoot : Since .dencun fork Hash32
  /-- The hash of the requests of the block to the consensus layer, from Pectra. -/
  requestsHash : Since .pectra fork Hash32
  /-- The hash of the block access list, from Glamsterdam. -/
  blockAccessListHash : Since .glamsterdam fork Hash32
  /-- The slot of the beacon chain for the block, from Glamsterdam.

  It follows the block access list hash. -/
  slotNumber : Since .glamsterdam fork UInt64

namespace Header

/-- The count of fields of a header at `fork`: the 15 of Frontier, and those added since. -/
def fieldCount (fork : Fork) : Nat :=
  15 + Item.sinceCount .london fork + Item.sinceCount .shapella fork
    + 3 * Item.sinceCount .dencun fork + Item.sinceCount .pectra fork
    + 2 * Item.sinceCount .glamsterdam fork

variable {fork : Fork}

/-- The item of a header: the list of the fields that it holds, in order. -/
def toItem (h : Header fork) : Item :=
  .list ([Codec.toItem h.parentHash, Codec.toItem h.ommersHash,
    Codec.toItem h.coinbase, Codec.toItem h.stateRoot, Codec.toItem h.transactionsRoot,
    Codec.toItem h.receiptRoot, Codec.toItem h.bloom, Codec.toItem h.difficulty,
    Codec.toItem h.number, Codec.toItem h.gasLimit, Codec.toItem h.gasUsed,
    Codec.toItem h.timestamp, Codec.toItem h.extraData, Codec.toItem h.prevRandao,
    Codec.toItem h.nonce] ++ Item.ofSince h.baseFeePerGas ++ Item.ofSince h.withdrawalsRoot
    ++ Item.ofSince h.blobGasUsed ++ Item.ofSince h.excessBlobGas
    ++ Item.ofSince h.parentBeaconBlockRoot ++ Item.ofSince h.requestsHash
    ++ Item.ofSince h.blockAccessListHash ++ Item.ofSince h.slotNumber)

/-- The header that an item holds: a list of the fields of the fork, in order. -/
def ofItem (item : Item) : Except RlpError (Header fork) := do
  let n := fieldCount fork
  let items ← item.fields n
  let (parentHash, items) ← Item.readField (α := Hash32) n items
  let (ommersHash, items) ← Item.readField (α := Hash32) n items
  let (coinbase, items) ← Item.readField (α := Address) n items
  let (stateRoot, items) ← Item.readField (α := Hash32) n items
  let (transactionsRoot, items) ← Item.readField (α := Hash32) n items
  let (receiptRoot, items) ← Item.readField (α := Hash32) n items
  let (bloom, items) ← Item.readField (α := Bytes256) n items
  let (difficulty, items) ← Item.readField (α := Nat) n items
  let (number, items) ← Item.readField (α := Nat) n items
  let (gasLimit, items) ← Item.readField (α := Nat) n items
  let (gasUsed, items) ← Item.readField (α := Nat) n items
  let (timestamp, items) ← Item.readField (α := U256) n items
  let (extraData, items) ← Item.readField (α := ByteArray) n items
  let (prevRandao, items) ← Item.readField (α := Bytes32) n items
  let (nonce, items) ← Item.readField (α := Bytes8) n items
  let (baseFeePerGas, items) ← Item.readSince (f := .london) (α := Nat) n items
  let (withdrawalsRoot, items) ← Item.readSince (f := .shapella) (α := Hash32) n items
  let (blobGasUsed, items) ← Item.readSince (f := .dencun) (α := UInt64) n items
  let (excessBlobGas, items) ← Item.readSince (f := .dencun) (α := UInt64) n items
  let (parentBeaconBlockRoot, items) ← Item.readSince (f := .dencun) (α := Hash32) n items
  let (requestsHash, items) ← Item.readSince (f := .pectra) (α := Hash32) n items
  let (blockAccessListHash, items) ← Item.readSince (f := .glamsterdam) (α := Hash32) n items
  let (slotNumber, _) ← Item.readSince (f := .glamsterdam) (α := UInt64) n items
  return ⟨parentHash, ommersHash, coinbase, stateRoot, transactionsRoot, receiptRoot, bloom,
    difficulty, number, gasLimit, gasUsed, timestamp, extraData, prevRandao, nonce,
    baseFeePerGas, withdrawalsRoot, blobGasUsed, excessBlobGas, parentBeaconBlockRoot,
    requestsHash, blockAccessListHash, slotNumber⟩

end Header

instance {fork : Fork} : Codec (Header fork) := ⟨Header.toItem, Header.ofItem⟩

namespace Header

open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The hash of a header: the Keccak-256 hash of its RLP form.

Section 4.4.4 of the Yellow Paper finds the parent of a block by this hash.

It fails only when a field has `2^64` bytes or more, since RLP cannot encode it. -/
def hash {fork : Fork} (h : Header fork) : Except RlpError Hash32 := do
  let bytes ← Codec.encode h
  return keccak256 bytes

end Header

end EthLib.Execution.Blocks
