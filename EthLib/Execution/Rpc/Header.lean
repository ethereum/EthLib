module

public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.Rpc.Base

/-!
# `Execution.Rpc.Header`

The header of a block as JSON: the object `Header` of [`block.yaml`][schema].

The object holds the hash of the header and each field of the header, under the names below.

- The ommers hash is `sha3Uncles`, the beneficiary `miner` and the receipts root `receiptsRoot`.
- The bloom filter is `logsBloom`, and the mix digest, the RANDAO mix from Paris, is `mixHash`.
- Each other field has its own name, such as `parentHash` or `baseFeePerGas`.

The object allows no other name.

The header methods of [`block.yaml`][methods] say that a field MUST be omitted before its fork.

The schema requires none of the fields from a fork, so they stay optional after their fork too.

Here the object holds a field exactly from its fork on, as the [fixtures][tests] of the source do.

The hash of a header fails when RLP cannot encode a field, so the writer can fail too.

A method writes the object with the hash that the node keeps for the block instead.

The reader reads the fields of the fork, and nothing else that is not `null`.

Like the other readers of objects, it ignores a field whose value is `null`.

It also requires the hash to be the hash of the header that it reads.

[schema]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block.yaml
[methods]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/eth/block.yaml
[tests]: https://github.com/ethereum/execution-apis/tree/3284ee80c3da3e516c53782dde75157cccf1ebdc/tests/eth_getHeaderByNumber
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Serialization.Rlp (RlpError)
open EthLib.Execution.Blocks (Header)

/-- A field from fork `f` as a named JSON value, or no field before `f`. -/
def sinceField {f fork : Fork} {α : Type} (name : String) (g : α → Json) (x : Since f fork α) :
    List (String × Json) :=
  if h : f ≤ fork then [(name, g (x h))] else []

/-- The name of a field from fork `f`, or no name before `f`. -/
def sinceName (f fork : Fork) (name : String) : List String :=
  if f ≤ fork then [name] else []

/-- The names of the header object at a fork: the hash, then each field that the fork has. -/
def headerNames (fork : Fork) : List String :=
  ["hash", "parentHash", "sha3Uncles", "miner", "stateRoot", "transactionsRoot", "receiptsRoot",
    "logsBloom", "difficulty", "number", "gasLimit", "gasUsed", "timestamp", "extraData",
    "mixHash", "nonce"] ++ sinceName .london fork "baseFeePerGas" ++
    sinceName .shapella fork "withdrawalsRoot" ++ sinceName .dencun fork "blobGasUsed" ++
    sinceName .dencun fork "excessBlobGas" ++ sinceName .dencun fork "parentBeaconBlockRoot" ++
    sinceName .pectra fork "requestsHash" ++ sinceName .glamsterdam fork "blockAccessListHash" ++
    sinceName .glamsterdam fork "slotNumber"

/-- A hash of 32 bytes as JSON. -/
def hash32Json (h : Hash32) : Json := dataJson h.toList

/-- The fields of a header object: the given hash, then each field of the header. -/
def headerFields {fork : Fork} (hash : Hash32) (h : Header fork) : List (String × Json) :=
  [("hash", hash32Json hash), ("parentHash", hash32Json h.parentHash),
    ("sha3Uncles", hash32Json h.ommersHash), ("miner", dataJson h.coinbase.toList),
    ("stateRoot", hash32Json h.stateRoot), ("transactionsRoot", hash32Json h.transactionsRoot),
    ("receiptsRoot", hash32Json h.receiptRoot), ("logsBloom", dataJson h.bloom.toList),
    ("difficulty", quantityJson h.difficulty), ("number", quantityJson h.number),
    ("gasLimit", quantityJson h.gasLimit), ("gasUsed", quantityJson h.gasUsed),
    ("timestamp", quantityJson h.timestamp.toNat),
    ("extraData", dataJson h.extraData.data.toList), ("mixHash", hash32Json h.prevRandao),
    ("nonce", dataJson h.nonce.toList)] ++
    sinceField "baseFeePerGas" quantityJson h.baseFeePerGas ++
    sinceField "withdrawalsRoot" hash32Json h.withdrawalsRoot ++
    sinceField "blobGasUsed" (fun x : UInt64 => quantityJson x.toNat) h.blobGasUsed ++
    sinceField "excessBlobGas" (fun x : UInt64 => quantityJson x.toNat) h.excessBlobGas ++
    sinceField "parentBeaconBlockRoot" hash32Json h.parentBeaconBlockRoot ++
    sinceField "requestsHash" hash32Json h.requestsHash ++
    sinceField "blockAccessListHash" hash32Json h.blockAccessListHash ++
    sinceField "slotNumber" (fun x : UInt64 => quantityJson x.toNat) h.slotNumber

/-- The header object of a header, with its hash.

It fails when the header has no hash, since RLP cannot encode one of its fields. -/
def headerJson {fork : Fork} (h : Header fork) : Except RlpError Json := do
  let hash ← h.hash
  return Json.mkObj (headerFields hash h)

/-- A field from fork `f`, read by its name when the fork has it. -/
def readSince {f : Fork} (fork : Fork) {α : Type} (read : Json → Read α)
    (fs : List (String × Json)) (name : String) : Read (Since f fork α) :=
  if h : f ≤ fork then do
    let x ← read (← field "header" fs name)
    return fun _ => x
  else return fun h' => absurd h' h

/-- A header at a fork, from an object with exactly the fields of that fork and its hash.

A field whose value is `null` counts as absent.

The hash must be the hash of the header that the other fields give. -/
def headerOfJson (fork : Fork) (j : Json) : Read (Header fork) := do
  let fs ← fields "header" j
  unless hasExactly fs (headerNames fork) do reject "header: wrong fields"
  let get := field "header" fs
  let hash ← hash32 "hash" (← get "hash")
  let header : Header fork := {
    parentHash := ← hash32 "parentHash" (← get "parentHash")
    ommersHash := ← hash32 "sha3Uncles" (← get "sha3Uncles")
    coinbase := ← address "miner" (← get "miner")
    stateRoot := ← hash32 "stateRoot" (← get "stateRoot")
    transactionsRoot := ← hash32 "transactionsRoot" (← get "transactionsRoot")
    receiptRoot := ← hash32 "receiptsRoot" (← get "receiptsRoot")
    bloom := ← bytes256 "logsBloom" (← get "logsBloom")
    difficulty := ← uint "difficulty" (← get "difficulty")
    number := ← uint "number" (← get "number")
    gasLimit := ← uint "gasLimit" (← get "gasLimit")
    gasUsed := ← uint "gasUsed" (← get "gasUsed")
    timestamp := ← uint256 "timestamp" (← get "timestamp")
    extraData := ← bytes "extraData" (← get "extraData")
    prevRandao := ← hash32 "mixHash" (← get "mixHash")
    nonce := ← bytes8 "nonce" (← get "nonce")
    baseFeePerGas := ← readSince fork (uint "baseFeePerGas") fs "baseFeePerGas"
    withdrawalsRoot := ← readSince fork (hash32 "withdrawalsRoot") fs "withdrawalsRoot"
    blobGasUsed := ← readSince fork (uint64 "blobGasUsed") fs "blobGasUsed"
    excessBlobGas := ← readSince fork (uint64 "excessBlobGas") fs "excessBlobGas"
    parentBeaconBlockRoot :=
      ← readSince fork (hash32 "parentBeaconBlockRoot") fs "parentBeaconBlockRoot"
    requestsHash := ← readSince fork (hash32 "requestsHash") fs "requestsHash"
    blockAccessListHash :=
      ← readSince fork (hash32 "blockAccessListHash") fs "blockAccessListHash"
    slotNumber := ← readSince fork (uint64 "slotNumber") fs "slotNumber" }
  match header.hash with
  | .ok computed => if computed = hash then return header else reject "hash: not the header hash"
  | .error _ => reject "header: no hash"

end EthLib.Execution.Rpc
