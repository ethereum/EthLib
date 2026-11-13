module

public import EthLib.Execution.Rpc.Base

/-!
# `Execution.Rpc.BlockParam`

The block parameter of the execution JSON-RPC API: the block whose state or contents a query reads.

A query names the block by its number, by a tag, or by its hash.

The schemas are those of [`block.yaml`][block].

The tag `earliest` names the lowest block the node holds, and `latest` the head of its chain.

The tag `safe` names the most recent block that is safe from reorgs under honest majority.

The tag `finalized` names the most recent block that is final.

The tag `pending` names a block that the node builds on top of `latest`.

A range of blocks takes every tag but `pending`.

A hash may also come in the object of [EIP-1898][eip1898], with a flag that the block be canonical.

That flag is `false` when absent.

A number may come in such an object too.

Both objects forbid other members, and none of their members may be `null`.

The schema for a number, a tag or a hash is an `anyOf`, so a string may match it in two ways.

A string of exactly 64 hex digits whose first digit is not `0` is both a number and a hash.

The official fixtures read such a string as a hash, as in [a balance query by hash][fixture].

So the reader reads a string as a hash first, then as a number, then as a tag.

[block]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/src/schemas/block.yaml
[fixture]: https://github.com/ethereum/execution-apis/blob/3284ee80c3da3e516c53782dde75157cccf1ebdc/tests/eth_getBalance/get-balance-blockhash.io
[eip1898]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-1898.md#specification
-/

@[expose] public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- A tag that names a block by its role rather than by its number or hash. -/
inductive BlockTag where
  /-- The lowest block that the node holds. -/
  | earliest
  /-- The most recent block that is final. -/
  | finalized
  /-- The most recent block that is safe from reorgs under honest majority. -/
  | safe
  /-- The head of the canonical chain of the node. -/
  | latest
  /-- A block that the node builds on top of the head. -/
  | pending
  deriving DecidableEq, Repr

/-- The name of a tag, as JSON writes it. -/
def BlockTag.name : BlockTag → String
  | .earliest => "earliest"
  | .finalized => "finalized"
  | .safe => "safe"
  | .latest => "latest"
  | .pending => "pending"

/-- The tag of a name, if the name is one. -/
def BlockTag.ofName? : String → Option BlockTag
  | "earliest" => some .earliest
  | "finalized" => some .finalized
  | "safe" => some .safe
  | "latest" => some .latest
  | "pending" => some .pending
  | _ => none

/-- How a query names a block. -/
inductive BlockParam where
  /-- The block of this number in the canonical chain. -/
  | number (n : Nat)
  /-- The block that the tag names. -/
  | tag (t : BlockTag)
  /-- The block of this hash; `requireCanonical` asks that it be in the canonical chain. -/
  | hash (h : Hash32) (requireCanonical : Bool)
  deriving DecidableEq, Repr

/-- A tag, given by its name. -/
def blockTag (what : String) : Json → Read BlockTag
  | .str s => match BlockTag.ofName? s with
    | some t => pure t
    | none => reject s!"{what}: not a block tag"
  | _ => reject s!"{what}: not a string"

/-- A block number or a tag, the schema `BlockNumberOrTag`.

A string that is a tag reads as the tag; any other value must be a number. -/
def blockNumberOrTag (what : String) (j : Json) : Read BlockParam :=
  match blockTag what j with
  | .ok t => pure (.tag t)
  | .error _ => return .number (← uint what j)

/-- A block number or a tag other than `pending`, the schema `BlockNumberOrTagForRange`. -/
def blockNumberOrTagForRange (what : String) (j : Json) : Read BlockParam := do
  match ← blockNumberOrTag what j with
  | .tag .pending => reject s!"{what}: pending is not a block of a range"
  | p => pure p

/-- The flag `requireCanonical` of an object of EIP-1898: a boolean, `false` when absent. -/
def requireCanonical (what : String) : Option Json → Read Bool
  | none => pure false
  | some (.bool b) => pure b
  | some _ => reject s!"{what}: requireCanonical is not a boolean"

/-- A block number, tag or hash, the schema `BlockNumberOrTagOrHash`.

A string reads as a hash if it can, else as a number, else as a tag.

An object is one of the two objects of EIP-1898, with no other member. -/
def blockNumberOrTagOrHash (what : String) (j : Json) : Read BlockParam :=
  match j with
  | .str _ =>
    match hash32 what j, uint what j, blockTag what j with
    | .ok h, _, _ => pure (.hash h false)
    | _, .ok n, _ => pure (.number n)
    | _, _, .ok t => pure (.tag t)
    | _, _, _ => reject s!"{what}: not a block number, tag or hash"
  | .obj kvs => do
    let members := kvs.toList
    match members.lookup "blockNumber", members.lookup "blockHash" with
    | some n, none =>
      unless members.length = 1 do reject s!"{what}: a member other than blockNumber"
      return .number (← uint what n)
    | none, some h =>
      unless members.all fun (k, _) => k == "blockHash" || k == "requireCanonical" do
        reject s!"{what}: a member other than blockHash and requireCanonical"
      return .hash (← hash32 what h) (← requireCanonical what (members.lookup "requireCanonical"))
    | _, _ => reject s!"{what}: not one block number or one block hash"
  | _ => reject s!"{what}: not a string or an object"

/-- A block parameter as JSON.

A number is written as a quantity and a tag as its name.

A hash is written as the object of EIP-1898, with its flag, so that it reads as nothing else. -/
def blockParamJson : BlockParam → Json
  | .number n => quantityJson n
  | .tag t => .str t.name
  | .hash h c => Json.mkObj [("blockHash", dataJson h.toList), ("requireCanonical", .bool c)]

end EthLib.Execution.Rpc
