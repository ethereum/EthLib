module

public import EthLib.Networking.Devp2p.ForkId
public import EthLib.Networking.Enr.Record

/-!
# `Networking.Enr.Eth`

The eth entry of a node record.

The source is the section Entry Format of [`enr-entries/eth.md`][eth].

[eth]: https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/enr-entries/eth.md#entry-format

A node of the eth capability announces its fork identifier in its record.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

/-- The key of the entry, `eth` in ASCII. -/
def KEY_ETH : ByteArray := ⟨#[0x65, 0x74, 0x68]⟩

/-- The value of the entry: the list whose one element is the fork identifier. -/
def ethEntry (id : ForkId) : Item :=
  -- `entry-value = [[ forkHash, forkNext ]]`: a single element list holding an EIP-2124 fork ID.
  .list [Codec.toItem id]

/-- The fork identifier in the value of the entry: its first element. -/
def readEthEntry (item : Item) : Except RlpError ForkId := do
  -- `entry-value` is a list, never a byte string.
  match ← item.toItems with
  -- Its first element is the fork ID `[ forkHash, forkNext ]`.
  --
  -- Implementations should ignore any additional list elements in `entry-value`.
  --
  -- EthLib ignores them, so that later versions of the entry can add some.
  | id :: _ => id.field 0
  -- An empty list holds no fork ID.
  | [] => throw (.wrongFieldCount 1 0)

/-- The fork identifier of the eth entry of a record, or none when the record has no entry. -/
def readEth (r : Enr) : Except RlpError (Option ForkId) :=
  -- `entry-key` is `eth`, in ASCII.
  match r.pairs.find? (·.1 = KEY_ETH) with
  -- A record need not have the entry, as every key but `id` is optional.
  | none => pure none
  | some (_, value) => some <$> readEthEntry value

end EthLib.Networking.Enr
