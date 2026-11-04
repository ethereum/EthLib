module

public import EthLib.Networking.Devp2p.ForkId
public import EthLib.Networking.Enr.Record

/-!
# `Networking.Enr.Eth`

The "eth" entry of a node record, from [`enr-entries/eth.md`][eth].

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/enr-entries/eth.md

A node of the eth capability announces its fork identifier in its record.

The value is the RLP list `[[forkHash, forkNext]]`, whose one element is the identifier.

A reader ignores the elements after the first, so that later versions can add some.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Networking.Devp2p
open EthLib.Serialization.Rlp

/-- The key of the entry, `eth` in ASCII. -/
def KEY_ETH : ByteArray := ⟨#[0x65, 0x74, 0x68]⟩

/-- The value of the entry: the list whose one element is the fork identifier. -/
def ethEntry (id : ForkId) : Item :=
  .list [Codec.toItem id]

/-- The fork identifier in the value of the entry: its first element.

The value must be a list with at least one element, and that element a fork identifier.

The elements after the first are ignored. -/
def readEthEntry (item : Item) : Except RlpError ForkId := do
  match ← item.toItems with
  | id :: _ => id.field 0
  | [] => throw (.wrongFieldCount 1 0)

/-- The fork identifier of the "eth" entry of a record, or none when the record has no entry. -/
def readEth (r : Enr) : Except RlpError (Option ForkId) :=
  match r.pairs.find? (·.1 = KEY_ETH) with
  | none => pure none
  | some (_, value) => some <$> readEthEntry value

end EthLib.Networking.Enr
