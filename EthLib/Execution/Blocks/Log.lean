module

public import EthLib.Base.Address
public import EthLib.Base.Hash32
public import EthLib.Serialization.Rlp.Codec

/-!
# `Blocks.Log`

A log: an address, a list of topics and free data, which a LOG instruction writes.

Its RLP form is the list `[address, topics, data]`.

Section 4.4.1 of the Yellow Paper, Shanghai version, defines it: [`Paper.tex`][yp].

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp

/-- A log entry. -/
structure Log where
  /-- The account whose code wrote the log. -/
  address : Address
  /-- The topics that a reader can filter on. -/
  topics : List Hash32
  /-- The data of the log. -/
  data : ByteArray

/-- A log is the list of its three fields, in order. -/
instance : Codec Log where
  toItem l := .list [Codec.toItem l.address, Codec.toItem l.topics, Codec.toItem l.data]
  ofItem item := do
    match ← item.fields 3 with
    | [address, topics, data] =>
      return {
        address := ← Item.field 0 address
        topics := ← Item.field 1 topics
        data := ← Item.field 2 data }
    | items => .error (.wrongFieldCount 3 items.length)

end EthLib.Execution.Blocks
