module

public import EthLib.Networking.Devp2p.P2p

/-!
# `Execution.Network.Protocol`

The versions of the eth capability, and the message IDs that each version uses.

The source is [`caps/eth.md`][eth] of the devp2p specifications, with its "Change Log".

[eth]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/eth.md

EthLib specifies the versions from eth/68 on, which nodes of every current fork speak.

- eth/68, [EIP-5793](https://eips.ethereum.org/EIPS/eip-5793), status Final.
- eth/69, [EIP-7642](https://eips.ethereum.org/EIPS/eip-7642), status Final.
- eth/70, [EIP-7975](https://eips.ethereum.org/EIPS/eip-7975), status Last Call.
- eth/71, [EIP-8159](https://eips.ethereum.org/EIPS/eip-8159), status Last Call.
- eth/72, [EIP-8070](https://eips.ethereum.org/EIPS/eip-8070), status Last Call.

A capability takes as many message IDs as its highest message ID plus one.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Networking.Devp2p

/-- A version of the eth capability. -/
inductive EthVersion where
  /-- eth/68: transaction announcements carry types and sizes. -/
  | eth68
  /-- eth/69: Status carries the block range, BlockRangeUpdate appears, receipts lose the bloom. -/
  | eth69
  /-- eth/70: a peer can request and send part of the receipts of a block. -/
  | eth70
  /-- eth/71: peers exchange block access lists. -/
  | eth71
  /-- eth/72: transaction announcements carry the cells of blobs, and peers exchange cells. -/
  | eth72
  deriving DecidableEq, Repr

namespace EthVersion

/-- A version is before another when it comes earlier in the list. -/
instance : LT EthVersion := ⟨fun a b => a.ctorIdx < b.ctorIdx⟩

/-- A version is at or before another when it comes no later in the list. -/
instance : LE EthVersion := ⟨fun a b => a.ctorIdx ≤ b.ctorIdx⟩

instance (a b : EthVersion) : Decidable (a < b) := Nat.decLt _ _

instance (a b : EthVersion) : Decidable (a ≤ b) := Nat.decLe _ _

/-- The version number, as a node announces it in Hello and in Status. -/
def number : EthVersion → Nat
  | eth68 => 68
  | eth69 => 69
  | eth70 => 70
  | eth71 => 71
  | eth72 => 72

/-- The version with a number, if EthLib specifies one. -/
def ofNumber? : Nat → Option EthVersion
  | 68 => some eth68
  | 69 => some eth69
  | 70 => some eth70
  | 71 => some eth71
  | 72 => some eth72
  | _ => none

/--
The number of message IDs of a version: its highest message ID plus one.

- eth/68 ends with Receipts (0x10).
- eth/69 adds BlockRangeUpdate (0x11), and eth/70 adds no message.
- eth/71 adds GetBlockAccessLists (0x12) and BlockAccessLists (0x13).
- eth/72 adds GetCells (0x14) and Cells (0x15).
-/
def messageCount : EthVersion → Nat
  | eth68 => 0x11
  | eth69 | eth70 => 0x12
  | eth71 => 0x14
  | eth72 => 0x16

end EthVersion

/-- The name of the capability, `eth` in ASCII. -/
def ETH_NAME : ByteArray := ⟨#[0x65, 0x74, 0x68]⟩

/-- The capability of a version, as a node lists it in Hello. -/
def EthVersion.capability (v : EthVersion) : Capability := ⟨ETH_NAME, v.number⟩

/-- The number of message IDs of a capability, for the multiplexing of RLPx.

It is the count of an eth version that EthLib specifies, and 0 for any other capability. -/
def ethLength (c : Capability) : Nat :=
  if c.name = ETH_NAME then ((EthVersion.ofNumber? c.version).map (·.messageCount)).getD 0
  else 0

end EthLib.Execution.Network
