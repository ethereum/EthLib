module

public import EthLib.Base.Hash32
public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# `Consensus.Containers.PowBlock`

From Bellatrix: a block of the proof-of-work chain, as the fork choice of the merge reads it.

The first payload of the beacon chain must follow a terminal block of that chain.

Its form is the same at every fork from Bellatrix on.

[EIP-3675] defines the terminal block.

[EIP-3675]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-3675.md#definitions
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- A block of the proof-of-work chain, with the total difficulty of its chain. -/
structure PowBlock where
  /-- The hash of the block. -/
  blockHash : Hash32
  /-- The hash of its parent. -/
  parentHash : Hash32
  /-- The total difficulty of the chain up to the block. -/
  totalDifficulty : U256
  deriving DecidableEq, Repr

instance : SszType PowBlock :=
  .container ["block_hash", "parent_hash", "total_difficulty"]
    (fun b => (b.blockHash, b.parentHash, b.totalDifficulty))
    (fun (blockHash, parentHash, totalDifficulty) => ⟨blockHash, parentHash, totalDifficulty⟩)

end EthLib.Consensus
