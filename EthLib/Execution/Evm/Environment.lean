module

public import EthLib.Base.Address
public import EthLib.Base.Fork
public import EthLib.Base.Hash32
public import EthLib.Base.U256
public import EthLib.Execution.Fees.BlobBaseFee

/-!
# `Evm.Environment`

What the EVM reads about the block and the transaction that run the code.

These values stay fixed for the whole transaction.

A value that a fork adds is a field from that fork on.

The subsection Execution Environment of the Yellow Paper, Shanghai version, lists them.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that add a field:

- [EIP-1559][eip1559], the base fee
- [EIP-4399][eip4399], the randomness of the beacon chain
- [EIP-4788][eip4788], the root of the parent beacon block
- [EIP-4844][eip4844], the excess blob gas and the blob hashes
- [EIP-7843][eip7843], the slot number
- [EIP-7892][eip7892], the blob schedule of the chain

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip1559]: https://eips.ethereum.org/EIPS/eip-1559#specification
[eip4399]: https://eips.ethereum.org/EIPS/eip-4399#specification
[eip4788]: https://eips.ethereum.org/EIPS/eip-4788#specification
[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#parameters
[eip7843]: https://eips.ethereum.org/EIPS/eip-7843#specification
[eip7892]: https://eips.ethereum.org/EIPS/eip-7892#execution-layer-configuration
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address BlobSchedule Bytes32 Fork Hash32 Since U256)

/-- The block that runs the code, at fork `fork`. -/
structure BlockEnvironment (fork : Fork) where
  /-- The identifier of the chain. -/
  chainId : Nat
  /-- The address that receives the fees of the block. -/
  coinbase : Address
  /-- The number of the block. -/
  number : Nat
  /-- The gas limit of the block. -/
  gasLimit : Nat
  /-- The time of the block, in seconds since the Unix epoch. -/
  timestamp : U256
  /-- The difficulty of the block, which EIP-3675 fixes to 0 from Paris. -/
  difficulty : Nat
  /-- The hashes of the blocks before this one, oldest first, at most 256 of them.

  The last hash is the hash of the parent. -/
  blockHashes : List Hash32
  /-- The base fee per gas of the block, from London. -/
  baseFeePerGas : Since .london fork Nat
  /-- The randomness of the beacon chain, from Paris. -/
  prevRandao : Since .paris fork Bytes32
  /-- The blob gas above the target that the chain has accumulated, from Dencun. -/
  excessBlobGas : Since .dencun fork UInt64
  /-- The root of the parent beacon block, from Dencun. -/
  parentBeaconBlockRoot : Since .dencun fork Hash32
  /-- The slot of the block on the beacon chain, from Glamsterdam. -/
  slotNumber : Since .glamsterdam fork UInt64
  /-- The blob schedule of the block, from Dencun.

  A chain can set its own, and by default it is the schedule of the fork. -/
  blobSchedule : Since .dencun fork BlobSchedule := Fees.BlobBaseFee.blobSchedule fork

/-- The transaction that runs the code, at fork `fork`. -/
structure TransactionEnvironment (fork : Fork) where
  /-- The sender of the transaction. -/
  origin : Address
  /-- The price per gas that the sender pays. -/
  gasPrice : Nat
  /-- The versioned hashes of the blobs of the transaction, from Dencun. -/
  blobVersionedHashes : Since .dencun fork (List Hash32)

end EthLib.Execution.Evm
