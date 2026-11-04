module

public import EthLib.Base.Exports
public import EthLib.Execution.Blocks.Difficulty
public import EthLib.Execution.Exports.Evm

/-!
# `Exports.Pow`

C-ABI exports of proof of work before Paris, for the Python C extension.

Each number crosses the boundary as its big-endian bytes, so no value is truncated.

A fork crosses it as its name, and an unknown name fails with code 0.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Base (bytesToNat)
open EthLib.Exports (Result forkOfName)
open EthLib.Execution.Evm.Exports (bytesOfNat)

/-- The difficulty of a block at a named fork, from its number, its timestamp and its parent.

The parent's ommers count only as none or some. -/
@[export eth_pow_block_difficulty]
def blockDifficultyExport (fork number timestamp parentTimestamp parentDifficulty
    parentOmmers : ByteArray) : Result ByteArray := do
  let fork ← forkOfName fork
  let n (bytes : ByteArray) := bytesToNat bytes.toList
  pure (bytesOfNat (blockDifficulty fork (n number) (n timestamp) (n parentTimestamp)
    (n parentDifficulty) (n parentOmmers ≠ 0)))

end EthLib.Execution.Blocks.Exports
