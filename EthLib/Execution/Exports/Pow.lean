module

public import EthLib.Base.Exports
public import EthLib.Execution.Blocks.Difficulty
public import EthLib.Execution.Blocks.ProofOfWork
public import EthLib.Execution.Exports.Evm

/-!
# `Exports.Pow`

C-ABI exports of proof of work before Paris, for the Python C extension.

Each number crosses the boundary as its big-endian bytes, so no value is truncated.

A fork crosses it as its name, and an unknown name fails with code 0.

A header crosses it as its RLP bytes, and a header that the decoder rejects fails with its RLP code.

The proof-of-work check takes a fork before Paris, and fails with code 0 at a later one.
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

/-- The header at a named fork that RLP bytes hold. -/
def headerOf (fork header : ByteArray) : Result (Σ fork : Base.Fork, Header fork) := do
  let fork ← forkOfName fork
  let header : Header fork ← (Serialization.Rlp.Codec.decode header).mapError
    fun e => (e.code, s!"header rejected: {reprStr e}")
  pure ⟨fork, header⟩

/-- The seal hash of a header: the Keccak-256 hash of the header without mix digest and nonce. -/
@[export eth_pow_seal_hash]
def sealHashExport (fork header : ByteArray) : Result ByteArray := do
  let ⟨_, header⟩ ← headerOf fork header
  let hash ← header.sealHash.mapError fun e => (e.code, s!"header has no encoding: {reprStr e}")
  pure ⟨hash.toArray⟩

/-- Check the proof of work of a header in RLP form, at a named fork before Paris. -/
@[export eth_pow_check]
def checkExport (fork header : ByteArray) : Result UInt8 := do
  let ⟨fork, header⟩ ← headerOf fork header
  if .paris ≤ fork then throw (0, "a header from Paris on has no proof of work")
  (checkProofOfWork header).map (fun () => 1) |>.mapError
    fun e => (e.code, s!"proof of work invalid: {reprStr e}")

end EthLib.Execution.Blocks.Exports
