module

public import EthLib.Base.Exports
public import EthLib.Execution.Blocks.Difficulty
public import EthLib.Execution.Blocks.ProofOfWork
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Exports.Blocks
public import EthLib.Execution.Exports.Evm

/-!
# `Exports.Pow`

C-ABI exports of proof of work before Paris, for the Python C extension.

Each number crosses the boundary as its big-endian bytes, so no value is truncated.

A fork crosses it as its name, and an unknown name fails with code 0.

A header crosses it as its RLP bytes, and a header that the decoder rejects fails with its RLP code.

The proof-of-work check takes a fork before Paris, and fails with code 0 at a later one.

Hegotá fails with code 0 too, since it is not yet specified.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Base (bytesToNat)
open EthLib.Exports (Result forkUpTo)
open EthLib.Execution.Evm.Exports (bytesOfNat)

/-- The difficulty of a block at a named fork, from its number, its timestamp and its parent.

The parent's ommers count only as none or some. -/
@[export eth_pow_block_difficulty]
def blockDifficultyExport (fork number timestamp parentTimestamp parentDifficulty
    parentOmmers : ByteArray) : Result ByteArray := do
  let fork ← forkUpTo .glamsterdam fork
  let n (bytes : ByteArray) := bytesToNat bytes.toList
  pure (bytesOfNat (blockDifficulty fork (n number) (n timestamp) (n parentTimestamp)
    (n parentDifficulty) (n parentOmmers ≠ 0)))

/-- The header at a named fork that RLP bytes hold. -/
def headerOf (fork header : ByteArray) : Result (Σ fork : Base.Fork, Header fork) := do
  let fork ← forkUpTo .glamsterdam fork
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

/-- Check the ommers of a block in RLP form, against recent blocks, each at the fork of its number.

The forks of the chain are an RLP list of `[name, first block]`, the first one from block 0.

The recent blocks are an RLP list of blocks, the last seven of the chain, ending with the parent.

A check seal of 0 leaves out the proof of work of the ommers, as for test chains. -/
@[export eth_pow_validate_ommers]
def validateOmmersExport (forks recent block : ByteArray) (checkSeal : UInt8) :
    Result UInt8 := do
  let config ← chainOfForks forks
  let rlpError (what : String) (e : Serialization.Rlp.RlpError) := (e.code, s!"{what}: {reprStr e}")
  let items ← match (← (Serialization.Rlp.decode recent).mapError (rlpError "recent rejected")) with
    | .list items => pure items
    | .bytes _ => throw (0, "recent blocks are not a list")
  let recentBlocks ← items.mapM fun item => do
    let ⟨fork, b⟩ ← blockOnChain config item
    pure (RecentBlock.mk fork b.header b.ommers)
  let ⟨_, b⟩ ← blockOnChain config
    (← (Serialization.Rlp.decode block).mapError (rlpError "block rejected"))
  (validateOmmers config (checkSeal != 0) recentBlocks b.header b.ommers).map (fun () => 1)
    |>.mapError fun e => (e.code, s!"ommers invalid: {reprStr e}")

end EthLib.Execution.Blocks.Exports
