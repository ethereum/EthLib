module

public import EthLib.Base.Exports.PyValue
public import EthLib.Execution.Blocks.Difficulty
public import EthLib.Execution.Blocks.ProofOfWork
public import EthLib.Execution.Blocks.Ommers
public import EthLib.Execution.Exports.Blocks

/-!
# `Exports.Pow`

C-ABI exports of proof of work before Paris, for the Python C extension.

The difficulty, the forks of a chain, the seal hash and the proof-of-work check take typed values.

A number crosses as an `int`, and a fork as its name, a `str`.

An unknown name fails with code 0.

Hegotá fails with code 0 too, since it is not yet specified.
-/

public section

namespace EthLib.Execution.Blocks.Exports

open EthLib.Exports (ExportError Result PyValue forkUpTo oneLine pyExport rejectArgument toResult)

/-- The difficulty of a block at a named fork, from its number, its timestamp and its parent.

The parent's ommers count only as none or some. -/
def blockDifficultyOf (args : String × Nat × Nat × Nat × Nat × Nat) : Result Nat := do
  let (fork, number, timestamp, parentTimestamp, parentDifficulty, parentOmmers) := args
  let fork ← forkUpTo .glamsterdam fork.toUTF8
  pure (blockDifficulty fork number timestamp parentTimestamp parentDifficulty (parentOmmers ≠ 0))

/-- The difficulty of a block at a named fork, from its number, its timestamp and its parent.

The arguments are the name of the fork, then the number and the timestamp of the block.

Then come the timestamp, the difficulty and the number of ommers of the parent. -/
@[export eth_pow_block_difficulty]
def blockDifficultyExport (args : PyValue) : Result PyValue :=
  pyExport blockDifficultyOf args

/-- The RLP form of the forks of a chain, each with its first block: a list of `[name, block]`.

The ommer check and the rewards root read the forks of a chain in this form. -/
def chainForksOf (forks : List (String × Nat)) : Result ByteArray :=
  toResult "forks have no encoding" (Serialization.Rlp.encode (.list (forks.map fun (name, first) =>
    .list [.bytes name.toUTF8, Serialization.Rlp.Codec.toItem first])))

/-- The RLP form of the forks of a chain, each with its first block.

The argument is the list of the forks, each its name and its first block. -/
@[export eth_pow_chain_forks]
def chainForksExport (args : PyValue) : Result PyValue :=
  pyExport chainForksOf args

/-- The header at a named fork that RLP bytes hold. -/
def headerOf (fork header : ByteArray) : Result (Σ fork : Base.Fork, Header fork) := do
  let fork ← forkUpTo .glamsterdam fork
  -- A header crosses as its RLP bytes.
  --
  -- A header that the decoder rejects fails with its RLP code.
  let header : Header fork ← toResult "header rejected" (Serialization.Rlp.Codec.decode header)
  pure ⟨fork, header⟩

/-- The seal hash of a header at a named fork: its Keccak-256 hash without mix digest and nonce. -/
def sealHashOf (args : String × ByteArray) : Result ByteArray := do
  let ⟨_, header⟩ ← headerOf args.1.toUTF8 args.2
  let hash ← toResult "header has no encoding" header.sealHash
  pure ⟨hash.toArray⟩

/-- The seal hash of a header: the Keccak-256 hash of the header without mix digest and nonce.

The arguments are the name of the fork and the header in RLP form. -/
@[export eth_pow_seal_hash]
def sealHashExport (args : PyValue) : Result PyValue :=
  pyExport sealHashOf args

/-- A proof-of-work error reaches Python with its code, and its message prints it on one line. -/
instance : ExportError PowError where
  code := PowError.code
  message := oneLine

/-- Check the proof of work of a header in RLP form, at a named fork before Paris. -/
def checkOf (args : String × ByteArray) : Result Bool := do
  let ⟨fork, header⟩ ← headerOf args.1.toUTF8 args.2
  -- The proof-of-work check takes a fork before Paris, and fails with code 0 at a later one.
  if .paris ≤ fork then rejectArgument none "a header from Paris on has no proof of work"
  toResult "proof of work invalid" ((checkProofOfWork header).map fun () => true)

/-- Check the proof of work of a header in RLP form, at a named fork before Paris.

The arguments are the name of the fork and the header in RLP form. -/
@[export eth_pow_check]
def checkExport (args : PyValue) : Result PyValue :=
  pyExport checkOf args

/-- An ommer error reaches Python with its code, and its message prints it on one line. -/
instance : ExportError OmmerError where
  code := OmmerError.code
  message := oneLine

/-- Check the ommers of a block in RLP form, against recent blocks, each at the fork of its number.

The forks of the chain are an RLP list of `[name, first block]`, the first one from block 0.

The recent blocks are an RLP list of blocks, oldest first, ending with the parent.

The last seven blocks are enough.

A check seal of 0 leaves out the proof of work of the ommers, as for test chains. -/
@[export eth_pow_validate_ommers]
def validateOmmersExport (forks recent block : ByteArray) (checkSeal : UInt8) :
    Result UInt8 := do
  -- The ommer check takes its forks and its blocks in RLP form.
  let config ← chainOfForks forks
  let items ← match (← toResult "recent rejected" (Serialization.Rlp.decode recent)) with
    | .list items => pure items
    | .bytes _ => rejectArgument none "recent blocks are not a list"
  let recentBlocks ← items.mapM fun item => do
    let ⟨fork, b⟩ ← blockOnChain config item
    pure (RecentBlock.mk fork b.header b.ommers)
  let ⟨_, b⟩ ← blockOnChain config
    (← toResult "block rejected" (Serialization.Rlp.decode block))
  toResult "ommers invalid"
    ((validateOmmers config (checkSeal != 0) recentBlocks b.header b.ommers).map fun () => 1)

end EthLib.Execution.Blocks.Exports
