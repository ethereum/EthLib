module

public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Cryptography.Kzg.VersionedHash
public import EthLib.Execution.Transactions.Validity

/-!
# `Transactions.Network`

The network form of a blob transaction, which peers send in answer to a request for it.

It carries the payload body of the transaction with its blobs, commitments and proofs.

A block holds only the payload body, so the hash of the transaction ignores the rest.

- [EIP-4844][eip4844] gives the form from Dencun, with one proof per blob.
- [EIP-7594][eip7594] gives the form from Fusaka, with one proof per cell of each extended blob.

[eip4844]: https://eips.ethereum.org/EIPS/eip-4844#networking
[eip7594]: https://eips.ethereum.org/EIPS/eip-7594#networking
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Serialization.Rlp

/-- A KZG commitment is the RLP string of its 48 bytes.

Source: "Networking" of [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#networking). -/
instance : Codec KZGCommitment := .wrapper KZGCommitment.mk KZGCommitment.bytes

/-- The version of the network form from Fusaka on. -/
def WRAPPER_VERSION : Nat := 1

/-- A blob transaction with its blobs, their commitments and their proofs. -/
structure NetworkBlobTransaction where
  /-- The transaction that a block holds. -/
  tx : BlobTransaction
  /-- The blobs, one for each versioned hash. -/
  blobs : List Blob
  /-- The KZG commitment of each blob. -/
  commitments : List KZGCommitment
  /-- The KZG proofs: one per blob before Fusaka, one per cell of each extended blob from it. -/
  proofs : List KZGProof
deriving DecidableEq

/-- Every way the network form of a blob transaction can be rejected. -/
inductive NetworkError where
  /-- The bytes hold no blob transaction at the fork, or its RLP has the wrong shape. -/
  | transaction (error : TransactionError)
  /-- The wrapper version is not 1. -/
  | wrongVersion (version : Nat)
  /-- The counts of versioned hashes, blobs, commitments and proofs do not match. -/
  | countMismatch (hashes blobs commitments proofs : Nat)
  /-- The commitment at `index`, counted from 0, hashes to `expected`, not to its versioned hash.

  That versioned hash, at the same position, is `actual`. -/
  | versionedHashMismatch (index : Nat) (expected actual : VersionedHash)
  /-- A blob, a commitment or a proof is not a valid KZG input. -/
  | kzg (error : KzgError)
  /-- The proofs do not show that the commitments match the blobs. -/
  | proofRejected

/--
The stable code of an error, for the C exports.

A transaction error keeps its own code, and the other codes start at 101.
-/
def NetworkError.code : NetworkError → UInt32
  | .transaction e => e.code
  | .wrongVersion _ => 101
  | .countMismatch .. => 102
  | .versionedHashMismatch .. => 103
  | .kzg _ => 104
  | .proofRejected => 105

namespace NetworkBlobTransaction

/-- The RLP list of the network form at `fork`, from Fusaka with the wrapper version. -/
def toItem (fork : Fork) (w : NetworkBlobTransaction) : Item :=
  -- EIP-7594, from Fusaka: five items, with the wrapper version after the payload body.
  --
  -- The cell proofs replace the proofs of EIP-4844: one per cell of each extended blob.
  if fork ≥ .fusaka then
    .list [Codec.toItem w.tx, Codec.toItem WRAPPER_VERSION, Codec.toItem w.blobs,
      Codec.toItem w.commitments, Codec.toItem w.proofs]
  -- EIP-4844, from Dencun: four items.
  --
  -- They are the payload body, the blobs, the commitments and the proofs.
  else
    .list [Codec.toItem w.tx, Codec.toItem w.blobs, Codec.toItem w.commitments,
      Codec.toItem w.proofs]

/-- The network form at `fork` in the RLP list `item`. -/
def ofItem (fork : Fork) (item : Item) : Except NetworkError NetworkBlobTransaction :=
  if fork ≥ .fusaka then
    match item with
    | .list [tx, v, b, c, p] => do
      let version ← (Codec.ofItem v : Except RlpError Nat).mapError (.transaction ∘ .decoding)
      -- EIP-7594 sets the wrapper version to 1, its only version, so any other version is rejected.
      if version ≠ WRAPPER_VERSION then throw (.wrongVersion version)
      (do return ⟨← Codec.ofItem tx, ← Codec.ofItem b, ← Codec.ofItem c, ← Codec.ofItem p⟩
        : Except RlpError _).mapError (.transaction ∘ .decoding)
    | .list items => .error (.transaction (.decoding (.wrongFieldCount 5 items.length)))
    | .bytes _ => .error (.transaction (.decoding .bytesAsList))
  else
    match item with
    | .list [tx, b, c, p] =>
      (do return ⟨← Codec.ofItem tx, ← Codec.ofItem b, ← Codec.ofItem c, ← Codec.ofItem p⟩
        : Except RlpError _).mapError (.transaction ∘ .decoding)
    | .list items => .error (.transaction (.decoding (.wrongFieldCount 4 items.length)))
    | .bytes _ => .error (.transaction (.decoding .bytesAsList))

end NetworkBlobTransaction

/--
The bytes of the network form at `fork`: the type 3, then the RLP list.

It fails only when an RLP payload has 2^64 bytes or more.
-/
def encodeNetwork (fork : Fork) (w : NetworkBlobTransaction) : Except RlpError ByteArray :=
  -- EIP-2718: the type byte `0x03`, then the payload that EIP-4844 wraps, the RLP of the list.
  typedBytes 3 <$> Serialization.Rlp.encode (w.toItem fork)

/--
The network form of a blob transaction that `bytes` encodes at `fork`.

It fails before Dencun, which has no blob transaction, and on any first byte but 3.
-/
def decodeNetwork (fork : Fork) (bytes : ByteArray) :
    Except NetworkError NetworkBlobTransaction :=
  match bytes.data.toList with
  | [] => .error (.transaction .emptyTransaction)
  | type :: payload =>
    -- Only the type `0x03` of EIP-4844 has a network form, from Dencun.
    if type = 3 ∧ fork ≥ .dencun then do
      let item ← (Serialization.Rlp.decode ⟨payload.toArray⟩).mapError (.transaction ∘ .decoding)
      NetworkBlobTransaction.ofItem fork item
    else .error (.transaction (.unsupportedType type))

/-- Whether each commitment hashes to the versioned hash at its position. -/
def hashesMatch (hashes : List VersionedHash) (commitments : List KZGCommitment) : Bool :=
  -- EIP-4844: the versioned hash at index `i` is the versioned hash of commitment `i`.
  --
  -- The pairs stop at the shorter list, and the counts are checked apart.
  (hashes.zip commitments).all fun (h, c) => decide (kzgCommitmentToVersionedHash c = h)

/-- The number of proofs at `fork` for `count` blobs: one per blob, or one per cell from Fusaka. -/
def proofCount (fork : Fork) (count : Nat) : Nat :=
  -- EIP-7594, from Fusaka: one proof per cell of each extended blob, so 128 per blob.
  --
  -- EIP-4844, before Fusaka: one proof per blob.
  if fork ≥ .fusaka then CELLS_PER_EXT_BLOB * count else count

/-- Whether the counts of versioned hashes, commitments and proofs match the count of blobs. -/
def blobCountsMatch (fork : Fork) (hashes : List VersionedHash) (blobs : List Blob)
    (commitments : List KZGCommitment) (proofs : List KZGProof) : Bool :=
  -- One blob and one commitment per versioned hash, and the proofs that the fork asks per blob.
  hashes.length == blobs.length && commitments.length == blobs.length &&
    proofs.length == proofCount fork blobs.length

/-- Whether the counts of the network form match the count of its blobs. -/
def countsMatch (fork : Fork) (w : NetworkBlobTransaction) : Bool :=
  blobCountsMatch fork w.tx.blobVersionedHashes w.blobs w.commitments w.proofs

/--
Whether the proofs show that the commitments match the blobs.

Before Fusaka, each blob has one proof, checked by the batch check of blobs.

From Fusaka, proof `128 i + j` is for cell `j` of the extended blob `i`.

The batch check of cells then runs on every cell of every extended blob.
-/
def verifyBlobBundle (setup : TrustedSetup) (fork : Fork) (blobs : List Blob)
    (commitments : List KZGCommitment) (proofs : List KZGProof) :
    Except KzgError Bool :=
  if fork ≥ .fusaka then do
    -- EIP-7594: the cells of each extended blob.
    let cells ← blobs.mapM computeCells
    -- EIP-7594: cell `j` of blob `i` takes commitment `i`, index `j` and proof `128 i + j`.
    --
    -- The batch check of cells verifies all of them at once.
    let indices := (List.range CELLS_PER_EXT_BLOB).toArray
    verifyCellKzgProofBatch setup
      (commitments.toArray.flatMap fun c => Array.replicate CELLS_PER_EXT_BLOB c.bytes)
      (Array.flatten (Array.replicate blobs.length indices))
      cells.toArray.flatten proofs.toArray
  -- EIP-4844: the batch check of blobs, one proof per blob.
  else
    verifyBlobKzgProofBatch setup blobs.toArray (commitments.toArray.map (·.bytes)) proofs.toArray

/-- Whether the network form's proofs show that its commitments match its blobs. -/
def proofsVerify (setup : TrustedSetup) (fork : Fork) (w : NetworkBlobTransaction) :
    Except KzgError Bool :=
  verifyBlobBundle setup fork w.blobs w.commitments w.proofs

/--
Check blobs, commitments and proofs at `fork` against the versioned hashes they answer.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.
-/
def validateBlobs (setup : TrustedSetup) (fork : Fork) (hashes : List VersionedHash)
    (blobs : List Blob) (commitments : List KZGCommitment) (proofs : List KZGProof) :
    Except NetworkError Unit := do
  -- EIP-4844 and EIP-7594: the counts of versioned hashes, blobs, commitments and proofs match.
  unless blobCountsMatch fork hashes blobs commitments proofs do
    throw (.countMismatch hashes.length blobs.length commitments.length proofs.length)
  -- Commitment `i` hashes to versioned hash `i`.
  unless hashesMatch hashes commitments do
    -- Some pair does not match, so the first such pair has an index below both lengths.
    let index := (hashes.zip commitments).findIdx fun (h, c) =>
      !decide (kzgCommitmentToVersionedHash c = h)
    let commitment := commitments.getD index ⟨Vector.replicate 48 0⟩
    throw (.versionedHashMismatch index (kzgCommitmentToVersionedHash commitment)
      (hashes.getD index ⟨0⟩))
  -- The commitments match the blobs and the proofs.
  unless ← (verifyBlobBundle setup fork blobs commitments proofs).mapError .kzg do
    throw .proofRejected

/--
Check the blobs of the network form of a blob transaction at `fork`, as EIP-4844 and EIP-7594 ask.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.

The checks of the transaction itself are separate.
-/
def validateNetwork (setup : TrustedSetup) (fork : Fork) (w : NetworkBlobTransaction) :
    Except NetworkError Unit :=
  validateBlobs setup fork w.tx.blobVersionedHashes w.blobs w.commitments w.proofs

end EthLib.Execution.Transactions
