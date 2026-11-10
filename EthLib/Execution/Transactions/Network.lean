module

public import EthLib.Cryptography.Kzg.Cells
public import EthLib.Cryptography.Kzg.VersionedHash
public import EthLib.Execution.Transactions.Validity

/-!
# `Transactions.Network`

The network form of a blob transaction, which peers send in answer to a request for it.

From Dencun, it is `0x03 || rlp([tx_payload_body, blobs, commitments, proofs])`.

It has one proof per blob, by [EIP-4844](https://eips.ethereum.org/EIPS/eip-4844#networking).

From Fusaka, it is `0x03 || rlp([tx_payload_body, wrapper_version, blobs, commitments, proofs])`.

The version is 1, by [EIP-7594](https://eips.ethereum.org/EIPS/eip-7594#networking).

It has one proof per cell of each extended blob.

A block holds only `tx_payload_body`, so the hash of the transaction ignores the rest.
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Serialization.Rlp

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
  /-- A commitment does not hash to the versioned hash at its position. -/
  | versionedHashMismatch
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
  | .versionedHashMismatch => 103
  | .kzg _ => 104
  | .proofRejected => 105

namespace NetworkBlobTransaction

/-- The RLP list of the network form at `fork`, from Fusaka with the wrapper version. -/
def toItem (fork : Fork) (w : NetworkBlobTransaction) : Item :=
  if fork ≥ .fusaka then
    .list [Codec.toItem w.tx, Codec.toItem WRAPPER_VERSION, Codec.toItem w.blobs,
      Codec.toItem w.commitments, Codec.toItem w.proofs]
  else
    .list [Codec.toItem w.tx, Codec.toItem w.blobs, Codec.toItem w.commitments,
      Codec.toItem w.proofs]

/-- The network form at `fork` in the RLP list `item`. -/
def ofItem (fork : Fork) (item : Item) : Except NetworkError NetworkBlobTransaction :=
  if fork ≥ .fusaka then
    match item with
    | .list [tx, v, b, c, p] => do
      let version ← (Codec.ofItem v : Except RlpError Nat).mapError (.transaction ∘ .decoding)
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
    if type = 3 ∧ fork ≥ .dencun then do
      let item ← (Serialization.Rlp.decode ⟨payload.toArray⟩).mapError (.transaction ∘ .decoding)
      NetworkBlobTransaction.ofItem fork item
    else .error (.transaction (.unsupportedType type))

/-- The versioned hash of a commitment: `0x01`, then the last 31 bytes of its SHA-256 hash. -/
def versionedHash (commitment : KZGCommitment) : Bytes32 :=
  Cryptography.Kzg.kzgCommitmentToVersionedHash ⟨commitment.toArray⟩

/-- Whether each commitment hashes to the versioned hash at its position. -/
def hashesMatch (hashes : List Bytes32) (commitments : List KZGCommitment) : Bool :=
  (hashes.zip commitments).all fun (h, c) => decide (versionedHash c = h)

/-- The number of proofs at `fork` for `count` blobs: one per blob, or one per cell from Fusaka. -/
def proofCount (fork : Fork) (count : Nat) : Nat :=
  if fork ≥ .fusaka then CELLS_PER_EXT_BLOB * count else count

/-- Whether the counts of versioned hashes, commitments and proofs match the count of blobs. -/
def blobCountsMatch (fork : Fork) (hashes : List Bytes32) (blobs : List Blob)
    (commitments : List KZGCommitment) (proofs : List KZGProof) : Bool :=
  hashes.length == blobs.length && commitments.length == blobs.length &&
    proofs.length == proofCount fork blobs.length

/-- Whether the counts of the network form match the count of its blobs. -/
def countsMatch (fork : Fork) (w : NetworkBlobTransaction) : Bool :=
  blobCountsMatch fork w.tx.blobVersionedHashes w.blobs w.commitments w.proofs

/--
Whether the proofs show that the commitments match the blobs.

Before Fusaka, each blob has one proof, checked by the batch check of blobs.

From Fusaka, proof `i * CELLS_PER_EXT_BLOB + j` is for cell `j` of the extended blob `i`.

The batch check of cells then runs on every cell of every extended blob.
-/
def verifyBlobBundle (setup : TrustedSetup) (fork : Fork) (blobs : List Blob)
    (commitments : List KZGCommitment) (proofs : List KZGProof) :
    Except KzgError Bool :=
  if fork ≥ .fusaka then do
    let cells ← blobs.mapM computeCells
    let indices := (List.range CELLS_PER_EXT_BLOB).toArray
    verifyCellKzgProofBatch setup
      (commitments.toArray.flatMap fun c => Array.replicate CELLS_PER_EXT_BLOB c)
      (Array.flatten (Array.replicate blobs.length indices))
      cells.toArray.flatten proofs.toArray
  else verifyBlobKzgProofBatch setup blobs.toArray commitments.toArray proofs.toArray

/-- Whether the network form's proofs show that its commitments match its blobs. -/
def proofsVerify (setup : TrustedSetup) (fork : Fork) (w : NetworkBlobTransaction) :
    Except KzgError Bool :=
  verifyBlobBundle setup fork w.blobs w.commitments w.proofs

/--
Check blobs, commitments and proofs at `fork` against the versioned hashes they answer.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.
-/
def validateBlobs (setup : TrustedSetup) (fork : Fork) (hashes : List Bytes32) (blobs : List Blob)
    (commitments : List KZGCommitment) (proofs : List KZGProof) : Except NetworkError Unit := do
  unless blobCountsMatch fork hashes blobs commitments proofs do
    throw (.countMismatch hashes.length blobs.length commitments.length proofs.length)
  unless hashesMatch hashes commitments do throw .versionedHashMismatch
  unless ← (verifyBlobBundle setup fork blobs commitments proofs).mapError .kzg do
    throw .proofRejected

/--
Check the blobs of the network form of a blob transaction at `fork`, as its "Networking" asks.

The counts match, each commitment hashes to its versioned hash, and the proofs verify.

The checks of the transaction itself are separate.
-/
def validateNetwork (setup : TrustedSetup) (fork : Fork) (w : NetworkBlobTransaction) :
    Except NetworkError Unit :=
  validateBlobs setup fork w.tx.blobVersionedHashes w.blobs w.commitments w.proofs

end EthLib.Execution.Transactions
