module

public import EthLib.Consensus.SlashingProtection
public import EthLib.Base.Exports

/-!
# `Exports.SlashingProtection`

C-ABI exports of the slashing protection of a signer, as EIP-3076 specifies.

An interchange file comes as JSON text in UTF-8, and each export that returns one writes it again.

A public key is 48 bytes, and a signing root is 32 bytes.

Text that is not JSON in UTF-8, or a key or a root of another length, has code 0.

A file that does not read, and a message that a signer must refuse, have the code of their error.
-/

public section

namespace EthLib.Consensus.Exports

open Lean Base Cryptography.Bls
open EthLib.Exports (Result)

/-- The result of a step of slashing protection, with the code of its error. -/
def runProtection {α : Type} (result : Except SlashingProtectionError α) : Result α :=
  result.mapError fun e => (e.code, s!"slashing protection failed with code {e.code}")

/-- An interchange file from its JSON text. -/
def interchangeOf (text : ByteArray) : Result Interchange := do
  let some text := String.fromUTF8? text | throw (0, "the interchange is not UTF-8")
  let .ok document := Json.parse text | throw (0, "the interchange is not JSON")
  runProtection (Interchange.ofJson document)

/-- The JSON text of an interchange file. -/
def interchangeText (interchange : Interchange) : ByteArray :=
  interchange.toJson.compress.toUTF8

/-- Bytes of a fixed length, or code 0 with a message that names them. -/
def fixedBytesOf (what : String) (size : Nat) (bytes : ByteArray) : Result (Vector UInt8 size) :=
  if sized : bytes.size = size then return ⟨bytes.data, sized⟩
  else throw (0, s!"{what} is {size} bytes, not {bytes.size}")

/-- An interchange file as the format writes it again, from its JSON text. -/
@[export eth_consensus_read_slashing_interchange]
def readSlashingInterchangeExport (text : ByteArray) : Result ByteArray := do
  return interchangeText (← interchangeOf text)

/-- The record of a signer that keeps every message, after it imports a file, as JSON text. -/
@[export eth_consensus_import_slashing_interchange]
def importSlashingInterchangeExport (held file : ByteArray) : Result ByteArray := do
  return interchangeText ((← interchangeOf held).importFile (← interchangeOf file))

/-- Whether a key may sign a block of a slot with a signing root, given a record.

It returns true, or the code of the condition that the block breaks. -/
@[export eth_consensus_check_block_signing]
def checkBlockSigningExport (text pubkey : ByteArray) (slot : UInt64) (signingRoot : ByteArray) :
    Result Bool := do
  let interchange ← interchangeOf text
  let pubkey ← fixedBytesOf "the public key" 48 pubkey
  let signingRoot ← fixedBytesOf "the signing root" 32 signingRoot
  runProtection (interchange.checkBlock pubkey slot signingRoot)
  return true

/-- Whether a key may sign a vote of two epochs with a signing root, given a record.

It returns true, or the code of the condition that the vote breaks. -/
@[export eth_consensus_check_attestation_signing]
def checkAttestationSigningExport (text pubkey : ByteArray) (sourceEpoch targetEpoch : UInt64)
    (signingRoot : ByteArray) : Result Bool := do
  let interchange ← interchangeOf text
  let pubkey ← fixedBytesOf "the public key" 48 pubkey
  let signingRoot ← fixedBytesOf "the signing root" 32 signingRoot
  runProtection (interchange.checkAttestation pubkey sourceEpoch targetEpoch signingRoot)
  return true

/-- The record after a key signs a block, as JSON text. -/
@[export eth_consensus_record_block_signing]
def recordBlockSigningExport (text pubkey : ByteArray) (slot : UInt64) (signingRoot : ByteArray) :
    Result ByteArray := do
  let interchange ← interchangeOf text
  let pubkey ← fixedBytesOf "the public key" 48 pubkey
  let signingRoot ← fixedBytesOf "the signing root" 32 signingRoot
  return interchangeText (interchange.recordBlock pubkey slot signingRoot)

/-- The record after a key signs a vote, as JSON text. -/
@[export eth_consensus_record_attestation_signing]
def recordAttestationSigningExport (text pubkey : ByteArray) (sourceEpoch targetEpoch : UInt64)
    (signingRoot : ByteArray) : Result ByteArray := do
  let interchange ← interchangeOf text
  let pubkey ← fixedBytesOf "the public key" 48 pubkey
  let signingRoot ← fixedBytesOf "the signing root" 32 signingRoot
  return interchangeText
    (interchange.recordAttestation pubkey sourceEpoch targetEpoch signingRoot)

end EthLib.Consensus.Exports
