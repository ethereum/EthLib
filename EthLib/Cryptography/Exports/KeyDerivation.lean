module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Bls.KeyDerivation
public import EthLib.Cryptography.Bls.KeyPath

/-!
# Exports: validator key derivation

ERC-2333 keys cross the boundary as 32 big-endian bytes, as BLS secret keys do.

ERC-2334 paths cross as strings, and child indices as checked 32-bit integers.
-/

public section

namespace EthLib.Cryptography.Bls.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The derivation or path error, with its detailed reason. -/
inductive KeyDerivationError where
  | bls (error : BlsError)
  | path (error : KeyPath.KeyPathError)

/-- Stable codes for the two kinds of failure. -/
def KeyDerivationError.code : KeyDerivationError → UInt32
  | .bls _ => 1
  | .path _ => 2

/-- The detailed message of the failing step. -/
def KeyDerivationError.message : KeyDerivationError → String
  | .bls error => error.message
  | .path error => error.message

/-- Pass the error kind and its message to Python. -/
def runKeyDerivation {α : Type} (act : Except KeyDerivationError α) : Result α :=
  act.mapError fun error => (error.code, error.message)

/-- Derive and encode the master key. -/
def deriveMasterSkBytes (seed : ByteArray) : Result ByteArray := runKeyDerivation do
  let key ← (KeyDerivation.deriveMasterSk seed).mapError KeyDerivationError.bls
  return Fr.toBytesBE key.val

/-- The ERC-2333 master secret key, as 32 big-endian bytes. -/
@[export eth_bls_derive_master_sk]
def deriveMasterSkExport (args : PyValue) : Result PyValue :=
  pyExport deriveMasterSkBytes args

/-- Read the parent key, derive its child and encode the result. -/
def deriveChildSkBytes (args : ByteArray × UInt32) : Result ByteArray := runKeyDerivation do
  let (parent, index) := args
  let parent ← (Signatures.SecretKey.fromBytes parent).mapError KeyDerivationError.bls
  let key ← (KeyDerivation.deriveChildSk parent index).mapError KeyDerivationError.bls
  return Fr.toBytesBE key.val

/-- The ERC-2333 child of a secret key at an index, as 32 big-endian bytes. -/
@[export eth_bls_derive_child_sk]
def deriveChildSkExport (args : PyValue) : Result PyValue :=
  pyExport deriveChildSkBytes args

/-- Parse an ERC-2334 path, derive the key it names and encode the result. -/
def derivePathBytes (args : ByteArray × String) : Result ByteArray := runKeyDerivation do
  let (seed, path) := args
  let path ← (KeyPath.parsePath path).mapError KeyDerivationError.path
  let key ← (KeyDerivation.derivePath seed path.indices).mapError KeyDerivationError.bls
  return Fr.toBytesBE key.val

/-- The key at an ERC-2334 path from a seed, as 32 big-endian bytes. -/
@[export eth_bls_derive_path]
def derivePathExport (args : PyValue) : Result PyValue :=
  pyExport derivePathBytes args

/-- The ERC-2334 withdrawal path `m/12381/3600/index/0`. -/
@[export eth_bls_withdrawal_path]
def withdrawalPathExport (args : PyValue) : Result PyValue :=
  pyExport (fun index : UInt32 => pure (KeyPath.withdrawalPath index).toString) args

/-- The ERC-2334 signing path `m/12381/3600/index/0/0`. -/
@[export eth_bls_signing_path]
def signingPathExport (args : PyValue) : Result PyValue :=
  pyExport (fun index : UInt32 => pure (KeyPath.signingPath index).toString) args

end EthLib.Cryptography.Bls.Exports
