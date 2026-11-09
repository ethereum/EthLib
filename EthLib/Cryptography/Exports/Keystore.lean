module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Keystore

/-!
# Exports: ERC-2335 keystores and Unicode NFKD

JSON text is parsed at this boundary, outside the specification's decoder of JSON values.

The exports return the code and message of the step that failed.
-/

public section

namespace EthLib.Cryptography.Keystore.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- Unicode 16.0.0 Normalization Form KD, UAX #15 rev. 56, §1.3. -/
@[export eth_keystore_nfkd]
def nfkd (args : PyValue) : Result PyValue :=
  pyExport (fun text : String => pure (Base.Unicode.nfkd text)) args

/-- NFKD, control removal and UTF-8 encoding, ERC-2335 "Password requirements". -/
@[export eth_keystore_password]
def password (args : PyValue) : Result PyValue :=
  pyExport (fun text : String => pure (passwordBytes text)) args

/-- Read JSON text at the boundary, then run the specified keystore decryption. -/
def decryptOf (args : String × String) : Result ByteArray := do
  let (text, password) := args
  let value ← (Lean.Json.parse text).mapError fun reason =>
    let error := KeystoreError.invalidJson reason
    (error.code, s!"{repr error}")
  (Keystore.decrypt value password).mapError fun error => (error.code, s!"{repr error}")

/-- Decrypt an ERC-2335 JSON keystore and return its secret octets. -/
@[export eth_keystore_decrypt]
def decrypt (args : PyValue) : Result PyValue := pyExport decryptOf args

end EthLib.Cryptography.Keystore.Exports
