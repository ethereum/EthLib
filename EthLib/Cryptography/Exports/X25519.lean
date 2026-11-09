module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.X25519

/-!
# Exports: X25519

The typed adapters reject wrong byte lengths before any scalar multiplication.
-/

public section

namespace EthLib.Cryptography.X25519.Exports

open EthLib.Exports (Result PyValue pyExport)

/-- The X25519 key and coordinate length in bytes, RFC 7748 §5. -/
@[export eth_x25519_const_key_size]
def x25519KeySize (_ : Unit) : UInt64 := 32

/-- X25519 scalar multiplication of two 32-byte inputs, RFC 7748 §5. -/
@[export eth_x25519]
def x25519Export (args : PyValue) : Result PyValue :=
  pyExport (fun (scalar, u) => pure (x25519 scalar u)) args

/-- X25519 public key at Montgomery coordinate 9, RFC 7748 §6.1. -/
@[export eth_x25519_public_key]
def x25519PublicKeyExport (args : PyValue) : Result PyValue :=
  pyExport (fun scalar => pure (publicKey scalar)) args

end EthLib.Cryptography.X25519.Exports
