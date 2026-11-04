module

public import EthLib.Networking.Discv5.Identity

/-!
# `Exports.Discv5`

C-ABI exports of the Node Discovery Protocol v5, for the Python bindings.

A private key crosses the boundary as 32 big-endian bytes, and a public key in a SEC 1 encoding.

A node ID is 32 bytes, and a rejected input becomes an error.
-/

public section

namespace EthLib.Networking.Discv5.Exports

open EthLib.Cryptography.Secp256k1

/-- A node ID of 32 bytes. -/
def nodeIdOf (bytes : ByteArray) : IO NodeId :=
  if h : bytes.size = 32 then pure ⟨bytes.data, h⟩
  else throw (IO.userError s!"node ID has {bytes.size} bytes, not 32")

/-- A private key of 32 big-endian bytes, below the group order. -/
def privateKeyOf (bytes : ByteArray) : IO Fn :=
  let k := ofBytesBE bytes.data.toList
  if bytes.size = 32 ∧ k < Fn.modulus then pure (Fin.ofNat _ k)
  else throw (IO.userError "private key is not 32 bytes below the group order")

/-- A public key in a SEC 1 encoding. -/
def publicKeyOf (bytes : ByteArray) : IO Point :=
  match Point.decode bytes with
  | .ok p => pure p
  | .error _ => throw (IO.userError "public key is not a point of secp256k1")

/-- The logarithmic distance between two node IDs. -/
@[export eth_discv5_log_distance]
def logDistanceExport (a b : ByteArray) : IO UInt64 := do
  return (logDistance (← nodeIdOf a) (← nodeIdOf b)).toUInt64

/-- The 33-byte shared secret of a private key and a public key. -/
@[export eth_discv5_ecdh]
def ecdhExport (sk pk : ByteArray) : IO ByteArray := do
  match ecdh (← privateKeyOf sk) (← publicKeyOf pk) with
  | .ok secret => pure secret
  | .error _ => throw (IO.userError "no shared secret")

/-- The session keys, as the 16 bytes of the initiator key, then the 16 of the recipient key.

The secret is the ECDH of the ephemeral private key and the public key of node B. -/
@[export eth_discv5_derive_keys]
def deriveKeysExport (ephemeralKey destPubkey nodeIdA nodeIdB challengeData : ByteArray) :
    IO ByteArray := do
  let some secret := (ecdh (← privateKeyOf ephemeralKey) (← publicKeyOf destPubkey)).toOption
    | throw (IO.userError "no shared secret")
  match deriveKeys secret challengeData (← nodeIdOf nodeIdA) (← nodeIdOf nodeIdB) with
  | .ok keys => pure (keys.initiatorKey ++ keys.recipientKey)
  | .error _ => throw (IO.userError "key derivation failed")

/-- The 64-byte ID signature of node A. -/
@[export eth_discv5_id_sign]
def idSignExport (staticKey challengeData ephemeralPubkey nodeIdB : ByteArray) :
    IO ByteArray := do
  match idSign (← privateKeyOf staticKey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB) with
  | .ok signature => pure signature
  | .error _ => throw (IO.userError "signing failed")

/-- Whether an ID signature verifies under the public key of node A. -/
@[export eth_discv5_id_verify]
def idVerifyExport (pubkey challengeData ephemeralPubkey nodeIdB signature : ByteArray) :
    IO UInt8 := do
  let ok := idVerify (← publicKeyOf pubkey) challengeData ephemeralPubkey (← nodeIdOf nodeIdB)
    signature
  return if ok then 1 else 0

end EthLib.Networking.Discv5.Exports
