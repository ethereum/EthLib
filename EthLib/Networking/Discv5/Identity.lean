module

public import EthLib.Cryptography.Hash.Hkdf
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Networking.Discv5.Distance

/-!
# `Networking.Discv5.Identity`

The cryptography of the discv5 handshake for the "v4" identity scheme.

The source is `discv5-theory.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/88f1c80800d6/discv5/discv5-theory.md>

Its sections are "Identity-Specific Cryptography in the Handshake", and "Step 3" of the handshake.

- The shared secret is the point `d Q` of an ECDH, in its 33-byte compressed form.
- HKDF over SHA-256 turns the secret into two 16-byte session keys.
- The ID signature is an ECDSA signature of a SHA-256 hash, written as the 64 bytes `r || s`.

The private keys are secret, and these functions make no constant-time claim.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Hash

/-- The ASCII bytes of a string. -/
def asciiBytes (s : String) : ByteArray := s.toUTF8

/-- The shared secret of a private key and a public key: `d Q`, compressed to 33 bytes.

The first byte is `02` when the `y` of `d Q` is even and `03` when it is odd, then `x` follows.

The public key must be a point of the curve other than `O`, as for the ECDH of SEC 1 v2. -/
def ecdh (sk : Fn) (pk : Point) : Except Secp256k1Error ByteArray :=
  if pk = .infinity then .error .pointAtInfinity
  else if !pk.isOnCurve then .error .notOnCurve
  else
    match Point.mul sk pk with
    | .infinity => .error .pointAtInfinity
    | p => .ok p.encodeCompressed

/-- The session keys of a handshake: the first and the last 16 bytes of the HKDF output. -/
structure SessionKeys where
  /-- The key of the node that starts the handshake. -/
  initiatorKey : ByteArray
  /-- The key of the node that answers it. -/
  recipientKey : ByteArray
  deriving DecidableEq

/-- The session keys from the shared secret and the challenge that the recipient sent.

The salt is the challenge data, and the info is the text, then the IDs of the two nodes.

The initiator is node A, and the recipient is node B, which sent the challenge. -/
def deriveKeys (secret challengeData : ByteArray) (nodeIdA nodeIdB : NodeId) :
    Except Hkdf.HkdfError SessionKeys := do
  let info := asciiBytes "discovery v5 key agreement" ++ ⟨nodeIdA.toArray⟩ ++ ⟨nodeIdB.toArray⟩
  let keyData ← Hkdf.hkdf challengeData secret info 32
  return ⟨keyData.extract 0 16, keyData.extract 16 32⟩

/-- The hash that an ID signature signs.

It is the SHA-256 of the text, the challenge data, the ephemeral public key and the ID of node B.

SHA-256 gives 32 bytes, so the vector holds the whole hash. -/
def idSignatureHash (challengeData ephemeralPubkey : ByteArray) (nodeIdB : NodeId) :
    Vector UInt8 32 :=
  let hash := Sha256.hash (asciiBytes "discovery v5 identity proof" ++ challengeData ++
    ephemeralPubkey ++ ⟨nodeIdB.toArray⟩)
  Vector.ofFn fun i => hash.data[i.val]?.getD 0

/-- The ID signature of node A: the 64 bytes `r || s` of an ECDSA signature of the hash.

The signature is deterministic, with the nonces of RFC 6979, and its `s` is at most `n / 2`. -/
def idSign (sk : Fn) (challengeData ephemeralPubkey : ByteArray) (nodeIdB : NodeId) :
    Except Secp256k1Error ByteArray := do
  let (r, s, _) ← Ecdsa.sign sk (idSignatureHash challengeData ephemeralPubkey nodeIdB)
  return ⟨(toBytesBE 32 r.val ++ toBytesBE 32 s.val).toArray⟩

/-- Whether an ID signature of 64 bytes `r || s` verifies under the public key of node A. -/
def idVerify (pk : Point) (challengeData ephemeralPubkey : ByteArray) (nodeIdB : NodeId)
    (signature : ByteArray) : Bool :=
  signature.size == 64 &&
    Ecdsa.verify pk (idSignatureHash challengeData ephemeralPubkey nodeIdB)
      (ofBytesBE (signature.data.toList.take 32)) (ofBytesBE (signature.data.toList.drop 32))

end EthLib.Networking.Discv5
