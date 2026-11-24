module

public import EthLib.Cryptography.Hash.Hkdf
public import EthLib.Cryptography.Hash.Sha256
public import EthLib.Cryptography.Secp256k1.Ecdsa
public import EthLib.Cryptography.Secp256k1.Sign
public import EthLib.Cryptography.Ecdsa.Encoding
public import EthLib.Networking.Discv5.Distance

/-!
# `Networking.Discv5.Identity`

The cryptography of the discv5 handshake for the identity scheme v4.

The source is `discv5-theory.md` in `ethereum/devp2p`:
<https://github.com/ethereum/devp2p/blob/277ceb399c15df86efb17d51eb58200c26879784/discv5/discv5-theory.md>

Its sections are Identity-Specific Cryptography in the Handshake, and Steps 3 and 4 of it.

The private keys are secret, and these functions make no constant-time claim.
-/

@[expose] public section

namespace EthLib.Networking.Discv5

open EthLib.Cryptography.Secp256k1
open EthLib.Cryptography.Hash

/-- The ASCII bytes of a string. -/
def asciiBytes (s : String) : ByteArray := s.toUTF8

/-- The shared secret of a private key and a public key: `d Q`, compressed to 33 bytes.

The public key must be a point of the curve other than `O`, as for the ECDH of SEC 1 v2. -/
def ecdh (sk : Fn) (pk : Point) : Except Secp256k1Error ByteArray :=
  -- Not in the source: SEC 1 v2 §3.3.1 asks for a valid key, on the curve and not `O`.
  if pk = .infinity then .error .pointAtInfinity
  else if !pk.isOnCurve then .error .notOnCurve
  else
    -- `eph = pubkey * privkey`.
    match Point.mul sk pk with
    -- Not in the source: `eph = O` has no `x`, so it is an error, as in SEC 1 v2 §3.3.1 step 2.
    | .infinity => .error .pointAtInfinity
    -- The 33-byte secret is `y || eph.x`, with `y = 0x02` for an even `eph.y` and `0x03` otherwise.
    | p => .ok p.encodeCompressed

/-- The session keys of a handshake: the first and the last 16 bytes of the HKDF output.

HKDF over SHA-256 turns the shared secret into these two keys. -/
structure SessionKeys where
  /-- The key of the node that starts the handshake. -/
  initiatorKey : ByteArray
  /-- The key of the node that answers it. -/
  recipientKey : ByteArray
  deriving DecidableEq

/-- The session keys from the shared secret and the challenge that the recipient sent.

The initiator is node A, and the recipient is node B, which sent the challenge. -/
def deriveKeys (secret challengeData : ByteArray) (nodeIdA nodeIdB : NodeId) :
    Except Hkdf.HkdfError SessionKeys := do
  -- `kdf-info = "discovery v5 key agreement" || node-id-A || node-id-B`.
  let info := asciiBytes "discovery v5 key agreement" ++ ⟨nodeIdA.toArray⟩ ++ ⟨nodeIdB.toArray⟩
  -- `prk = HKDF-Extract(challenge-data, secret)`, then `key-data = HKDF-Expand(prk, kdf-info)`.
  --
  -- RFC 5869 with HMAC-SHA-256, and 32 bytes of output.
  let keyData ← Hkdf.hkdf challengeData secret info 32
  -- `initiator-key = key-data[:16]` and `recipient-key = key-data[16:]`.
  return ⟨keyData.extract 0 16, keyData.extract 16 32⟩

/-- The hash that an ID signature signs.

SHA-256 gives 32 bytes, so the vector holds the whole hash. -/
def idSignatureHash (challengeData ephemeralPubkey : ByteArray) (nodeIdB : NodeId) :
    Vector UInt8 32 :=
  -- `id-signature-text = "discovery v5 identity proof"`.
  --
  -- `id-signature-input = id-signature-text || challenge-data || ephemeral-pubkey || node-id-B`.
  --
  -- The hash is `sha256(id-signature-input)`.
  Sha256.hash32 (asciiBytes "discovery v5 identity proof" ++ challengeData ++
    ephemeralPubkey ++ ⟨nodeIdB.toArray⟩)

/-- The ID signature of node A: the 64 bytes `r || s` of an ECDSA signature of the SHA-256 hash.

The signature is deterministic, with the nonces of RFC 6979, and its `s` is at most `n / 2`. -/
def idSign (sk : Fn) (challengeData ephemeralPubkey : ByteArray) (nodeIdB : NodeId) :
    Except Secp256k1Error ByteArray := do
  -- `id-signature` signs `sha256(id-signature-input)` with the static private key of node A.
  --
  -- The source fixes neither the nonce nor `s`: EthLib takes RFC 6979 nonces and `s ≤ n / 2`.
  let (r, s, _) ← Ecdsa.sign sk (idSignatureHash challengeData ephemeralPubkey nodeIdB)
  -- The signature is encoded as the 64-byte array `r || s`.
  return Base.packBytes (Cryptography.Ecdsa.toBytes r.val s.val)

/-- Whether an ID signature of 64 bytes `r || s` verifies under the public key of node A. -/
def idVerify (pk : Point) (challengeData ephemeralPubkey : ByteArray) (nodeIdB : NodeId)
    (signature : ByteArray) : Bool :=
  -- Step 4: node B verifies `id-signature` against the identity public key of the record of A.
  --
  -- The signature is the 64-byte array `r || s`; any other length fails.
  match Cryptography.Ecdsa.read? signature with
  -- ECDSA verification of SEC 1 v2 on `sha256(id-signature-input)`; the source sets no low-s rule.
  | some (r, s) => Ecdsa.verify pk (idSignatureHash challengeData ephemeralPubkey nodeIdB) r s
  | none => false

end EthLib.Networking.Discv5
