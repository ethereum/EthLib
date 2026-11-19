module

public import EthLib.Cryptography.Hash.Tls13

/-!
# QUIC v1 packet keys

[RFC 9001 §5.2][initial] derives Initial secrets from the client's first Destination Connection ID.

[RFC 9001 §5.1][keys] derives a payload key, an IV and a header-protection key from each secret.

This module derives the keys for AES-128-GCM and ChaCha20-Poly1305 with SHA-256.

Anyone who sees the connection ID can compute the Initial secrets, RFC 9001 §5.2.

The other traffic secrets are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

[initial]: https://www.rfc-editor.org/rfc/rfc9001#section-5.2
[keys]: https://www.rfc-editor.org/rfc/rfc9001#section-5.1
-/

@[expose] public section

namespace EthLib.Networking.Quic

open EthLib.Base EthLib.Cryptography.Hash

/-- The salt of QUIC version 1, RFC 9001 §5.2.

RFC 9001 §5.2 asks later QUIC versions to use their own salts. -/
def INITIAL_SALT : Vector UInt8 20 :=
  #v[0x38, 0x76, 0x2c, 0xf7, 0xf5, 0x59, 0x34, 0xb3, 0x4d, 0x17,
    0x9a, 0xe6, 0xa4, 0xc8, 0x0c, 0xad, 0xcc, 0xbb, 0x7f, 0x0a]

/-- Client and server Initial traffic secrets, in that order, RFC 9001 §5.2.

The connection ID is the one in the client's first Initial packet.

After a Retry, it is the connection ID that the server chose, RFC 9001 §5.2. -/
def initialSecrets (dcid : ByteArray) : Except Tls13.Error (Tls13.Secret × Tls13.Secret) := do
  let initial := Tls13.extract (packBytes INITIAL_SALT) dcid
  let client ← Tls13.expandLabel initial "client in".toUTF8 .empty 32
  let server ← Tls13.expandLabel initial "server in".toUTF8 .empty 32
  return (client, server)

/-- The two SHA-256 cipher suites of RFC 9001 §5.3 that this derivation covers. -/
inductive CipherSuite where
  | aes128GcmSha256
  | chacha20Poly1305Sha256
  deriving DecidableEq, Repr

/-- The AEAD and header-protection key length, RFC 9001 §5.1, §5.4.3 and §5.4.4. -/
def CipherSuite.keyLength : CipherSuite → Nat
  | .aes128GcmSha256 => 16
  | .chacha20Poly1305Sha256 => 32

/-- The three keys of one sending direction, with the sizes that RFC 9001 §5.1 requires. -/
structure PacketKeys (suite : CipherSuite) where
  /-- The AEAD key for the payload. -/
  key : Vector UInt8 suite.keyLength
  /-- The initialization vector used to form packet nonces. -/
  iv : Vector UInt8 12
  /-- The header-protection key. -/
  hp : Vector UInt8 suite.keyLength
  deriving DecidableEq

/-- Derive the payload key, IV and header-protection key, RFC 9001 §5.1.

All three expansions use an empty context, and their labels separate the keys.

The traffic secret is secret, and this function makes no constant-time claim. -/
def packetKeys (suite : CipherSuite) (secret : Tls13.Secret) :
    Except Tls13.Error (PacketKeys suite) := do
  let key ← Tls13.expandLabel secret "quic key".toUTF8 .empty suite.keyLength
  let iv ← Tls13.expandLabel secret "quic iv".toUTF8 .empty 12
  let hp ← Tls13.expandLabel secret "quic hp".toUTF8 .empty suite.keyLength
  return ⟨key, iv, hp⟩

end EthLib.Networking.Quic
