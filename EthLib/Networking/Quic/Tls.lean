module

public import EthLib.Cryptography.Hash.Tls13

/-!
# TLS 1.3 key schedule for SHA-256

[RFC 9846 §7.1][schedule] derives handshake and application traffic secrets from a shared secret.

This schedule uses no pre-shared key.

It stops at the first application traffic secrets; the exporter and resumption secrets are absent.

It also computes the Finished value of [RFC 9846 §4.5.3][finished].

Callers supply the transcript bytes of [RFC 9846 §4.1][transcript], including handshake headers.

After a HelloRetryRequest, the transcript starts with the `message_hash` message of §4.1.

That message, with its handshake header, takes the place of ClientHello1.

The functions do not parse messages, negotiate algorithms or authenticate a peer.

They accept a shared secret of any length and do not check it.

The caller encodes the shared secret as [§7.4][dh] specifies.

The caller also rejects an all-zero X25519 output and invalid group elements, as §7.4 requires.

[schedule]: https://www.rfc-editor.org/rfc/rfc9846#section-7.1
[finished]: https://www.rfc-editor.org/rfc/rfc9846#section-4.5.3
[transcript]: https://www.rfc-editor.org/rfc/rfc9846#section-4.1
[dh]: https://www.rfc-editor.org/rfc/rfc9846#section-7.4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open EthLib.Base
open EthLib.Cryptography.Hash
open Tls13 (Secret)

/-- The string of `Hash.length` zero bytes, 32 for SHA-256, of RFC 9846 §7.1. -/
def zeros : Secret := Vector.replicate 32 0

/-- Derive-Secret of RFC 9846 §7.1, with SHA-256 over the encoded handshake messages.

The label excludes the `tls13 ` prefix, which the labelled expansion adds.

The empty message argument hashes to SHA-256 of the empty string, rather than an empty context. -/
def deriveSecret (secret : Secret) (label messages : ByteArray) : Except Tls13.Error Secret :=
  -- §7.1: `HKDF-Expand-Label(Secret, Label, Transcript-Hash(Messages), Hash.length)`.
  --
  -- `Transcript-Hash(Messages)` is the SHA-256 hash of the messages (§4.1), of 32 bytes.
  Tls13.expandLabel secret label (packBytes (Sha256.hash32 messages)) 32

/-- The early secret without a pre-shared key, RFC 9846 §7.1. -/
def earlySecret : Secret :=
  -- §7.1: if PSK is not in use, `Early Secret = HKDF-Extract(0, 0)`.
  --
  -- The salt `0` is the 0-value, and the PSK, which is not available, is the 0-value too.
  Tls13.extract (packBytes zeros) (packBytes zeros)

/-- Mix the shared secret into the early secret, RFC 9846 §7.1. -/
def handshakeSecret (sharedSecret : ByteArray) : Except Tls13.Error Secret := do
  -- `Derive-Secret(., "derived", "")`, from the Early Secret.
  let derived ← deriveSecret earlySecret "derived".toUTF8 .empty
  -- `asymmetric shared secret -> HKDF-Extract = Handshake Secret`: the salt is the derived secret.
  return Tls13.extract (packBytes derived) sharedSecret

/-- Derive the Main Secret from the Handshake Secret, RFC 9846 §7.1.

RFC 8446 named it the Master Secret. -/
def masterSecret (handshake : Secret) : Except Tls13.Error Secret := do
  -- `Derive-Secret(., "derived", "")`, from the Handshake Secret.
  let derived ← deriveSecret handshake "derived".toUTF8 .empty
  -- `0 -> HKDF-Extract = Main Secret`: the salt is the derived secret, the input the 0-value.
  return Tls13.extract (packBytes derived) (packBytes zeros)

/-- The secrets through the first application traffic generation, RFC 9846 §7.1. -/
structure KeySchedule where
  /-- `early_secret`. -/
  early : Secret
  /-- `handshake_secret`. -/
  handshake : Secret
  /-- The Main Secret, the Master Secret of RFC 8446. -/
  master : Secret
  /-- `client_handshake_traffic_secret`. -/
  clientHandshake : Secret
  /-- `server_handshake_traffic_secret`. -/
  serverHandshake : Secret
  /-- `client_application_traffic_secret_0`. -/
  clientApplication : Secret
  /-- `server_application_traffic_secret_0`. -/
  serverApplication : Secret
  deriving DecidableEq

/-- Compute the no-PSK handshake and first application traffic secrets of RFC 9846 §7.1.

The first transcript runs from ClientHello through ServerHello.

The second runs from ClientHello through the server's Finished message.

The function does not check that the second transcript extends the first.

Each transcript includes handshake headers and excludes record headers, as §4.1 requires. -/
def keySchedule (sharedSecret helloTranscript serverTranscript : ByteArray) :
    Except Tls13.Error KeySchedule := do
  -- The left side of the §7.1 diagram: the Handshake Secret, from the asymmetric shared secret.
  let handshake ← handshakeSecret sharedSecret
  -- Then the Main Secret, from the Handshake Secret.
  let master ← masterSecret handshake
  -- `Derive-Secret(., "c hs traffic", ClientHello...ServerHello)`, from the Handshake Secret.
  let clientHandshake ← deriveSecret handshake "c hs traffic".toUTF8 helloTranscript
  -- `Derive-Secret(., "s hs traffic", ClientHello...ServerHello)`, from the Handshake Secret.
  let serverHandshake ← deriveSecret handshake "s hs traffic".toUTF8 helloTranscript
  -- `Derive-Secret(., "c ap traffic", ClientHello...server Finished)`, from the Main Secret.
  let clientApplication ← deriveSecret master "c ap traffic".toUTF8 serverTranscript
  -- `Derive-Secret(., "s ap traffic", ClientHello...server Finished)`, from the Main Secret.
  let serverApplication ← deriveSecret master "s ap traffic".toUTF8 serverTranscript
  -- Not derived: the binder key, the client early traffic secret and the early exporter secret.
  --
  -- They need a PSK.
  --
  -- Not derived either: the exporter and resumption secrets.
  return ⟨earlySecret, handshake, master, clientHandshake, serverHandshake,
    clientApplication, serverApplication⟩

/-- The Finished `verify_data` of RFC 9846 §4.5.3.

During the handshake the secret is the sender's handshake traffic secret, the base key of §4.5.

The transcript ends before the Finished message being computed.

Comparing a received value with this one is left to the caller. -/
def finished (trafficSecret : Secret) (transcript : ByteArray) : Except Tls13.Error Secret := do
  -- `finished_key = HKDF-Expand-Label(BaseKey, "finished", "", Hash.length)`, with 32 bytes.
  let key ← Tls13.expandLabel trafficSecret "finished".toUTF8 .empty 32
  -- `verify_data = HMAC(finished_key, Transcript-Hash(...))`, with HMAC-SHA-256.
  --
  -- The transcript is the Handshake Context, then Certificate and CertificateVerify if present.
  return Hmac.hmac32 (packBytes key) (packBytes (Sha256.hash32 transcript))

end EthLib.Networking.Quic.Tls
