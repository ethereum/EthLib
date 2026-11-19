module

public import EthLib.Cryptography.Hash.Tls13

/-!
# TLS 1.3 key schedule for SHA-256

[RFC 8446 §7.1][schedule] derives handshake and application traffic secrets from a shared secret.

This schedule uses no pre-shared key.

It stops at the first application traffic secrets; the exporter and resumption secrets are absent.

It also computes the Finished value of [RFC 8446 §4.4.4][finished].

Callers supply the transcript bytes of [RFC 8446 §4.4.1][transcript], including handshake headers.

After a HelloRetryRequest, the transcript starts with the `message_hash` message of §4.4.1.

That message, with its handshake header, takes the place of ClientHello1.

The functions do not parse messages, negotiate algorithms or authenticate a peer.

They accept a shared secret of any length and do not check it.

The caller encodes the shared secret as [§7.4][dh] specifies.

The caller also rejects an all-zero X25519 output and invalid group elements, as §7.4 requires.

[schedule]: https://www.rfc-editor.org/rfc/rfc8446#section-7.1
[finished]: https://www.rfc-editor.org/rfc/rfc8446#section-4.4.4
[transcript]: https://www.rfc-editor.org/rfc/rfc8446#section-4.4.1
[dh]: https://www.rfc-editor.org/rfc/rfc8446#section-7.4
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open EthLib.Base
open EthLib.Cryptography.Hash
open Tls13 (Secret)

/-- The string of `Hash.length` zero bytes, 32 for SHA-256, of RFC 8446 §7.1. -/
def zeros : Secret := Vector.replicate 32 0

/-- Derive-Secret of RFC 8446 §7.1, with SHA-256 over the encoded handshake messages.

The label excludes the `tls13 ` prefix, which the labelled expansion adds.

The empty message argument hashes to SHA-256 of the empty string, rather than an empty context. -/
def deriveSecret (secret : Secret) (label messages : ByteArray) : Except Tls13.Error Secret :=
  Tls13.expandLabel secret label (packBytes (Sha256.hash32 messages)) 32

/-- The early secret without a pre-shared key, RFC 8446 §7.1. -/
def earlySecret : Secret := Tls13.extract (packBytes zeros) (packBytes zeros)

/-- Mix the shared secret into the early secret, RFC 8446 §7.1. -/
def handshakeSecret (sharedSecret : ByteArray) : Except Tls13.Error Secret := do
  let derived ← deriveSecret earlySecret "derived".toUTF8 .empty
  return Tls13.extract (packBytes derived) sharedSecret

/-- Derive the master secret from the handshake secret, RFC 8446 §7.1. -/
def masterSecret (handshake : Secret) : Except Tls13.Error Secret := do
  let derived ← deriveSecret handshake "derived".toUTF8 .empty
  return Tls13.extract (packBytes derived) (packBytes zeros)

/-- The secrets through the first application traffic generation, RFC 8446 §7.1. -/
structure KeySchedule where
  /-- `early_secret`. -/
  early : Secret
  /-- `handshake_secret`. -/
  handshake : Secret
  /-- `master_secret`. -/
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

/-- Compute the no-PSK handshake and first application traffic secrets of RFC 8446 §7.1.

The first transcript runs from ClientHello through ServerHello.

The second runs from ClientHello through the server's Finished message.

The function does not check that the second transcript extends the first.

Each transcript includes handshake headers and excludes record headers, as §4.4.1 requires. -/
def keySchedule (sharedSecret helloTranscript serverTranscript : ByteArray) :
    Except Tls13.Error KeySchedule := do
  let handshake ← handshakeSecret sharedSecret
  let master ← masterSecret handshake
  let clientHandshake ← deriveSecret handshake "c hs traffic".toUTF8 helloTranscript
  let serverHandshake ← deriveSecret handshake "s hs traffic".toUTF8 helloTranscript
  let clientApplication ← deriveSecret master "c ap traffic".toUTF8 serverTranscript
  let serverApplication ← deriveSecret master "s ap traffic".toUTF8 serverTranscript
  return ⟨earlySecret, handshake, master, clientHandshake, serverHandshake,
    clientApplication, serverApplication⟩

/-- Finished `verify_data`, the HMAC of the transcript hash under the finished key, RFC 8446 §4.4.4.

During the handshake the secret is the sender's handshake traffic secret, the base key of §4.4.

The transcript ends before the Finished message being computed.

Comparing a received value with this one is left to the caller. -/
def finished (trafficSecret : Secret) (transcript : ByteArray) : Except Tls13.Error Secret := do
  let key ← Tls13.expandLabel trafficSecret "finished".toUTF8 .empty 32
  return Hmac.hmac32 (packBytes key) (packBytes (Sha256.hash32 transcript))

end EthLib.Networking.Quic.Tls
