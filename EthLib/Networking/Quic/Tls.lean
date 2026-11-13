module

public import EthLib.Cryptography.Hash.Tls13

/-!
# TLS 1.3 key schedule for SHA-256

[RFC 8446 §7.1][schedule] derives handshake and application traffic secrets from a shared secret.

This schedule uses no pre-shared key.

Callers supply the transcript bytes of [RFC 8446 §4.4.1][transcript], including handshake headers.

After HelloRetryRequest, the caller supplies its synthetic `message_hash` in place of ClientHello1.

The functions do not parse messages, negotiate algorithms or authenticate a peer.

[schedule]: https://www.rfc-editor.org/rfc/rfc8446#section-7.1
[transcript]: https://www.rfc-editor.org/rfc/rfc8446#section-4.4.1
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open EthLib.Base
open EthLib.Cryptography.Hash
open Tls13 (Secret)

/-- `Hash.length` zero bytes, the absent input of RFC 8446 §7.1. -/
def zeros : Secret := Vector.replicate 32 0

/-- Derive-Secret of RFC 8446 §7.1, with SHA-256 over the encoded handshake messages.

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
  early : Secret
  handshake : Secret
  master : Secret
  clientHandshake : Secret
  serverHandshake : Secret
  clientApplication : Secret
  serverApplication : Secret
  deriving DecidableEq

/-- Compute the no-PSK schedule of RFC 8446 §7.1 with SHA-256.

`helloTranscript` contains ClientHello through ServerHello.

`serverTranscript` contains ClientHello through the server's Finished message.

Each transcript includes handshake headers and excludes record headers, as §7.1 requires. -/
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

/-- Finished verify_data, the HMAC of the transcript hash under the finished key, RFC 8446 §4.4.4.

The transcript ends before the Finished message being computed. -/
def finished (trafficSecret : Secret) (transcript : ByteArray) : Except Tls13.Error Secret := do
  let key ← Tls13.expandLabel trafficSecret "finished".toUTF8 .empty 32
  return Hmac.hmac32 (packBytes key) (packBytes (Sha256.hash32 transcript))

end EthLib.Networking.Quic.Tls
