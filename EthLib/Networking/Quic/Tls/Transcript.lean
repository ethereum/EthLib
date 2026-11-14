module

public import EthLib.Networking.Quic.Tls.Messages
public import EthLib.Cryptography.Hash.Sha256

/-!
# SHA-256 handshake transcripts

[RFC 8446 §4.4.1][transcript] hashes complete handshake messages with their headers.

The transcript retains the received bytes, including unknown extensions and their order.

A HelloRetryRequest replaces ClientHello1 with its synthetic SHA-256 `message_hash` message.

The retry is accepted only immediately after one ClientHello, and only once.

The caller must have negotiated a cipher suite whose hash is SHA-256.

Other message-order checks and all authentication checks belong to the handshake steps.

[transcript]: https://www.rfc-editor.org/rfc/rfc8446#section-4.4.1
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire
open EthLib.Cryptography.Hash

/-- Transcript bytes and whether the HelloRetryRequest replacement has occurred.

These bytes exclude record headers, CRYPTO frame headers and QUIC packet headers. -/
structure Transcript where
  bytes : List UInt8 := []
  retried : Bool := false
  deriving Repr, DecidableEq

/-- The SHA-256 synthetic handshake message of RFC 8446 §4.4.1.

The uint24 length is 32 and the type is 254. -/
def messageHash (clientHello : List UInt8) : List UInt8 :=
  [254, 0, 0, 32] ++ (Sha256.hash32 ⟨clientHello.toArray⟩).toList

/-- Check that the saved bytes are exactly one ClientHello, as the retry replacement requires. -/
def singleClientHello (input : List UInt8) : Bool :=
  match exact (decode 32) input with
  | .ok (.clientHello _) => true
  | _ => false

/-- Append exactly one complete SHA-256 handshake message, preserving its received bytes.

A retry rewrites ClientHello1 as §4.4.1 requires; another retry is rejected (§4.1.4).

The result records framing and retry handling, without authenticating the handshake. -/
def Transcript.append (transcript : Transcript) (encoded : List UInt8) :
    Except Error Transcript := do
  let message ← exact (decode 32) encoded
  if message.isRetry then
    Base.ensure (transcript.retried = false ∧ singleClientHello transcript.bytes = true) .retry
    return ⟨messageHash transcript.bytes ++ encoded, true⟩
  else
    return ⟨transcript.bytes ++ encoded, transcript.retried⟩

/-- Build a SHA-256 transcript from complete messages, rejecting framing and retry errors. -/
def transcript (messages : List (List UInt8)) : Except Error Transcript :=
  messages.foldlM Transcript.append {}

/-- Hash the saved handshake bytes, RFC 8446 §4.4.1. -/
def Transcript.hash (transcript : Transcript) : Vector UInt8 32 :=
  Sha256.hash32 ⟨transcript.bytes.toArray⟩

/-- CertificateVerify's signed content, RFC 8446 §4.4.3.

It contains 64 spaces, the role's context string, a zero separator and the transcript hash.

The caller hashes the transcript through Certificate, before CertificateVerify. -/
def certificateVerifyInput (server : Bool) (digest : Vector UInt8 32) : List UInt8 :=
  List.replicate 64 32 ++
    (if server then "TLS 1.3, server CertificateVerify"
      else "TLS 1.3, client CertificateVerify").toUTF8.toList ++ [0] ++ digest.toList

end EthLib.Networking.Quic.Tls
