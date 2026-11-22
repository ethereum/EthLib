module

public import EthLib.Networking.Quic.Tls.Messages
public import EthLib.Cryptography.Hash.Sha256

/-!
# SHA-256 handshake transcripts

[RFC 8446 §4.4.1][transcript] hashes complete handshake messages with their headers.

The transcript retains the received bytes, including unknown extensions and their order.

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
  bytes : ByteArray := .empty
  retried : Bool := false
  deriving Repr, DecidableEq

/-- The SHA-256 synthetic handshake message of RFC 8446 §4.4.1. -/
def messageHash (clientHello : ByteArray) : ByteArray :=
  -- `message_hash || 00 00 Hash.length || Hash(ClientHello1)`.
  --
  -- The synthetic message has handshake type 254 (§4).
  --
  -- With SHA-256, `Hash.length` is 32.
  [254, 0, 0, 32].toByteArray ++ Base.packBytes (Sha256.hash32 clientHello)

/-- Check that the saved bytes are exactly one ClientHello, as the retry replacement requires. -/
def singleClientHello (input : ByteArray) : Bool :=
  -- The saved bytes decode as one whole handshake message, and it is a ClientHello.
  match exact (decodeList 32) input.data.toList with
  | .ok (.clientHello _) => true
  | _ => false

/-- Append exactly one complete SHA-256 handshake message, preserving its received bytes.

The result records framing and retry handling, without authenticating the handshake. -/
def Transcript.append (transcript : Transcript) (encoded : ByteArray) :
    Except Error Transcript := do
  -- §4.4.1: each message includes its header, carrying the handshake type and length.
  let message ← exact (decodeList 32) encoded.data.toList
  if message.isRetry then
    -- §4.1.4: a client that receives a second HelloRetryRequest MUST abort.
    --
    -- EthLib returns its retry error instead of the alert of the RFC.
    --
    -- EthLib's check: the transcript so far is exactly one ClientHello, which the retry answers.
    Base.ensure (transcript.retried = false ∧ singleClientHello transcript.bytes = true) .retry
    -- §4.4.1: ClientHello1 is replaced with the synthetic message that holds its hash.
    --
    -- So the bytes become `message_hash || 00 00 Hash.length || Hash(ClientHello1)`.
    --
    -- Then the HelloRetryRequest follows them.
    return ⟨messageHash transcript.bytes ++ encoded, true⟩
  else
    -- §4.4.1: `M1 || M2 || ... || Mn`, each message appended as received.
    return ⟨transcript.bytes ++ encoded, transcript.retried⟩

/-- Build a SHA-256 transcript from complete messages, rejecting framing and retry errors. -/
def transcript (messages : List ByteArray) : Except Error Transcript :=
  -- §4.4.1: the messages in the order they were sent, from the first ClientHello.
  messages.foldlM Transcript.append {}

/-- Hash the saved handshake bytes, RFC 8446 §4.4.1. -/
def Transcript.hash (transcript : Transcript) : Vector UInt8 32 :=
  -- `Transcript-Hash(M1, M2, ... Mn) = Hash(M1 || M2 || ... || Mn)`, where `Hash` is SHA-256.
  Sha256.hash32 transcript.bytes

/-- CertificateVerify's signed content, RFC 8446 §4.4.3.

The caller hashes the transcript through Certificate, before CertificateVerify. -/
def certificateVerifyInput (server : Bool) (digest : Vector UInt8 32) : ByteArray :=
  -- A string that consists of octet 32 (0x20) repeated 64 times.
  (List.replicate 64 32 ++
    -- The context string, for a server or for a client signature.
    (if server then "TLS 1.3, server CertificateVerify"
      else "TLS 1.3, client CertificateVerify").toUTF8.data.toList ++
    -- A single 0 byte which serves as the separator.
    --
    -- Then the content to be signed: `Transcript-Hash(Handshake Context, Certificate)`.
    [0] ++ digest.toList).toByteArray

end EthLib.Networking.Quic.Tls
