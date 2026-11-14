module

public import EthLib.Networking.Quic.Tls.Transcript
public import EthLib.Networking.Proofs.Quic.Tls.Messages

/-!
# Proofs: handshake transcript bytes

Ordinary messages keep all received bytes.

A retry makes the replacement of [RFC 8446 §4.4.1][transcript].

These results make no claim about message ordering beyond the retry or about authentication.

[transcript]: https://www.rfc-editor.org/rfc/rfc8446#section-4.4.1
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire
open EthLib.Cryptography.Hash

/-- The synthetic message has a four-byte header and a 32-byte hash. -/
theorem length_messageHash (clientHello : List UInt8) : (messageHash clientHello).length = 36 := by
  simp [messageHash]

/-- An ordinary message appends its received encoding without reconstructing its fields. -/
theorem append_eq_ok_of_not_retry (saved : Transcript) (encoded : List UInt8) (message : Message)
    (decoded : Wire.exact (decode 32) encoded = .ok message)
    (ordinary : message.isRetry = false) :
    saved.append encoded = .ok ⟨saved.bytes ++ encoded, saved.retried⟩ := by
  simp [Transcript.append, decoded, ordinary, bind, Except.bind, pure, Except.pure]

/-- The first retry replaces exactly ClientHello1 and then includes the received retry bytes. -/
theorem append_eq_ok_of_retry (saved : Transcript) (encoded : List UInt8) (message : Message)
    (decoded : Wire.exact (decode 32) encoded = .ok message)
    (retry : message.isRetry = true) (first : saved.retried = false)
    (hello : singleClientHello saved.bytes = true) :
    saved.append encoded = .ok ⟨messageHash saved.bytes ++ encoded, true⟩ := by
  simp [Transcript.append, decoded, retry, first, hello, Base.ensure,
    bind, Except.bind, pure, Except.pure]

/-- A second retry is rejected, regardless of its contents, RFC 8446 §4.1.4. -/
theorem append_error_of_retried (saved : Transcript) (encoded : List UInt8) (message : Message)
    (decoded : Wire.exact (decode 32) encoded = .ok message)
    (retry : message.isRetry = true) (already : saved.retried = true) :
    saved.append encoded = .error .retry := by
  simp [Transcript.append, decoded, retry, already, Base.ensure, bind, Except.bind]

/-- A retry cannot replace a transcript other than one complete ClientHello. -/
theorem append_error_of_not_clientHello (saved : Transcript) (encoded : List UInt8)
    (message : Message) (decoded : Wire.exact (decode 32) encoded = .ok message)
    (retry : message.isRetry = true) (notHello : singleClientHello saved.bytes = false) :
    saved.append encoded = .error .retry := by
  simp [Transcript.append, decoded, retry, notHello, Base.ensure, bind, Except.bind]

/-- Malformed or coalesced input cannot contribute bytes to a transcript. -/
theorem append_error_of_decode_error (saved : Transcript) (encoded : List UInt8) (error : Error)
    (rejected : Wire.exact (decode 32) encoded = .error error) :
    saved.append encoded = .error error := by
  simp [Transcript.append, rejected, bind, Except.bind]

end EthLib.Networking.Quic.Tls
