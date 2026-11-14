module

public import EthLib.Networking.Quic.Tls.Extensions
public import EthLib.Networking.Proofs.Quic.Tls.Messages

/-!
# Proofs: handshake extension payloads

Every successfully encoded payload recovers its identifiers and opaque byte fields.

The result concerns wire format, without an algorithm or protocol-selection policy.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire
open EthLib.Base (bind_ok_iff)

attribute [local simp] bind pure StateT.bind StateT.pure StateT.lift Except.bind Except.pure

/-- A key share retains its named group and exchange bytes, without validating the group element. -/
theorem readKeyShare_encode {share : KeyShareEntry} {encoded : List UInt8}
    (written : encodeKeyShare share = .ok encoded) (rest : List UInt8) :
    readKeyShare (encoded ++ rest) = .ok (share, rest) := by
  simp only [encodeKeyShare, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, rfl⟩ := written
  simp [readKeyShare, List.append_assoc, blob_encode_of_encode hd]

/-- A successful key share encoding is never empty. -/
theorem length_encodeKeyShare {share : KeyShareEntry} {encoded : List UInt8}
    (written : encodeKeyShare share = .ok encoded) : 0 < encoded.length := by
  simp only [encodeKeyShare, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, _, rfl⟩ := written
  simp only [List.length_append, Base.natToBytes_length]
  omega

/-- A vector of client key shares preserves their order and may be empty. -/
theorem keyShares_encode {values : List KeyShareEntry} {encoded : List UInt8}
    (written : encodeItems 2 0 65535 encodeKeyShare values = .ok encoded)
    (rest : List UInt8) :
    items 2 0 65535 readKeyShare (encoded ++ rest) = .ok (values, rest) :=
  items_encodeItems encodeKeyShare readKeyShare
    (fun _ _ rest h => readKeyShare_encode h rest)
    (fun _ _ h => length_encodeKeyShare h) written rest

/-- An ALPN vector retains every opaque protocol name without truncating it. -/
theorem alpn_encode {values : List (List UInt8)} {encoded : List UInt8}
    (written : encodeItems 2 2 65535 (encodeBlob 1 1 255) values = .ok encoded)
    (rest : List UInt8) :
    items 2 2 65535 (blob 1 1 255) (encoded ++ rest) = .ok (values, rest) := by
  apply items_encodeItems (encodeBlob 1 1 255) (blob 1 1 255) _ _ written rest
  · intro value data rest h
    exact blob_encode_of_encode h rest
  · intro value data h
    have length := length_encodeBlob h
    omega

/-- All payload forms recover their fields when read as an isolated extension body. -/
theorem readPayload_encodePayloadBody {payload : Payload} {encoded : List UInt8}
    (written : encodePayloadBody payload = .ok encoded) :
    readPayload payload.form encoded = .ok (payload, []) := by
  cases payload with
  | supportedVersions values =>
    have parsed := codePoints_encode written []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | selectedVersion version =>
    cases written
    have parsed := codePoint_encode version []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | supportedGroups values =>
    have parsed := codePoints_encode written []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | signatureAlgorithms values =>
    have parsed := codePoints_encode written []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | clientKeyShare values =>
    have parsed := keyShares_encode written []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | serverKeyShare share =>
    have parsed := readKeyShare_encode written []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | retryKeyShare group =>
    cases written
    have parsed := codePoint_encode group []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | alpn values =>
    have parsed := alpn_encode written []
    simp only [List.append_nil] at parsed
    simp [readPayload, Payload.form, parsed]
  | quicTransportParameters data =>
    cases written
    rfl

/-- Every successfully encoded extension payload decodes in its caller-selected form. -/
theorem decodePayload_encodePayload {payload : Payload} {extension : Extension}
    (written : encodePayload payload = .ok extension) :
    decodePayload payload.form extension = .ok payload := by
  simp only [encodePayload, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, u, size, rfl⟩ := written
  have bound := EthLib.Base.ensure_ok_iff.mp size
  simp [decodePayload, Base.ensure, bound, Wire.exact, readPayload_encodePayloadBody hd,
    Except.mapError]

end EthLib.Networking.Quic.Tls
