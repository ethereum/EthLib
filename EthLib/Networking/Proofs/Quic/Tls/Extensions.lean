module

public import EthLib.Networking.Quic.Tls.Extensions
public import EthLib.Networking.Proofs.Quic.Tls.Messages

/-!
# Proofs: handshake extension payloads

Every successfully encoded payload recovers its identifiers and opaque byte fields.

Every successfully decoded payload re-encodes to its original extension.

The result concerns wire format, without an algorithm or protocol-selection policy.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire
open EthLib.Base (bind_ok_iff)

attribute [local simp] EthLib.Base.toByteArray_data_toList

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
theorem alpn_encode {values : List ByteArray} {encoded : List UInt8}
    (written : encodeItems 2 2 65535 (fun data => encodeBlob 1 1 255 data.data.toList) values =
      .ok encoded)
    (rest : List UInt8) :
    items 2 2 65535 readAlpnName (encoded ++ rest) = .ok (values, rest) := by
  apply items_encodeItems (fun (data : ByteArray) => encodeBlob 1 1 255 data.data.toList)
    readAlpnName _ _ written rest
  · intro value data rest h
    simp [readAlpnName, blob_encode_of_encode h rest]
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
    simp [readPayload, Payload.form]

/-- Every successfully encoded extension payload decodes in its caller-selected form. -/
theorem decodePayload_encodePayload {payload : Payload} {extension : Extension}
    (written : encodePayload payload = .ok extension) :
    decodePayload payload.form extension = .ok payload := by
  simp only [encodePayload, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, u, size, rfl⟩ := written
  have bound := EthLib.Base.ensure_ok_iff.mp size
  simp [decodePayload, Base.ensure, bound, Wire.exact, readPayload_encodePayloadBody hd,
    Except.mapError]

/-- An accepted key share reconstructs its named group and length-prefixed exchange bytes. -/
theorem encodeKeyShare_of_readKeyShare {input rest : List UInt8} {share : KeyShareEntry}
    (parsed : readKeyShare input = .ok (share, rest)) :
    ∃ encoded, encodeKeyShare share = .ok encoded ∧ input = encoded ++ rest := by
  change (codePoint input >>= fun (group, suffix) =>
    blob 2 1 65535 suffix >>= fun (data, trailing) =>
      .ok (⟨group, data.toByteArray⟩, trailing)) =
      .ok (share, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨group, suffix⟩, groupRead, ⟨data, trailing⟩, dataRead, rfl, rfl⟩ := parsed
  dsimp only at dataRead ⊢
  obtain ⟨encoded, written, same⟩ := encodeBlob_of_blob dataRead
  refine ⟨Base.natToBytes 2 group.val ++ encoded, ?_, ?_⟩
  · simp [encodeKeyShare, written]
  · rw [eq_natToBytes_of_codePoint groupRead, same]
    simp only [List.append_assoc]

/-- An accepted packed ALPN name reconstructs every byte of its length-prefixed encoding. -/
theorem encodeBlob_of_readAlpnName {input rest : List UInt8} {name : ByteArray}
    (parsed : readAlpnName input = .ok (name, rest)) :
    ∃ encoded, encodeBlob 1 1 255 name.data.toList = .ok encoded ∧ input = encoded ++ rest := by
  change (blob 1 1 255 input >>= fun (data, suffix) => .ok (data.toByteArray, suffix)) =
    .ok (name, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨data, suffix⟩, dataRead, rfl, rfl⟩ := parsed
  simpa using encodeBlob_of_blob dataRead

/-- An accepted isolated payload has the selected form and re-encodes to every input byte. -/
theorem encodePayloadBody_of_readPayload {form : PayloadForm} {input : List UInt8}
    {payload : Payload} (parsed : readPayload form input = .ok (payload, [])) :
    payload.form = form ∧ encodePayloadBody payload = .ok input := by
  cases form with
  | supportedVersions =>
    change (items 1 2 254 codePoint input >>= fun (values, suffix) =>
      .ok (.supportedVersions values, suffix)) = .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨values, suffix⟩, valuesRead, rfl, rfl⟩ := parsed
    obtain ⟨encoded, written, same⟩ := encodeCodePoints_of_items valuesRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simpa only [encodePayloadBody, same] using written⟩
  | selectedVersion =>
    change (codePoint input >>= fun (value, suffix) => .ok (.selectedVersion value, suffix)) =
      .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨value, suffix⟩, valueRead, rfl, rfl⟩ := parsed
    have same := eq_natToBytes_of_codePoint valueRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simp [encodePayloadBody, same]⟩
  | supportedGroups =>
    change (items 2 2 65535 codePoint input >>= fun (values, suffix) =>
      .ok (.supportedGroups values, suffix)) = .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨values, suffix⟩, valuesRead, rfl, rfl⟩ := parsed
    obtain ⟨encoded, written, same⟩ := encodeCodePoints_of_items valuesRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simpa only [encodePayloadBody, same] using written⟩
  | signatureAlgorithms =>
    change (items 2 2 65534 codePoint input >>= fun (values, suffix) =>
      .ok (.signatureAlgorithms values, suffix)) = .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨values, suffix⟩, valuesRead, rfl, rfl⟩ := parsed
    obtain ⟨encoded, written, same⟩ := encodeCodePoints_of_items valuesRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simpa only [encodePayloadBody, same] using written⟩
  | clientKeyShare =>
    change (items 2 0 65535 readKeyShare input >>= fun (values, suffix) =>
      .ok (.clientKeyShare values, suffix)) = .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨values, suffix⟩, valuesRead, rfl, rfl⟩ := parsed
    obtain ⟨encoded, written, same⟩ := encodeItems_of_items encodeKeyShare readKeyShare
      (fun _ _ _ accepted => encodeKeyShare_of_readKeyShare accepted) valuesRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simpa only [encodePayloadBody, same] using written⟩
  | serverKeyShare =>
    change (readKeyShare input >>= fun (share, suffix) => .ok (.serverKeyShare share, suffix)) =
      .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨share, suffix⟩, shareRead, rfl, rfl⟩ := parsed
    obtain ⟨encoded, written, same⟩ := encodeKeyShare_of_readKeyShare shareRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simpa only [encodePayloadBody, same] using written⟩
  | retryKeyShare =>
    change (codePoint input >>= fun (group, suffix) => .ok (.retryKeyShare group, suffix)) =
      .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨group, suffix⟩, groupRead, rfl, rfl⟩ := parsed
    have same := eq_natToBytes_of_codePoint groupRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simp [encodePayloadBody, same]⟩
  | alpn =>
    change (items 2 2 65535 readAlpnName input >>= fun (values, suffix) =>
      .ok (.alpn values, suffix)) = .ok (payload, []) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨values, suffix⟩, valuesRead, rfl, rfl⟩ := parsed
    obtain ⟨encoded, written, same⟩ := encodeItems_of_items
      (fun name : ByteArray => encodeBlob 1 1 255 name.data.toList) readAlpnName
      (fun _ _ _ accepted => encodeBlob_of_readAlpnName accepted) valuesRead
    simp only [List.append_nil] at same
    exact ⟨rfl, by simpa only [encodePayloadBody, same] using written⟩
  | quicTransportParameters =>
    cases parsed
    exact ⟨rfl, by simp [encodePayloadBody]⟩

/-- Every accepted extension payload is its original encoding in the caller-selected form. -/
theorem encodePayload_of_decodePayload {form : PayloadForm} {extension : Extension}
    {payload : Payload} (parsed : decodePayload form extension = .ok payload) :
    payload.form = form ∧ encodePayload payload = .ok extension := by
  simp only [decodePayload, bind_ok_iff] at parsed
  obtain ⟨u, kindCheck, v, lengthCheck, bodyRead⟩ := parsed
  have kind := Base.ensure_ok_iff.mp kindCheck
  have length := Base.ensure_ok_iff.mp lengthCheck
  have exactRead : Wire.exact (readPayload form) extension.data.data.toList = .ok payload := by
    cases result : Wire.exact (readPayload form) extension.data.data.toList <;>
      simp_all [Except.mapError]
  obtain ⟨sameForm, written⟩ :=
    encodePayloadBody_of_readPayload ((exact_eq_ok_iff ..).mp exactRead)
  refine ⟨sameForm, ?_⟩
  cases extension with
  | mk originalKind data =>
    dsimp only at kind length written ⊢
    subst originalKind
    simp [encodePayload, written, Base.ensure, length, sameForm]

/-- Payload decoding succeeds exactly for the encoding of a payload in the selected form. -/
theorem decodePayload_eq_ok_iff {form : PayloadForm} {extension : Extension} {payload : Payload} :
    decodePayload form extension = .ok payload ↔
      payload.form = form ∧ encodePayload payload = .ok extension := by
  constructor
  · exact encodePayload_of_decodePayload
  · rintro ⟨rfl, written⟩
    exact decodePayload_encodePayload written

end EthLib.Networking.Quic.Tls
