module

public import EthLib.Networking.Quic.Tls.Messages
public import EthLib.Networking.Proofs.Quic.Tls.Wire

/-!
# Proofs: handshake framing

Framing writes exactly one type byte and three length bytes before the unchanged body.

Reading the frame preserves arbitrary bytes after it.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire
open EthLib.Base (bind_ok_iff)

attribute [local simp] bind pure StateT.bind StateT.pure StateT.lift Except.bind Except.pure

/-- An extension recovers its numeric type, opaque bytes and arbitrary trailing bytes. -/
theorem readExtension_encode {extension : Extension} {encoded : List UInt8}
    (written : encodeExtension extension = .ok encoded) (rest : List UInt8) :
    readExtension (encoded ++ rest) = .ok (extension, rest) := by
  simp only [encodeExtension, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, rfl⟩ := written
  simp [readExtension, List.append_assoc, blob_encode_of_encode hd rest]

/-- An encoded extension consumes its type and length header before its data. -/
theorem length_encodeExtension {extension : Extension} {encoded : List UInt8}
    (written : encodeExtension extension = .ok encoded) : 0 < encoded.length := by
  simp only [encodeExtension, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, rfl⟩ := written
  simp only [List.length_append, Base.natToBytes_length]
  omega

/-- Every successful extension block round trips with its original order and trailing bytes. -/
theorem readExtensions_encode {minimum : Nat} {extensions : List Extension}
    {encoded : List UInt8} (written : encodeExtensions minimum extensions = .ok encoded)
    (rest : List UInt8) :
    readExtensions minimum (encoded ++ rest) = .ok (extensions, rest) := by
  simp only [encodeExtensions, bind_ok_iff] at written
  obtain ⟨u, unique, encoded⟩ := written
  have hu := EthLib.Base.ensure_ok_iff.mp unique
  simp [readExtensions, items_encodeItems encodeExtension readExtension
    (fun _ _ rest h => readExtension_encode h rest)
    (fun _ _ h => length_encodeExtension h) encoded rest, hu]

/-- A vector of two-byte identifiers preserves even identifiers with no implemented algorithm. -/
theorem codePoints_encode {width minimum maximum : Nat} {values : List CodePoint}
    {encoded : List UInt8} (written : encodeCodePoints width minimum maximum values = .ok encoded)
    (rest : List UInt8) :
    items width minimum maximum codePoint (encoded ++ rest) = .ok (values, rest) := by
  unfold encodeCodePoints at written
  apply items_encodeItems (fun (n : CodePoint) => .ok (Base.natToBytes 2 n.val))
    codePoint _ _ written rest
  · intro value data rest h
    cases h
    exact codePoint_encode value rest
  · intro value data h
    cases h
    simp [Base.natToBytes_length]

/-- A certificate entry preserves its certificate bytes and per-certificate extension order. -/
theorem readCertificateEntry_encode {entry : CertificateEntry} {encoded : List UInt8}
    (written : encodeCertificateEntry entry = .ok encoded) (rest : List UInt8) :
    readCertificateEntry (encoded ++ rest) = .ok (entry, rest) := by
  simp only [encodeCertificateEntry, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, extensions, he, rfl⟩ := written
  simp [readCertificateEntry, List.append_assoc,
    blob_encode_of_encode hd (extensions ++ rest), readExtensions_encode he rest]

/-- A certificate entry's length prefix alone consumes three bytes. -/
theorem length_encodeCertificateEntry {entry : CertificateEntry} {encoded : List UInt8}
    (written : encodeCertificateEntry entry = .ok encoded) : 0 < encoded.length := by
  simp only [encodeCertificateEntry, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, extensions, _, rfl⟩ := written
  have length := length_encodeBlob hd
  simp only [List.length_append]
  omega

/-- A certificate list retains every entry, including its order, and may be empty. -/
theorem certificateEntries_encode {values : List CertificateEntry} {encoded : List UInt8}
    (written : encodeItems 3 0 (2 ^ 24 - 1) encodeCertificateEntry values = .ok encoded)
    (rest : List UInt8) :
    items 3 0 (2 ^ 24 - 1) readCertificateEntry (encoded ++ rest) = .ok (values, rest) :=
  items_encodeItems encodeCertificateEntry readCertificateEntry
    (fun _ _ rest h => readCertificateEntry_encode h rest)
    (fun _ _ h => length_encodeCertificateEntry h) written rest

/-- A body within the uint24 bound gets its exact four-byte handshake header. -/
theorem frame_eq_ok (kind : UInt8) (body : List UInt8) (bound : body.length < 2 ^ 24) :
    frame kind body = .ok (kind :: (Base.natToBytes 3 body.length ++ body)) := by
  have upper : body.length ≤ 2 ^ 24 - 1 := by omega
  have capacity : body.length < 256 ^ 3 := bound
  simp [frame, encodeBlob, upper, capacity, bind, Except.bind, pure, Except.pure]

/-- A handshake envelope round trips without consuming a following message. -/
theorem readFrame_frame (kind : UInt8) (body rest : List UInt8)
    (bound : body.length < 2 ^ 24) :
    (frame kind body >>= fun encoded => readFrame (encoded ++ rest)) =
      .ok ((kind, body), rest) := by
  have upper : body.length ≤ 2 ^ 24 - 1 := by omega
  have capacity : body.length < 256 ^ 3 := bound
  simp [frame_eq_ok kind body bound, readFrame, List.append_assoc,
    blob_encode 3 0 (2 ^ 24 - 1) body rest (Nat.zero_le _) upper capacity,
    bind, Except.bind, StateT.bind, pure, Except.pure, StateT.pure]

/-- A framed message has its body length plus the four header bytes. -/
theorem length_frame {kind : UInt8} {body encoded : List UInt8}
    (accepted : frame kind body = .ok encoded) : encoded.length = body.length + 4 := by
  simp only [frame, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
  obtain ⟨data, written, rfl⟩ := accepted
  obtain ⟨_, _, _, rfl⟩ := (encodeBlob_eq_ok_iff ..).mp written
  simp only [List.length_cons, List.length_append, Base.natToBytes_length]
  omega

/-- A duplicate extension type cannot be emitted in a handshake block (§4.2). -/
theorem encodeExtensions_duplicate (minimum : Nat) (extensions : List Extension)
    (duplicate : uniqueExtensions extensions = false) :
    encodeExtensions minimum extensions = .error .duplicateExtension := by
  simp [encodeExtensions, Base.ensure, duplicate, bind, Except.bind]

/-- A Finished message with the wrong hash length cannot be encoded (§4.4.4). -/
theorem encodeBody_finished_length (hashLength : Nat) (data : List UInt8)
    (wrong : data.length ≠ hashLength) :
    encodeBody hashLength (.finished data) = .error .length := by
  simp [encodeBody, Base.ensure, wrong, bind, Except.bind]

@[simp] theorem uint_legacy (rest : List UInt8) :
    uint 2 (3 :: 3 :: rest) = .ok (0x0303, rest) := by
  exact uint_encode 2 0x0303 rest

@[simp] theorem bytes_compression (rest : List UInt8) :
    bytes 2 (1 :: 0 :: rest) = .ok ([1, 0], rest) := by
  simpa using bytes_append [1, 0] rest

/-- Every successfully encoded message body recovers all fields with arbitrary trailing bytes. -/
theorem readBody_encodeBody {hashLength : Nat} {message : Message} {body : List UInt8}
    (written : encodeBody hashLength message = .ok body) (rest : List UInt8) :
    readBody hashLength message.type (body ++ rest) = .ok (message, rest) := by
  cases message with
  | clientHello h =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨session, hs, suites, hc, extensions, he, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc, blob_encode_of_encode hs,
      codePoints_encode hc, readExtensions_encode he, require]
  | serverHello h =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨session, hs, extensions, he, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc, blob_encode_of_encode hs,
      readExtensions_encode he, require]
  | encryptedExtensions extensions =>
    simp [readBody, Message.type, readExtensions_encode written rest]
  | certificateRequest request =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨context, hc, extensions, he, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc,
      blob_encode_of_encode hc, readExtensions_encode he]
  | certificate certificate =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨context, hc, entries, he, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc,
      blob_encode_of_encode hc, certificateEntries_encode he]
  | certificateVerify algorithm signature =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨data, hd, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc, blob_encode_of_encode hd]
  | finished data =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨u, size, rfl⟩ := written
    have length := EthLib.Base.ensure_ok_iff.mp size
    simp [readBody, Message.type, ← length]

/-- A successful frame always has a body within the uint24 bound. -/
theorem bound_of_frame {kind : UInt8} {body encoded : List UInt8}
    (written : frame kind body = .ok encoded) : body.length < 2 ^ 24 := by
  simp only [frame, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, _⟩ := written
  exact ((encodeBlob_eq_ok_iff ..).mp hd).2.2.1

/-- All seven message encoders round trip, preserving arbitrary bytes after the message. -/
theorem decode_encode {hashLength : Nat} {message : Message} {encoded : List UInt8}
    (written : encode hashLength message = .ok encoded) (rest : List UInt8) :
    decode hashLength (encoded ++ rest) = .ok (message, rest) := by
  simp only [encode, bind_ok_iff] at written
  obtain ⟨body, hb, hf⟩ := written
  have framed := readFrame_frame message.type body rest (bound_of_frame hf)
  simp only [hf, bind, Except.bind] at framed
  have decoded := readBody_encodeBody hb []
  simp only [List.append_nil] at decoded
  simp [decode, framed, Wire.exact, decoded, Except.mapError]

/-- Two successfully encoded messages with the same bytes have the same fields. -/
theorem encode_injective {hashLength : Nat} {first second : Message} {encoded : List UInt8}
    (left : encode hashLength first = .ok encoded)
    (right : encode hashLength second = .ok encoded) : first = second := by
  have hf := decode_encode left []
  rw [decode_encode right []] at hf
  simpa using hf.symm

end EthLib.Networking.Quic.Tls
