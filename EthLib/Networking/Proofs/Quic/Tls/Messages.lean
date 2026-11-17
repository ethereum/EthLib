module

public import EthLib.Base.Proofs.Except
public import EthLib.Networking.Quic.Tls.Messages
public import EthLib.Networking.Proofs.Quic.Tls.Wire

/-!
# Proofs: handshake framing

Framing writes exactly one type byte and three length bytes before the unchanged body.

Reading the frame preserves arbitrary bytes after it.

Every successfully encoded message decodes to the same fields, so encoding is injective.

Every accepted message re-encodes to exactly the bytes that decoding consumed.
-/

@[expose] public section

namespace EthLib.Networking.Quic.Tls

open Wire
open EthLib.Base.ByteReader (bytes_append uint_encode require_true)
open EthLib.Base (bind_ok_iff)

attribute [local simp] EthLib.Base.toByteArray_data_toList

attribute [local simp] bind pure StateT.bind StateT.pure StateT.lift Except.bind Except.pure

/-- An extension recovers its numeric type, opaque bytes and arbitrary trailing bytes. -/
theorem readExtension_encode {extension : Extension} {encoded : List UInt8}
    (written : encodeExtension extension = .ok encoded) (rest : List UInt8) :
    readExtension (encoded ++ rest) = .ok (extension, rest) := by
  simp only [encodeExtension, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, rfl⟩ := written
  simp [readExtension, List.append_assoc, blob_encode_of_encode hd rest]

/-- A successful extension encoding is never empty. -/
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

/-- An identifier vector round trips, including identifiers that no algorithm implements. -/
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

/-- A successful certificate entry encoding is never empty. -/
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
theorem frameList_eq_ok (kind : UInt8) (body : List UInt8) (bound : body.length < 2 ^ 24) :
    frameList kind body = .ok (kind :: (Base.natToBytes 3 body.length ++ body)) := by
  have upper : body.length ≤ 2 ^ 24 - 1 := by omega
  have capacity : body.length < 256 ^ 3 := bound
  simp [frameList, encodeBlob, upper, capacity, bind, Except.bind, pure, Except.pure]

/-- A handshake envelope round trips without consuming a following message. -/
theorem readFrame_frameList (kind : UInt8) (body rest : List UInt8)
    (bound : body.length < 2 ^ 24) :
    (frameList kind body >>= fun encoded => readFrame (encoded ++ rest)) =
      .ok ((kind, body), rest) := by
  have upper : body.length ≤ 2 ^ 24 - 1 := by omega
  have capacity : body.length < 256 ^ 3 := bound
  simp [frameList_eq_ok kind body bound, readFrame, List.append_assoc,
    blob_encode 3 0 (2 ^ 24 - 1) body rest (Nat.zero_le _) upper capacity,
    bind, Except.bind, StateT.bind, pure, Except.pure, StateT.pure]

/-- A framed message has its body length plus the four header bytes. -/
theorem length_frameList {kind : UInt8} {body encoded : List UInt8}
    (accepted : frameList kind body = .ok encoded) : encoded.length = body.length + 4 := by
  simp only [frameList, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at accepted
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
theorem encodeBody_finished_length (hashLength : Nat) (data : ByteArray)
    (wrong : data.size ≠ hashLength) :
    encodeBody hashLength (.finished data) = .error .length := by
  simp [encodeBody, Base.ensure, wrong, bind, Except.bind]

/-- The legacy version bytes read as `0x0303`. -/
@[simp] theorem uint_legacy (rest : List UInt8) :
    uint 2 (3 :: 3 :: rest) = .ok (0x0303, rest) := by
  exact uint_encode Wire.Error.truncated 2 0x0303 rest

/-- The compression vector reads back unchanged. -/
@[simp] theorem bytes_compression (rest : List UInt8) :
    bytes 2 (1 :: 0 :: rest) = .ok ([1, 0], rest) := by
  simpa using bytes_append Wire.Error.truncated [1, 0] rest

/-- Every successfully encoded message body recovers all fields with arbitrary trailing bytes. -/
theorem readBody_encodeBody {hashLength : Nat} {message : Message} {body : List UInt8}
    (written : encodeBody hashLength message = .ok body) (rest : List UInt8) :
    readBody hashLength message.type (body ++ rest) = .ok (message, rest) := by
  cases message with
  | clientHello h =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨session, hs, suites, hc, extensions, he, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc, blob_encode_of_encode hs,
      codePoints_encode hc, readExtensions_encode he, require, Base.ByteReader.require]
  | serverHello h =>
    simp only [encodeBody, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
    obtain ⟨session, hs, extensions, he, rfl⟩ := written
    simp [readBody, Message.type, List.append_assoc, blob_encode_of_encode hs,
      readExtensions_encode he, require, Base.ByteReader.require]
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
    have read : bytes data.size (data.data.toList ++ rest) =
        .ok (data.data.toList, rest) := by
      simpa using bytes_append Wire.Error.truncated data.data.toList rest
    simp [readBody, Message.type, ← length, read]

/-- A successful frame always has a body within the uint24 bound. -/
theorem bound_of_frameList {kind : UInt8} {body encoded : List UInt8}
    (written : frameList kind body = .ok encoded) : body.length < 2 ^ 24 := by
  simp only [frameList, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at written
  obtain ⟨data, hd, _⟩ := written
  exact ((encodeBlob_eq_ok_iff ..).mp hd).2.2.1

/-- All seven message encoders round trip, preserving arbitrary bytes after the message. -/
theorem decodeList_encodeList {hashLength : Nat} {message : Message} {encoded : List UInt8}
    (written : encodeList hashLength message = .ok encoded) (rest : List UInt8) :
    decodeList hashLength (encoded ++ rest) = .ok (message, rest) := by
  simp only [encodeList, bind_ok_iff] at written
  obtain ⟨body, hb, hf⟩ := written
  have framed := readFrame_frameList message.type body rest (bound_of_frameList hf)
  simp only [hf, bind, Except.bind] at framed
  have decoded := readBody_encodeBody hb []
  simp only [List.append_nil] at decoded
  simp [decodeList, framed, Wire.exact, decoded, Except.mapError]

/-- Two successfully encoded messages with the same bytes have the same fields. -/
theorem encodeList_injective {hashLength : Nat} {first second : Message} {encoded : List UInt8}
    (left : encodeList hashLength first = .ok encoded)
    (right : encodeList hashLength second = .ok encoded) : first = second := by
  have hf := decodeList_encodeList left []
  rw [decodeList_encodeList right []] at hf
  simpa using hf.symm

/-- An accepted extension is exactly its numeric type and length-prefixed payload. -/
theorem encodeExtension_of_readExtension {input rest : List UInt8} {extension : Extension}
    (parsed : readExtension input = .ok (extension, rest)) :
    ∃ encoded, encodeExtension extension = .ok encoded ∧ input = encoded ++ rest := by
  change (codePoint input >>= fun (kind, suffix) =>
    blob 2 0 65535 suffix >>= fun (data, trailing) => .ok (⟨kind, data.toByteArray⟩, trailing)) =
      .ok (extension, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨kind, suffix⟩, kindRead, ⟨data, trailing⟩, dataRead, rfl, rfl⟩ := parsed
  dsimp only at dataRead ⊢
  obtain ⟨encoded, written, same⟩ := encodeBlob_of_blob dataRead
  refine ⟨Base.natToBytes 2 kind.val ++ encoded, ?_, ?_⟩
  · simp [encodeExtension, written]
  · rw [eq_natToBytes_of_codePoint kindRead, same]
    simp only [List.append_assoc]

/-- An accepted extension block has the exact encoding of its returned ordered extensions. -/
theorem encodeExtensions_of_readExtensions {minimum : Nat} {input rest : List UInt8}
    {extensions : List Extension}
    (parsed : readExtensions minimum input = .ok (extensions, rest)) :
    ∃ encoded, encodeExtensions minimum extensions = .ok encoded ∧ input = encoded ++ rest := by
  change (items 2 minimum 65535 readExtension input >>= fun (values, suffix) =>
    require (uniqueExtensions values = true) .duplicateExtension suffix >>= fun (_, trailing) =>
      .ok (values, trailing)) = .ok (extensions, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨values, suffix⟩, valuesRead, ⟨u, trailing⟩, checked, rfl, rfl⟩ := parsed
  obtain ⟨unique, rfl⟩ := (Base.ByteReader.require_ok_iff ..).mp checked
  obtain ⟨encoded, written, same⟩ := encodeItems_of_items encodeExtension readExtension
    (fun _ _ _ accepted => encodeExtension_of_readExtension accepted) valuesRead
  refine ⟨encoded, ?_, same⟩
  simp [encodeExtensions, Base.ensure, unique, written]

/-- Every accepted vector of identifiers reconstructs its exact length-prefixed encoding. -/
theorem encodeCodePoints_of_items {width minimum maximum : Nat} {input rest : List UInt8}
    {values : List CodePoint}
    (parsed : items width minimum maximum codePoint input = .ok (values, rest)) :
    ∃ encoded, encodeCodePoints width minimum maximum values = .ok encoded ∧
      input = encoded ++ rest := by
  apply encodeItems_of_items (fun value : CodePoint => .ok (Base.natToBytes 2 value.val))
    codePoint _ parsed
  intro data value trailing read
  exact ⟨Base.natToBytes 2 value.val, rfl, eq_natToBytes_of_codePoint read⟩

/-- An accepted certificate entry re-encodes its opaque bytes and extensions without change. -/
theorem encodeCertificateEntry_of_readCertificateEntry {input rest : List UInt8}
    {entry : CertificateEntry} (parsed : readCertificateEntry input = .ok (entry, rest)) :
    ∃ encoded, encodeCertificateEntry entry = .ok encoded ∧ input = encoded ++ rest := by
  change (blob 3 1 (2 ^ 24 - 1) input >>= fun (data, suffix) =>
    readExtensions 0 suffix >>= fun (extensions, trailing) =>
      .ok (⟨data.toByteArray, extensions⟩, trailing)) =
      .ok (entry, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨data, suffix⟩, dataRead, ⟨extensions, trailing⟩, extensionsRead, rfl, rfl⟩ := parsed
  dsimp only at extensionsRead ⊢
  obtain ⟨encodedData, dataWritten, first⟩ := encodeBlob_of_blob dataRead
  obtain ⟨encodedExtensions, extensionsWritten, last⟩ :=
    encodeExtensions_of_readExtensions extensionsRead
  refine ⟨encodedData ++ encodedExtensions, ?_, ?_⟩
  · simp [encodeCertificateEntry, dataWritten, extensionsWritten]
  · rw [first, last]
    simp only [List.append_assoc]

/-- An accepted handshake envelope reconstructs its exact type, body length and body bytes. -/
theorem frameList_of_readFrame {input rest body : List UInt8} {kind : UInt8}
    (parsed : readFrame input = .ok ((kind, body), rest)) :
    ∃ encoded, frameList kind body = .ok encoded ∧ input = encoded ++ rest := by
  change (uint 1 input >>= fun (tag, suffix) =>
    blob 3 0 (2 ^ 24 - 1) suffix >>= fun (data, trailing) =>
      .ok ((UInt8.ofNat tag, data), trailing)) = .ok ((kind, body), rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨tag, suffix⟩, tagRead, ⟨data, trailing⟩, dataRead, ⟨rfl, rfl⟩, rfl⟩ := parsed
  dsimp only at dataRead ⊢
  obtain ⟨encoded, written, same⟩ := encodeBlob_of_blob dataRead
  refine ⟨UInt8.ofNat tag :: encoded, ?_, ?_⟩
  · simp [frameList, written]
  · rw [(Base.ByteReader.uint_ok_iff ..).mp tagRead |>.2, same]
    rfl

/-- An accepted message body re-encodes to its exact prefix and has the received type. -/
theorem encodeBody_of_readBody {hashLength : Nat} {kind : UInt8} {input rest : List UInt8}
    {message : Message} (parsed : readBody hashLength kind input = .ok (message, rest)) :
    message.type = kind ∧ ∃ encoded,
      encodeBody hashLength message = .ok encoded ∧ input = encoded ++ rest := by
  have cases : kind.toNat = 1 ∨ kind.toNat = 2 ∨ kind.toNat = 8 ∨ kind.toNat = 13 ∨
      kind.toNat = 11 ∨ kind.toNat = 15 ∨ kind.toNat = 20 ∨
      (kind.toNat ≠ 1 ∧ kind.toNat ≠ 2 ∧ kind.toNat ≠ 8 ∧ kind.toNat ≠ 13 ∧
        kind.toNat ≠ 11 ∧ kind.toNat ≠ 15 ∧ kind.toNat ≠ 20) := by omega
  rcases cases with tag | tag | tag | tag | tag | tag | tag | other
  ·
    have sameKind : kind = 1 := UInt8.toNat_inj.mp tag
    subst kind
    change (uint 2 input >>= fun (version, a) =>
      require (version = 0x0303) .constant a >>= fun (_, b) =>
      vector 32 b >>= fun (random, c) =>
      blob 1 0 32 c >>= fun (session, d) =>
      items 2 2 65534 codePoint d >>= fun (suites, e) =>
      bytes 2 e >>= fun (compression, f) =>
      require (compression = [1, 0]) .constant f >>= fun (_, g) =>
      readExtensions 8 g >>= fun (extensions, h) =>
        .ok (.clientHello ⟨random, session.toByteArray, suites, extensions⟩, h)) =
          .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨version, a⟩, versionRead, ⟨u, b⟩, versionCheck, ⟨random, c⟩, randomRead,
      ⟨session, d⟩, sessionRead, ⟨suites, e⟩, suitesRead, ⟨compression, f⟩, compressionRead,
      ⟨v, g⟩, compressionCheck, ⟨extensions, h⟩, extensionsRead, rfl, rfl⟩ := parsed
    dsimp only at *
    obtain ⟨rfl, rfl⟩ := (Base.ByteReader.require_ok_iff ..).mp versionCheck
    obtain ⟨rfl, rfl⟩ := (Base.ByteReader.require_ok_iff ..).mp compressionCheck
    obtain ⟨encodedSession, sessionWritten, sessionSame⟩ := encodeBlob_of_blob sessionRead
    obtain ⟨encodedSuites, suitesWritten, suitesSame⟩ := encodeCodePoints_of_items suitesRead
    obtain ⟨encodedExtensions, extensionsWritten, extensionsSame⟩ :=
      encodeExtensions_of_readExtensions extensionsRead
    refine ⟨rfl, [3, 3] ++ random.toList ++ encodedSession ++ encodedSuites ++
      [1, 0] ++ encodedExtensions, ?_, ?_⟩
    · simp [encodeBody, sessionWritten, suitesWritten, extensionsWritten]
    · rw [(Base.ByteReader.uint_ok_iff ..).mp versionRead |>.2,
        eq_toList_append_of_vector randomRead, sessionSame, suitesSame,
        (Base.ByteReader.bytes_ok_iff ..).mp compressionRead |>.2, extensionsSame]
      simp only [List.append_assoc]
      rfl
  ·
    have sameKind : kind = 2 := UInt8.toNat_inj.mp tag
    subst kind
    change (uint 2 input >>= fun (version, a) =>
      require (version = 0x0303) .constant a >>= fun (_, b) =>
      vector 32 b >>= fun (random, c) =>
      blob 1 0 32 c >>= fun (session, d) =>
      codePoint d >>= fun (suite, e) =>
      uint 1 e >>= fun (compression, f) =>
      require (compression = 0) .constant f >>= fun (_, g) =>
      readExtensions 6 g >>= fun (extensions, h) =>
        .ok (.serverHello ⟨random, session.toByteArray, suite, extensions⟩, h)) =
          .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨version, a⟩, versionRead, ⟨u, b⟩, versionCheck, ⟨random, c⟩, randomRead,
      ⟨session, d⟩, sessionRead, ⟨suite, e⟩, suiteRead, ⟨compression, f⟩, compressionRead,
      ⟨v, g⟩, compressionCheck, ⟨extensions, h⟩, extensionsRead, rfl, rfl⟩ := parsed
    dsimp only at *
    obtain ⟨rfl, rfl⟩ := (Base.ByteReader.require_ok_iff ..).mp versionCheck
    obtain ⟨rfl, rfl⟩ := (Base.ByteReader.require_ok_iff ..).mp compressionCheck
    obtain ⟨encodedSession, sessionWritten, sessionSame⟩ := encodeBlob_of_blob sessionRead
    obtain ⟨encodedExtensions, extensionsWritten, extensionsSame⟩ :=
      encodeExtensions_of_readExtensions extensionsRead
    refine ⟨rfl, [3, 3] ++ random.toList ++ encodedSession ++ Base.natToBytes 2 suite.val ++
      [0] ++ encodedExtensions, ?_, ?_⟩
    · simp [encodeBody, sessionWritten, extensionsWritten]
    · rw [(Base.ByteReader.uint_ok_iff ..).mp versionRead |>.2,
        eq_toList_append_of_vector randomRead, sessionSame,
        eq_natToBytes_of_codePoint suiteRead,
        (Base.ByteReader.uint_ok_iff ..).mp compressionRead |>.2, extensionsSame]
      simp only [List.append_assoc]
      rfl
  ·
    have sameKind : kind = 8 := UInt8.toNat_inj.mp tag
    subst kind
    change (readExtensions 0 input >>= fun (extensions, suffix) =>
      .ok (.encryptedExtensions extensions, suffix)) = .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨extensions, suffix⟩, extensionsRead, rfl, rfl⟩ := parsed
    exact ⟨rfl, encodeExtensions_of_readExtensions extensionsRead⟩
  ·
    have sameKind : kind = 13 := UInt8.toNat_inj.mp tag
    subst kind
    change (blob 1 0 255 input >>= fun (context, suffix) =>
      readExtensions 2 suffix >>= fun (extensions, trailing) =>
        .ok (.certificateRequest ⟨context.toByteArray, extensions⟩, trailing)) =
          .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨context, suffix⟩, contextRead, ⟨extensions, trailing⟩,
      extensionsRead, rfl, rfl⟩ := parsed
    dsimp only at extensionsRead ⊢
    obtain ⟨encodedContext, contextWritten, contextSame⟩ := encodeBlob_of_blob contextRead
    obtain ⟨encodedExtensions, extensionsWritten, extensionsSame⟩ :=
      encodeExtensions_of_readExtensions extensionsRead
    refine ⟨rfl, encodedContext ++ encodedExtensions, ?_, ?_⟩
    · simp [encodeBody, contextWritten, extensionsWritten]
    · rw [contextSame, extensionsSame]
      simp only [List.append_assoc]
  ·
    have sameKind : kind = 11 := UInt8.toNat_inj.mp tag
    subst kind
    change (blob 1 0 255 input >>= fun (context, suffix) =>
      items 3 0 (2 ^ 24 - 1) readCertificateEntry suffix >>= fun (entries, trailing) =>
        .ok (.certificate ⟨context.toByteArray, entries⟩, trailing)) = .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨context, suffix⟩, contextRead, ⟨entries, trailing⟩, entriesRead, rfl, rfl⟩ := parsed
    dsimp only at entriesRead ⊢
    obtain ⟨encodedContext, contextWritten, contextSame⟩ := encodeBlob_of_blob contextRead
    obtain ⟨encodedEntries, entriesWritten, entriesSame⟩ :=
      encodeItems_of_items encodeCertificateEntry readCertificateEntry
        (fun _ _ _ accepted => encodeCertificateEntry_of_readCertificateEntry accepted) entriesRead
    refine ⟨rfl, encodedContext ++ encodedEntries, ?_, ?_⟩
    · simp [encodeBody, contextWritten, entriesWritten]
    · rw [contextSame, entriesSame]
      simp only [List.append_assoc]
  ·
    have sameKind : kind = 15 := UInt8.toNat_inj.mp tag
    subst kind
    change (codePoint input >>= fun (algorithm, suffix) =>
      blob 2 0 65535 suffix >>= fun (signature, trailing) =>
        .ok (.certificateVerify algorithm signature.toByteArray, trailing)) =
          .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨algorithm, suffix⟩, algorithmRead, ⟨signature, trailing⟩, signatureRead,
      rfl, rfl⟩ := parsed
    dsimp only at signatureRead ⊢
    obtain ⟨encodedSignature, signatureWritten, signatureSame⟩ := encodeBlob_of_blob signatureRead
    refine ⟨rfl, Base.natToBytes 2 algorithm.val ++ encodedSignature, ?_, ?_⟩
    · simp [encodeBody, signatureWritten]
    · rw [eq_natToBytes_of_codePoint algorithmRead, signatureSame]
      simp only [List.append_assoc]
  ·
    have sameKind : kind = 20 := UInt8.toNat_inj.mp tag
    subst kind
    change (bytes hashLength input >>= fun (data, suffix) =>
      .ok (.finished data.toByteArray, suffix)) = .ok (message, rest) at parsed
    simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
    obtain ⟨⟨data, suffix⟩, dataRead, rfl, rfl⟩ := parsed
    obtain ⟨length, same⟩ := (Base.ByteReader.bytes_ok_iff ..).mp dataRead
    refine ⟨rfl, data, ?_, same⟩
    simp [encodeBody, Base.ensure, length]
  · simp [readBody, other.1, other.2.1, other.2.2.1, other.2.2.2.1,
      other.2.2.2.2.1, other.2.2.2.2.2.1, other.2.2.2.2.2.2,
      throw, throwThe, MonadExceptOf.throw, StateT.lift] at parsed

/-- Every accepted message is exactly one successful encoding followed by the returned suffix. -/
theorem encodeList_of_decodeList {hashLength : Nat} {input rest : List UInt8} {message : Message}
    (parsed : decodeList hashLength input = .ok (message, rest)) :
    ∃ encoded, encodeList hashLength message = .ok encoded ∧ input = encoded ++ rest := by
  change (readFrame input >>= fun ((kind, body), suffix) =>
    (Wire.exact (readBody hashLength kind) body).mapError
      (fun error => match error with | .truncated => .length | error => error) >>=
        fun decoded => .ok (decoded, suffix)) = .ok (message, rest) at parsed
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at parsed
  obtain ⟨⟨⟨kind, body⟩, suffix⟩, frameRead, decoded, bodyRead, rfl, rfl⟩ := parsed
  have exactRead : Wire.exact (readBody hashLength kind) body = .ok decoded := by
    cases result : Wire.exact (readBody hashLength kind) body <;>
      simp_all [Except.mapError]
  have bodyRead := (exact_eq_ok_iff ..).mp exactRead
  obtain ⟨sameKind, encodedBody, bodyWritten, bodySame⟩ := encodeBody_of_readBody bodyRead
  simp only [List.append_nil] at bodySame
  subst body
  obtain ⟨encoded, framed, inputSame⟩ := frameList_of_readFrame frameRead
  refine ⟨encoded, ?_, inputSame⟩
  simp [encodeList, bodyWritten, sameKind, framed]

/-- Decoding succeeds exactly for a complete encoding followed by the returned suffix. -/
theorem decodeList_eq_ok_iff {hashLength : Nat} {input rest : List UInt8} {message : Message} :
    decodeList hashLength input = .ok (message, rest) ↔
      ∃ encoded, encodeList hashLength message = .ok encoded ∧ input = encoded ++ rest := by
  constructor
  · exact encodeList_of_decodeList
  · rintro ⟨encoded, written, rfl⟩
    exact decodeList_encodeList written rest

/-- A packed body within the uint24 bound gets its exact four-byte handshake header. -/
theorem frame_eq_ok (kind : UInt8) (body : ByteArray) (bound : body.size < 2 ^ 24) :
    frame kind body =
      .ok ((kind :: (Base.natToBytes 3 body.size ++ body.data.toList)).toByteArray) := by
  have capacity : body.data.toList.length < 2 ^ 24 := by simpa using bound
  simp [frame, frameList_eq_ok kind body.data.toList capacity, Except.map]

/-- A successfully framed packed body has its size plus the four header bytes. -/
theorem size_frame {kind : UInt8} {body encoded : ByteArray}
    (written : frame kind body = .ok encoded) : encoded.size = body.size + 4 := by
  cases original : frameList kind body.data.toList with
  | error error => simp [frame, original, Except.map] at written
  | ok bytes =>
    have same : bytes.toByteArray = encoded := by simpa [frame, original, Except.map] using written
    subst encoded
    simpa using length_frameList original

/-- A successfully framed packed body fits the uint24 length bound. -/
theorem bound_of_frame {kind : UInt8} {body encoded : ByteArray}
    (written : frame kind body = .ok encoded) : body.size < 2 ^ 24 := by
  cases original : frameList kind body.data.toList with
  | error error => simp [frame, original, Except.map] at written
  | ok bytes => simpa using bound_of_frameList original

/-- Every packed encoding decodes to its message and preserves packed trailing bytes. -/
theorem decode_encode {hashLength : Nat} {message : Message} {encoded : ByteArray}
    (written : encode hashLength message = .ok encoded) (rest : ByteArray) :
    decode hashLength (encoded ++ rest) = .ok (message, rest) := by
  cases original : encodeList hashLength message with
  | error error => simp [encode, original, Except.map] at written
  | ok bytes =>
    have same : bytes.toByteArray = encoded := by simpa [encode, original, Except.map] using written
    subst encoded
    simpa [decode, Except.map, EthLib.Base.toByteArray_data_toList] using
      congrArg (Except.map fun (pair : Message × List UInt8) =>
        (pair.1, pair.2.toByteArray)) (decodeList_encodeList original rest.data.toList)

/-- Two messages with the same successful packed encoding are equal. -/
theorem encode_injective {hashLength : Nat} {first second : Message} {encoded : ByteArray}
    (left : encode hashLength first = .ok encoded)
    (right : encode hashLength second = .ok encoded) : first = second := by
  have l := decode_encode left ByteArray.empty
  have r := decode_encode right ByteArray.empty
  rw [l] at r
  exact (Prod.mk.inj (Except.ok.inj r)).1

/-- Packing a message encoding preserves exactly the list encoder's successful result. -/
theorem encode_ok_iff (hashLength : Nat) (message : Message) (encoded : ByteArray) :
    encode hashLength message = .ok encoded ↔
      encodeList hashLength message = .ok encoded.data.toList := by
  cases written : encodeList hashLength message with
  | error error => simp [encode, written, Except.map]
  | ok data =>
    simp only [encode, written, Except.map, Except.ok.injEq]
    constructor
    · intro same
      simpa using congrArg (fun bytes : ByteArray => bytes.data.toList) same
    · intro same
      rw [same, Base.toByteArray_data_toList]

/-- Packing a decoded message preserves its fields and every trailing byte. -/
theorem decode_ok_iff (hashLength : Nat) (input rest : ByteArray) (message : Message) :
    decode hashLength input = .ok (message, rest) ↔
      decodeList hashLength input.data.toList = .ok (message, rest.data.toList) := by
  cases read : decodeList hashLength input.data.toList with
  | error error => simp [decode, read, Except.map]
  | ok result =>
    rcases result with ⟨value, trailing⟩
    simp only [decode, read, Except.map, Except.ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, same⟩
      exact ⟨rfl, by simpa using congrArg (fun bytes : ByteArray => bytes.data.toList) same⟩
    · rintro ⟨rfl, same⟩
      exact ⟨rfl, by rw [same, Base.toByteArray_data_toList]⟩

/-- Every accepted packed message is its encoding followed by the exact returned suffix. -/
theorem encode_of_decode {hashLength : Nat} {input rest : ByteArray} {message : Message}
    (parsed : decode hashLength input = .ok (message, rest)) :
    ∃ encoded, encode hashLength message = .ok encoded ∧ input = encoded ++ rest := by
  have read := (decode_ok_iff hashLength input rest message).mp parsed
  obtain ⟨data, written, same⟩ := encodeList_of_decodeList read
  refine ⟨data.toByteArray, ?_, ?_⟩
  · simp [encode, written, Except.map]
  · apply ByteArray.ext
    apply Array.toList_inj.mp
    simpa [ByteArray.data_append] using same

/-- Packed message decoding succeeds exactly for one encoding followed by its returned suffix. -/
theorem decode_eq_ok_iff {hashLength : Nat} {input rest : ByteArray} {message : Message} :
    decode hashLength input = .ok (message, rest) ↔
      ∃ encoded, encode hashLength message = .ok encoded ∧ input = encoded ++ rest := by
  constructor
  · exact encode_of_decode
  · rintro ⟨encoded, written, rfl⟩
    exact decode_encode written rest

end EthLib.Networking.Quic.Tls
