module

public import EthLib.Networking.Snappy.Frame
public import EthLib.Networking.Proofs.Snappy.Block

/-!
# `Networking.Proofs.Snappy.Frame`

Properties of the Snappy framing format, against `framing_format.txt` of `google/snappy`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt>

- The stream of the encoder decodes back to its data.
- A stream that decodes starts with the stream identifier (§4.1).
- After the identifier, one bad chunk rejects the whole stream.
- A wrong checksum, more than 65536 bytes or a reserved unskippable type makes a chunk bad.
- Padding and reserved skippable chunks add nothing.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Frame

open EthLib.Networking.Snappy
open EthLib.Base (bytesToUint uintToBytes)

/-! ## One chunk -/

/-- The three length bytes of a length below 2^24, as a list, and their value. -/
theorem uintToBytes_three {n : Nat} (h : n < 2 ^ 24) :
    ∃ a b c, (uintToBytes 3 n).toList = [a, b, c] ∧ bytesToUint #v[a, b, c] = n := by
  have hv : uintToBytes 3 n =
      #v[(uintToBytes 3 n)[0], (uintToBytes 3 n)[1], (uintToBytes 3 n)[2]] := by
    ext i hi
    match i, hi with
    | 0, _ | 1, _ | 2, _ => rfl
  refine ⟨_, _, _, by rw [hv]; rfl, ?_⟩
  rw [← hv, EthLib.Base.bytesToUint_uintToBytes]
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- A chunk that decodes adds its output, and the loop goes on after it. -/
theorem decodeChunks_chunk_ok {type : UInt8} {body out : List UInt8} (rest : List UInt8)
    (fuel : Nat) (h : body.length < 2 ^ 24) (hc : decodeChunk type body = .ok out) :
    decodeChunks (type :: (uintToBytes 3 body.length).toList ++ body ++ rest) (fuel + 1) =
      (decodeChunks rest fuel).map (out ++ ·) := by
  obtain ⟨a, b, c, habc, hv⟩ := uintToBytes_three h
  rw [habc]
  simp [decodeChunks, hv, hc, show ¬ body.length + rest.length < body.length by omega]

/-- A chunk that fails to decode makes the loop fail with its error. -/
theorem decodeChunks_chunk_error {type : UInt8} {body : List UInt8} {e : FrameError}
    (rest : List UInt8) (fuel : Nat) (h : body.length < 2 ^ 24)
    (hc : decodeChunk type body = .error e) :
    decodeChunks (type :: (uintToBytes 3 body.length).toList ++ body ++ rest) (fuel + 1) =
      .error e := by
  obtain ⟨a, b, c, habc, hv⟩ := uintToBytes_three h
  rw [habc]
  simp [decodeChunks, hv, hc, show ¬ body.length + rest.length < body.length by omega]

/-- An uncompressed chunk of at most 65536 bytes with its own checksum decodes to its data. -/
theorem decodeChunk_uncompressed {data : List UInt8} (h : data.length ≤ maxChunkLength) :
    decodeChunk uncompressedType
        ((uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ data) = .ok data := by
  -- The four checksum bytes read back as the checksum, which is below 2^32.
  have hv : Vector.foldr (fun byte acc => byte.toNat + 256 * acc) 0
      (uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat) = (maskedCrc ⟨data.toArray⟩).toNat :=
    (EthLib.Base.bytesToUint_uintToBytes 4 _).trans (Nat.mod_eq_of_lt (UInt32.toNat_lt _))
  simp [decodeChunk, verifyChecksum, compressedType, uncompressedType,
    EthLib.Base.bytesToUint_toVector, hv,
    show ¬ maxChunkLength < data.length by omega]

/-! ## The round trip -/

/-- An uncompressed chunk is a chunk header followed by its checksum and data. -/
theorem uncompressedChunk_eq (data : List UInt8) :
    uncompressedChunk data =
      let body := (uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ data
      uncompressedType :: (uintToBytes 3 body.length).toList ++ body := by
  simp [uncompressedChunk, Nat.add_comm]

/-- The chunks the encoder writes decode back to the data, given enough fuel on both sides. -/
theorem decodeChunks_encodeChunksLiteral (data : List UInt8) {n fuel : Nat}
    (hn : data.length ≤ n) (hfuel : (encodeChunksLiteral data n).length ≤ fuel) :
    decodeChunks (encodeChunksLiteral data n) fuel = .ok data := by
  induction n generalizing data fuel with
  | zero =>
      cases data with
      | nil => cases fuel <;> rfl
      | cons _ _ => simp at hn
  | succ n ih =>
      cases data with
      | nil => cases fuel <;> rfl
      | cons b bs =>
          -- One chunk of the first 65536 bytes, then the rest.
          let chunk := (b :: bs).take maxChunkLength
          let tail := encodeChunksLiteral ((b :: bs).drop maxChunkLength) n
          have henc : encodeChunksLiteral (b :: bs) (n + 1) = uncompressedChunk chunk ++ tail := rfl
          have hchunk : chunk.length ≤ maxChunkLength := List.length_take_le _ _
          rw [henc, uncompressedChunk_eq] at hfuel ⊢
          simp only [List.length_cons, List.length_append, Vector.length_toList] at hfuel
          obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [decodeChunks_chunk_ok tail fuel (by simp [maxChunkLength] at hchunk ⊢; omega)
            (decodeChunk_uncompressed hchunk)]
          rw [ih _ (by simp [maxChunkLength] at hn ⊢; omega) (show tail.length ≤ fuel by omega)]
          simp [Except.map, chunk]

/-- A stream that starts with the stream identifier decodes as the chunks after it. -/
theorem decodeFramesList_streamIdentifier (rest : List UInt8) :
    decodeFramesList (streamIdentifier ++ rest) = decodeChunks rest (rest.length + 9) := by
  have hid : streamIdentifier ++ rest =
      streamIdentifierType :: (uintToBytes 3 (streamIdentifier.drop 4).length).toList ++
        streamIdentifier.drop 4 ++ rest := rfl
  have hc : decodeChunk streamIdentifierType (streamIdentifier.drop 4) = .ok [] := rfl
  have hlen : (streamIdentifier ++ rest).length = rest.length + 9 + 1 := by
    simp [streamIdentifier]
  simp only [decodeFramesList]
  rw [hlen, hid, decodeChunks_chunk_ok rest _ (by decide) hc]
  cases decodeChunks rest (rest.length + 9) <;> rfl

/-- The encoder's stream decodes back to the data. -/
theorem decodeFrames_encodeFramesLiteral (d : ByteArray) :
    decodeFrames (encodeFramesLiteral d) = .ok d := by
  simp only [decodeFrames, encodeFramesLiteral, decodeFramesList_streamIdentifier]
  -- The data length is the byte array's size.
  have hn : d.data.toList.length ≤ d.size := Nat.le_of_eq Array.length_toList
  rw [decodeChunks_encodeChunksLiteral _ hn (by omega)]
  rfl

/-! ## Rejected streams -/

/-- A stream that decodes starts with the ten bytes of the stream identifier (§1, §4.1). -/
theorem decodeFramesList_ok_prefix {bs out : List UInt8} (h : decodeFramesList bs = .ok out) :
    streamIdentifier <+: bs := by
  match bs, h with
  | t :: l0 :: l1 :: l2 :: rest, h =>
      simp only [decodeFramesList] at h
      split at h
      · rename_i ht
        have ht : t = 0xff := by simpa [streamIdentifierType] using ht
        subst ht
        -- The three length bytes, read as a number.
        have hb : bytesToUint #v[l0, l1, l2] = l0.toNat + 256 * (l1.toNat + 256 * l2.toNat) := by
          simp [EthLib.Base.bytesToUint_eq_foldr]
        simp only [List.length_cons, decodeChunks, hb] at h
        split at h
        · simp at h
        · rename_i hlen
          split at h
          · simp at h
          · rename_i out' hc
            simp [decodeChunk, compressedType, uncompressedType, streamIdentifierType,
              streamIdentifier] at hc
            split at hc
            · rename_i htake
              -- The six bytes of "sNaPpY" fix the length at 6, so the header is `06 00 00`.
              have hv : l0.toNat + 256 * (l1.toNat + 256 * l2.toNat) = 6 := by
                have := congrArg List.length htake
                simp at this
                omega
              have b0 := l0.toNat_lt
              have b1 := l1.toNat_lt
              have b2 := l2.toNat_lt
              rw [hv] at htake
              have e0 : l0 = 6 := UInt8.toNat_inj.mp (by simp; omega)
              have e1 : l1 = 0 := UInt8.toNat_inj.mp (by simp; omega)
              have e2 : l2 = 0 := UInt8.toNat_inj.mp (by simp; omega)
              subst e0 e1 e2
              have hsplit := List.take_append_drop 6 rest
              rw [htake] at hsplit
              exact ⟨rest.drop 6, congrArg (fun l => 255 :: 6 :: 0 :: 0 :: l) hsplit⟩
            · simp at hc
      · simp at h
  | [], h => simp [decodeFramesList] at h
  | [_], h | [_, _], h | [_, _, _], h =>
      revert h
      simp only [decodeFramesList, decodeChunks]
      split <;> simp

/-- A chunk that fails to decode after the stream identifier rejects the stream with its error. -/
theorem decodeFramesList_chunk_error {type : UInt8} {body : List UInt8} {e : FrameError}
    (rest : List UInt8) (h : body.length < 2 ^ 24) (hc : decodeChunk type body = .error e) :
    decodeFramesList
        (streamIdentifier ++ (type :: (uintToBytes 3 body.length).toList ++ body ++ rest)) =
      .error e := by
  rw [decodeFramesList_streamIdentifier]
  exact decodeChunks_chunk_error rest _ h hc

/-! ## Rejected chunks -/

/-- A reserved unskippable chunk, of type `0x02` to `0x7f`, is rejected (§4.5). -/
theorem decodeChunk_reservedUnskippable {type : UInt8} (body : List UInt8)
    (hlo : 0x02 ≤ type) (hhi : type < 0x80) :
    decodeChunk type body = .error (.reservedUnskippable type) := by
  have hlo := UInt8.le_iff_toNat_le.mp hlo
  have hhi' := UInt8.lt_iff_toNat_lt.mp hhi
  have h0 : type ≠ compressedType := fun h => by subst h; simp [compressedType] at hlo
  have h1 : type ≠ uncompressedType := fun h => by subst h; simp [uncompressedType] at hlo
  have hff : type ≠ streamIdentifierType := fun h => by
    subst h; simp [streamIdentifierType] at hhi'
  simp [decodeChunk, h0, h1, hff, hhi]

/-- A padding chunk (§4.4) or a reserved skippable chunk (§4.6) adds nothing. -/
theorem decodeChunk_skippable {type : UInt8} (body : List UInt8)
    (hlo : 0x80 ≤ type) (hff : type ≠ streamIdentifierType) :
    decodeChunk type body = .ok [] := by
  have hlo' := UInt8.le_iff_toNat_le.mp hlo
  have h0 : type ≠ compressedType := fun h => by subst h; simp [compressedType] at hlo'
  have h1 : type ≠ uncompressedType := fun h => by subst h; simp [uncompressedType] at hlo'
  have hlt : ¬ type < 0x80 := fun h => by
    have := UInt8.lt_iff_toNat_lt.mp h; omega
  simp [decodeChunk, h0, h1, hff, hlt]

/-- An uncompressed chunk with more than 65536 data bytes is rejected (§4.3). -/
theorem decodeChunk_uncompressed_tooLarge {body : List UInt8}
    (h : maxChunkLength < body.length - 4) :
    decodeChunk uncompressedType body = .error (.chunkTooLarge (body.length - 4)) := by
  have h4 : ¬ body.length < 4 := by simp [maxChunkLength] at h; omega
  simp [decodeChunk, compressedType, uncompressedType, h4, h]

/-- A compressed chunk whose block declares more than 65536 bytes is rejected (§4.2). -/
theorem decodeChunk_compressed_tooLarge {body rest : List UInt8} {declared : Nat}
    (h4 : 4 ≤ body.length) (hpre : readPreamble (body.drop 4) = .ok (declared, rest))
    (h : maxChunkLength < declared) :
    decodeChunk compressedType body = .error (.chunkTooLarge declared) := by
  simp [decodeChunk, show ¬ body.length < 4 by omega, hpre, h]

/-- An uncompressed chunk is rejected if its checksum is not the masked CRC-32C of its data (§3). -/
theorem decodeChunk_uncompressed_checksumMismatch {checksum data : List UInt8}
    (hcs : checksum.length = 4) (hd : data.length ≤ maxChunkLength)
    (hne : UInt32.ofNat (bytesToUint checksum.toArray.toVector) ≠ maskedCrc ⟨data.toArray⟩) :
    decodeChunk uncompressedType (checksum ++ data) =
      .error (.checksumMismatch (UInt32.ofNat (bytesToUint checksum.toArray.toVector))
        (maskedCrc ⟨data.toArray⟩)) := by
  simp only [EthLib.Base.bytesToUint_toVector] at hne
  simp [decodeChunk, compressedType, uncompressedType, hcs, verifyChecksum,
    EthLib.Base.bytesToUint_toVector, hne,
    show ¬ maxChunkLength < data.length by omega]

/-- A compressed chunk is rejected if its checksum does not match its decompressed data (§3). -/
theorem decodeChunk_compressed_checksumMismatch {checksum block data : List UInt8}
    (hcs : checksum.length = 4) (hb : decompressList block = .ok data)
    (hd : data.length ≤ maxChunkLength)
    (hne : UInt32.ofNat (bytesToUint checksum.toArray.toVector) ≠ maskedCrc ⟨data.toArray⟩) :
    decodeChunk compressedType (checksum ++ block) =
      .error (.checksumMismatch (UInt32.ofNat (bytesToUint checksum.toArray.toVector))
        (maskedCrc ⟨data.toArray⟩)) := by
  obtain ⟨rest, hpre⟩ := Block.decompressList_length_eq_declared hb
  simp only [EthLib.Base.bytesToUint_toVector] at hne
  simp [decodeChunk, hcs, hpre, hb, verifyChecksum, EthLib.Base.bytesToUint_toVector, hne,
    show ¬ maxChunkLength < data.length by omega]

/-! ## Known answers

The two accepted streams come from `python-snappy` 0.7.3 on `cramjam` 2.14.0.

The rejected streams are built by hand from the format description.

Each comment says what the stream pins.
-/

/-- The masked CRC-32C of `123456789`.

Its CRC-32C is the check value `0xe3069283` of the CRC catalogue.

Rotated right by 15 bits and added to `0xa282ead8` by hand, it gives `0xc78ab0e5`.
-/
example : maskedCrc "123456789".toUTF8 = 0xc78ab0e5 := by
  rw [String.toUTF8_eq_toByteArray]
  decide +kernel

/-- The nine bytes `123456789` in one uncompressed chunk, as `python-snappy` frames them. -/
def framedDigits : List UInt8 :=
  [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59,
    0x01, 0x0d, 0x00, 0x00, 0xe5, 0xb0, 0x8a, 0xc7,
    0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]

set_option maxRecDepth 8000 in
/-- The stream decodes to the nine bytes. -/
example : decodeFramesList framedDigits =
    .ok [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] := rfl

/-- The encoder writes the same stream, byte for byte. -/
example :
    (encodeFramesLiteral ⟨#[0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39]⟩).data.toList =
      framedDigits := by
  decide +kernel

set_option maxRecDepth 20000 in
/-- 32 zero bytes in one compressed chunk, as `python-snappy` frames them.

The block is the length 32, a literal of one zero byte, and a copy of 31 bytes from 1 byte back.
-/
example : decodeFramesList
    [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59,
      0x00, 0x0a, 0x00, 0x00, 0xfa, 0xff, 0xd7, 0x0f,
      0x20, 0x00, 0x00, 0x7a, 0x01, 0x00] = .ok (List.replicate 32 0) := rfl

/-- The empty data: the encoder writes the stream identifier alone, which decodes to nothing. -/
example : (encodeFramesLiteral ByteArray.empty).data.toList = streamIdentifier ∧
    decodeFramesList streamIdentifier = .ok [] :=
  ⟨by decide +kernel, rfl⟩

/-- A second stream identifier, then a padding chunk and a reserved skippable chunk, add nothing. -/
example : decodeFramesList (streamIdentifier ++ streamIdentifier ++
    [0xfe, 0x02, 0x00, 0x00, 0x00, 0x00, 0x80, 0x01, 0x00, 0x00, 0x41]) = .ok [] := rfl

/-- No bytes at all. -/
example : decodeFramesList [] = .error .missingStreamIdentifier := rfl

/-- An uncompressed chunk first, without the stream identifier. -/
example : decodeFramesList (framedDigits.drop 10) = .error .missingStreamIdentifier := rfl

/-- A stream identifier chunk that holds `sNaPpX`. -/
example : decodeFramesList [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x58] =
    .error .badStreamIdentifier := rfl

/-- A stream that ends after two bytes of a chunk header. -/
example : decodeFramesList (streamIdentifier ++ [0x01, 0x0d]) = .error .headerTruncated := rfl

/-- A chunk that declares 13 bytes, with 12 left. -/
example : decodeFramesList (framedDigits.dropLast) = .error .chunkPastEnd := rfl

/-- An uncompressed chunk of three bytes, too short for its checksum. -/
example : decodeFramesList (streamIdentifier ++ [0x01, 0x03, 0x00, 0x00, 0x00, 0x00, 0x00]) =
    .error .checksumTruncated := rfl

set_option maxRecDepth 8000 in
/-- The digits chunk with its last checksum byte changed from `c7` to `c6`. -/
example : decodeFramesList (framedDigits.set 17 0xc6) =
    .error (.checksumMismatch 0xc68ab0e5 0xc78ab0e5) := rfl

/-- A compressed chunk whose block declares 65537 bytes. -/
example : decodeFramesList (streamIdentifier ++
    [0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x81, 0x80, 0x04]) =
    .error (.chunkTooLarge 65537) := rfl

/-- A compressed chunk whose block starts with a copy. -/
example : decodeFramesList (streamIdentifier ++
    [0x00, 0x07, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x01, 0x01]) =
    .error (.block (.copyOffsetTooLarge 1)) := rfl

/-- A chunk of type `0x02`, the first reserved unskippable type. -/
example : decodeFramesList (streamIdentifier ++ [0x02, 0x00, 0x00, 0x00]) =
    .error (.reservedUnskippable 0x02) := rfl

end EthLib.Networking.Proofs.Snappy.Frame
