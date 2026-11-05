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

/-- The four bytes of a 32-bit value, such as a checksum, read back as that value. -/
theorem foldr_uintToBytes_four (c : UInt32) :
    Vector.foldr (fun byte acc => byte.toNat + 256 * acc) 0 (uintToBytes 4 c.toNat) = c.toNat :=
  (EthLib.Base.bytesToUint_uintToBytes 4 _).trans (Nat.mod_eq_of_lt (UInt32.toNat_lt _))

/-- An uncompressed chunk of at most 65536 bytes with its own checksum decodes to its data. -/
theorem decodeChunk_uncompressed {data : List UInt8} (h : data.length ≤ maxChunkLength) :
    decodeChunk uncompressedType
        ((uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ data) = .ok data := by
  simp [decodeChunk, verifyChecksum, compressedType, uncompressedType,
    EthLib.Base.bytesToUint_toVector, foldr_uintToBytes_four,
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

/-- A compressed chunk decodes to its data (§4.2).

Its block may be any block that decompresses to at most 65536 bytes.

Its checksum is the one of the decompressed data.
-/
theorem decodeChunk_compressed {block data : List UInt8}
    (hb : decompressList block = .ok data) (hd : data.length ≤ maxChunkLength) :
    decodeChunk compressedType
        ((uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++ block) = .ok data := by
  -- The preamble of a block that decompresses declares the length of its output.
  obtain ⟨rest, hpre⟩ := Block.decompressList_length_eq_declared hb
  simp [decodeChunk, hpre, hb, verifyChecksum, EthLib.Base.bytesToUint_toVector,
    foldr_uintToBytes_four, show ¬ maxChunkLength < data.length by omega]

/-- A compressed chunk whose block is one literal decodes to its data.

So some compressed chunk of each length up to 65536 bytes decodes.
-/
theorem decodeChunk_compressed_compressLiteralList {data : List UInt8}
    (h : data.length ≤ maxChunkLength) :
    decodeChunk compressedType
        ((uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++
          compressLiteralList data) = .ok data :=
  decodeChunk_compressed
    (Block.decompressList_compressLiteralList
      (Nat.le_trans h (by simp [maxChunkLength, maxUncompressedLength]))) h

/-! ## Error codes -/

section

open EthLib.Networking.Snappy

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Snappy.FrameError.code_injective
    (e₁ e₂ : FrameError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [FrameError.code] at h; exact absurd h (by decide))

/-- A frame error never has the code of a block error, so one Python class carries both. -/
theorem _root_.EthLib.Networking.Snappy.FrameError.code_ne_block
    (e : FrameError) (r : SnappyError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [FrameError.code, SnappyError.code] <;> decide

end

end EthLib.Networking.Proofs.Snappy.Frame
