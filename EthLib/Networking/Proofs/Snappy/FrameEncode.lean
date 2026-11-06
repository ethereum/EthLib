module

public import EthLib.Networking.Proofs.Snappy.Frame
public import EthLib.Networking.Snappy.FrameEncode

/-!
# `Networking.Proofs.Snappy.FrameEncode`

The stream that compresses decodes back to its data, against `framing_format.txt`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt>

- A chunk of at most 65536 bytes, in the shorter of its two forms, decodes to its data (§4.2, §4.3).
- The chunks of a stream decode to the data they were cut from.
- The stream is never longer than the stream of uncompressed chunks.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.FrameEncode

open EthLib.Base (uintToBytes)
open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Frame

/-! ## One chunk -/

/-- A chunk of at most 65536 bytes, in its shorter form, is one chunk that decodes to the data.

It is also no longer than the uncompressed chunk.
-/
theorem dataChunk_spec {data : List UInt8} (h : data.length ≤ maxChunkLength) :
    ∃ (type : UInt8) (body : List UInt8), body.length < 2 ^ 24 ∧
      dataChunk data = type :: (uintToBytes 3 body.length).toList ++ body ∧
      decodeChunk type body = .ok data ∧
      (dataChunk data).length ≤ (uncompressedChunk data).length := by
  unfold dataChunk
  split
  · rename_i hlt
    refine ⟨compressedType,
      (uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++
        (compress ⟨data.toArray⟩).data.toList, ?_, ?_,
      decodeChunk_compressed_compress h, Nat.le_of_lt hlt⟩
    · simp only [compressedChunk, uncompressedChunk, List.length_append, List.length_cons,
        Vector.length_toList, maxChunkLength] at hlt h ⊢
      omega
    · simp only [compressedChunk, List.length_append, Vector.length_toList]
      simp [List.append_assoc, Nat.add_comm]
  · rename_i hge
    refine ⟨uncompressedType, _, ?_, ?_, decodeChunk_uncompressed h, Nat.le_refl _⟩
    · simp only [maxChunkLength] at h
      simp only [List.length_append, Vector.length_toList]
      omega
    · rw [uncompressedChunk_eq]

/-! ## The stream -/

/-- The chunks of the encoder decode back to the data, given enough fuel on both sides. -/
theorem decodeChunks_encodeChunks (data : List UInt8) {n fuel : Nat}
    (hn : data.length ≤ n) (hfuel : (encodeChunks data n).length ≤ fuel) :
    decodeChunks (encodeChunks data n) fuel = .ok data := by
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
          let tail := encodeChunks ((b :: bs).drop maxChunkLength) n
          have henc : encodeChunks (b :: bs) (n + 1) = dataChunk chunk ++ tail := rfl
          have hchunk : chunk.length ≤ maxChunkLength := List.length_take_le _ _
          obtain ⟨type, body, hbl, hdc, hdec, _⟩ := dataChunk_spec hchunk
          rw [henc, hdc] at hfuel ⊢
          simp only [List.length_append, List.length_cons, Vector.length_toList] at hfuel
          obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [decodeChunks_chunk_ok tail fuel hbl hdec]
          rw [ih _ (by simp [maxChunkLength] at hn ⊢; omega) (show tail.length ≤ fuel by omega)]
          simp [Except.map, chunk]

/-- The stream of the encoder decodes back to the data. -/
theorem decodeFrames_encodeFrames (d : ByteArray) : decodeFrames (encodeFrames d) = .ok d := by
  simp only [decodeFrames, encodeFrames, decodeFramesList_streamIdentifier]
  -- The data length is the byte array's size.
  have hn : d.data.toList.length ≤ d.size := Nat.le_of_eq Array.length_toList
  rw [decodeChunks_encodeChunks _ hn (by omega)]
  rfl

/-! ## The size -/

/-- The chunks of the encoder are no longer than the uncompressed chunks of the same data. -/
theorem length_encodeChunks_le (data : List UInt8) (fuel : Nat) :
    (encodeChunks data fuel).length ≤ (encodeChunksLiteral data fuel).length := by
  induction fuel generalizing data with
  | zero => cases data <;> simp [encodeChunks, encodeChunksLiteral]
  | succ fuel ih =>
      cases data with
      | nil => simp [encodeChunks, encodeChunksLiteral]
      | cons b bs =>
          have hchunk : ((b :: bs).take maxChunkLength).length ≤ maxChunkLength :=
            List.length_take_le _ _
          obtain ⟨_, _, _, _, _, hle⟩ := dataChunk_spec hchunk
          have := ih ((b :: bs).drop maxChunkLength)
          simp only [encodeChunks, encodeChunksLiteral, List.length_append]
          omega

/-- The stream of the encoder is no longer than the stream of uncompressed chunks. -/
theorem size_encodeFrames_le (d : ByteArray) :
    (encodeFrames d).size ≤ (encodeFramesLiteral d).size := by
  have := length_encodeChunks_le d.data.toList d.size
  simp only [encodeFrames, encodeFramesLiteral, ByteArray.size, List.size_toArray,
    List.length_append] at this ⊢
  omega

end EthLib.Networking.Proofs.Snappy.FrameEncode
