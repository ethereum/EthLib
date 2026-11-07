module

public import EthLib.Networking.Proofs.Snappy.Frame
public import EthLib.Networking.Snappy.FrameEncode

/-!
# `Networking.Proofs.Snappy.FrameEncode`

The stream that compresses decodes back to its data, against `framing_format.txt`:

<https://github.com/google/snappy/blob/7406111ac4ae539ea0db8b7ea2dc76730cd957f4/framing_format.txt>

- A chunk of at most 65536 bytes, in the shorter of its two forms, decodes to its data (§4.2, §4.3).
- The chunks of a stream decode to the data they were cut from.
- Two streams, one after the other, decode to their two pieces of data in turn.
- The stream is never longer than the stream of uncompressed chunks.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.FrameEncode

open EthLib.Base (uintToBytes)
open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Frame

/-! ## One chunk -/

/-- A chunk of at most 65536 bytes, in its shorter form, is a header and a body that decodes to it.
-/
theorem dataChunk_spec {data : List UInt8} (h : data.length ≤ maxChunkLength) :
    ∃ (type : UInt8) (body : List UInt8), body.length < 2 ^ 24 ∧
      dataChunk data = type :: (uintToBytes 3 body.length).toList ++ body ∧
      decodeChunk type body = .ok data := by
  unfold dataChunk
  split
  · rename_i hlt
    refine ⟨compressedType,
      (uintToBytes 4 (maskedCrc ⟨data.toArray⟩).toNat).toList ++
        (compress ⟨data.toArray⟩).data.toList, ?_, ?_, decodeChunk_compressed_compress h⟩
    · simp only [compressedChunk, uncompressedChunk, List.length_append, List.length_cons,
        Vector.length_toList, maxChunkLength] at hlt h ⊢
      omega
    · simp only [compressedChunk, List.length_append, Vector.length_toList]
      simp [List.append_assoc, Nat.add_comm]
  · exact uncompressedChunk_spec h

/-- A chunk in its shorter form is no longer than the uncompressed chunk. -/
theorem length_dataChunk_le (data : List UInt8) :
    (dataChunk data).length ≤ (uncompressedChunk data).length := by
  unfold dataChunk
  split <;> omega

/-! ## The stream -/

/-- The stream of the encoder decodes back to the data. -/
theorem decodeFrames_encodeFrames (d : ByteArray) : decodeFrames (encodeFrames d) = .ok d := by
  simp only [decodeFrames, encodeFrames, decodeFramesList_streamIdentifier]
  -- The data length is the byte array's size.
  have hn : d.data.toList.length ≤ d.size := Nat.le_of_eq Array.length_toList
  rw [decodeChunks_encodeChunks (chunk := dataChunk) (fun _ h => dataChunk_spec h) _ hn
    (by omega)]
  rfl

/-- Two streams of the encoder, one after the other, decode to their two pieces of data in turn. -/
theorem decodeFrames_encodeFrames_append (d e : ByteArray) :
    decodeFrames (encodeFrames d ++ encodeFrames e) = .ok (d ++ e) :=
  decodeFrames_append (decodeFrames_encodeFrames d) (decodeFrames_encodeFrames e)

/-! ## The size -/

/-- The chunks of the encoder are no longer than the uncompressed chunks of the same data. -/
theorem length_encodeChunks_le (data : List UInt8) (fuel : Nat) :
    (encodeChunks dataChunk data fuel).length ≤
      (encodeChunks uncompressedChunk data fuel).length := by
  induction fuel generalizing data with
  | zero => cases data <;> simp [encodeChunks]
  | succ fuel ih =>
      cases data with
      | nil => simp [encodeChunks]
      | cons b bs =>
          have hle := length_dataChunk_le ((b :: bs).take maxChunkLength)
          have := ih ((b :: bs).drop maxChunkLength)
          simp only [encodeChunks, List.length_append]
          omega

/-- The stream of the encoder is no longer than the stream of uncompressed chunks. -/
theorem size_encodeFrames_le (d : ByteArray) :
    (encodeFrames d).size ≤ (encodeFramesLiteral d).size := by
  have := length_encodeChunks_le d.data.toList d.size
  simp only [encodeFrames, encodeFramesLiteral, ByteArray.size, List.size_toArray,
    List.length_append] at this ⊢
  omega

end EthLib.Networking.Proofs.Snappy.FrameEncode
