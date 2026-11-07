module

public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Proofs.Snappy.Block
public import EthLib.Networking.Proofs.Snappy.CompressSize

/-!
# `Networking.Proofs.Gossip.Payload`

Properties of the size limits on gossip, and of the gossipsub parameters.

- The worst-case compression of the payload cap is `32 + n + n / 6` bytes, with no overflow.
- The largest gossip message is that compression plus 1024 bytes, above the floor of 1 MiB.
- Take data within that length.
  The decoder accepts it exactly when it decompresses to a payload within the cap and type bound.
- It rejects data above either bound.
- Data that it accepts leaves 1024 bytes of the largest gossip message for framing.
- It accepts the block of the compressor for a payload within the cap and its type bound.
- It rejects a payload length above the bounds from the preamble alone, before it decompresses.
- The mesh bounds and the message cache windows are ordered.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Payload

open EthLib.Networking.Gossip
open EthLib.Networking.ReqResp (MAX_PAYLOAD_SIZE maxCompressedLen maxMessageSize)

/-- The worst-case compression of the payload cap fits 64 bits: `32 + n + n / 6` bytes. -/
theorem maxCompressedLen_maxPayloadSize :
    maxCompressedLen MAX_PAYLOAD_SIZE =
      .ok (UInt64.ofNat (32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6)) := by
  rfl

/-- The largest gossip message is the worst-case compression of the payload cap plus 1024 bytes.

That sum is above 1 MiB, so the floor of 1 MiB does not apply, and it fits 64 bits. -/
theorem maxMessageSize_eq :
    maxMessageSize =
      .ok (UInt64.ofNat (32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 + 1024)) := by
  rfl

/-- The decoder accepts exactly the data within both bounds that decompresses. -/
theorem decodePayload_eq_ok_iff {typeBound : UInt64} {data payload : ByteArray} :
    decodePayload typeBound data = .ok payload ↔
      data.size ≤ 32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 ∧
      Snappy.decompress data = .ok payload ∧
      payload.size ≤ (min typeBound MAX_PAYLOAD_SIZE).toNat := by
  have cap : (UInt64.ofNat (32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6)).toNat =
      32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 := by decide
  unfold decodePayload
  simp only [maxCompressedLen_maxPayloadSize, Except.mapError, bind, Except.bind, cap]
  by_cases long : 32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 < data.size
  · simp [long, throw, throwThe, MonadExceptOf.throw, Nat.not_le.mpr long]
  · simp only [long, ite_false, Nat.not_lt.mp long, true_and]
    cases hd : Snappy.decompress data with
    | error e =>
      -- Every path fails: at the preamble check, or at the decompression.
      simp only [reduceCtorEq, false_and, iff_false]
      split <;> (try split) <;> simp [throw, throwThe, MonadExceptOf.throw]
    | ok decoded =>
      -- The preamble declares the length of the decompressed payload.
      rw [Proofs.Snappy.Block.declaredLength_of_decompress hd]
      by_cases over : (min typeBound MAX_PAYLOAD_SIZE).toNat < decoded.size
      · simp only [over, ite_true, throw, throwThe, MonadExceptOf.throw, reduceCtorEq,
          false_iff, not_and, Except.ok.injEq]
        rintro rfl
        omega
      · simp only [over, ite_false, pure, Except.pure, Except.ok.injEq]
        constructor
        · rintro rfl
          exact ⟨rfl, by omega⟩
        · rintro ⟨rfl, _⟩
          rfl

/-- Data that the decoder accepts leaves 1024 bytes of the largest gossip message for framing. -/
theorem size_add_le_maxMessageSize_of_decodePayload {typeBound : UInt64}
    {data payload : ByteArray} (h : decodePayload typeBound data = .ok payload) :
    ∃ limit, maxMessageSize = .ok limit ∧ data.size + 1024 ≤ limit.toNat := by
  refine ⟨_, maxMessageSize_eq, ?_⟩
  have within := (decodePayload_eq_ok_iff.mp h).1
  have value : (UInt64.ofNat (32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 +
      1024)).toNat = 32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 + 1024 := by decide
  omega

/-- The decoder accepts the block of the compressor for a payload exactly when the payload fits.

It fits when it is within the payload cap and the bound of its type.

The block then takes at most `32 + n + n / 6` bytes, within the worst-case compression of the cap.
-/
theorem decodePayload_compress_eq_ok_iff {typeBound : UInt64} {payload : ByteArray} :
    decodePayload typeBound (Snappy.compress payload) = .ok payload ↔
      payload.size ≤ (min typeBound MAX_PAYLOAD_SIZE).toNat := by
  refine ⟨fun h => (decodePayload_eq_ok_iff.mp h).2.2, fun within => ?_⟩
  have capmax : MAX_PAYLOAD_SIZE.toNat ≤ Snappy.maxUncompressedLength := by decide
  have hle : (min typeBound MAX_PAYLOAD_SIZE).toNat ≤ MAX_PAYLOAD_SIZE.toNat :=
    UInt64.le_iff_toNat_le.mp (Std.min_le_right)
  have hmax : payload.size ≤ Snappy.maxUncompressedLength := by omega
  refine decodePayload_eq_ok_iff.mpr ⟨?_, Proofs.Snappy.Compress.decompress_compress hmax, within⟩
  have := Proofs.Snappy.CompressSize.size_compress_le payload
  omega

/-- Data longer than the worst-case compression of the payload cap is rejected. -/
theorem decodePayload_compressed_too_long {typeBound : UInt64} {data : ByteArray}
    (long : 32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 < data.size) :
    ∀ payload, decodePayload typeBound data ≠ .ok payload := fun _ accepted =>
  absurd (decodePayload_eq_ok_iff.mp accepted).1 (Nat.not_le.mpr long)

/-- A payload above the payload cap or the bound of its type is rejected. -/
theorem decodePayload_payload_too_long {typeBound : UInt64} {data payload : ByteArray}
    (decompressed : Snappy.decompress data = .ok payload)
    (long : (min typeBound MAX_PAYLOAD_SIZE).toNat < payload.size) :
    ∀ other, decodePayload typeBound data ≠ .ok other := fun other accepted => by
  obtain ⟨_, same, within⟩ := decodePayload_eq_ok_iff.mp accepted
  rw [decompressed] at same
  cases same
  omega

/-- A payload whose preamble declares a length above the bounds is rejected unread.

The result does not depend on the rest of the data, so nothing is decompressed. -/
theorem decodePayload_declared_too_long {typeBound : UInt64} {data : ByteArray} {declared : Nat}
    (short : data.size ≤ 32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6)
    (hd : Snappy.declaredLength data = .ok declared)
    (long : (min typeBound MAX_PAYLOAD_SIZE).toNat < declared) :
    decodePayload typeBound data =
      .error (.payloadTooLong declared (min typeBound MAX_PAYLOAD_SIZE).toNat) := by
  have cap : (UInt64.ofNat (32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6)).toNat =
      32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6 := by decide
  unfold decodePayload
  simp only [maxCompressedLen_maxPayloadSize, Except.mapError, bind, Except.bind, cap,
    Nat.not_lt.mpr short, ite_false, hd, long, ite_true, throw, throwThe, MonadExceptOf.throw]

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Gossip.PayloadError.code_injective
    (e₁ e₂ : PayloadError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PayloadError.code] at h; exact absurd h (by decide))

/-- The mesh bounds are ordered: `D_low ≤ D ≤ D_high`, and gossip goes to `D_lazy` peers. -/
theorem gossipsubParameters_mesh (slotDurationMs slotsPerEpoch : Nat) :
    let p := gossipsubParameters slotDurationMs slotsPerEpoch
    p.D_low ≤ p.D ∧ p.D ≤ p.D_high ∧ 0 < p.D_lazy := by
  simp [gossipsubParameters]

/-- A node tells peers only of messages that it still keeps whole. -/
theorem gossipsubParameters_mcache (slotDurationMs slotsPerEpoch : Nat) :
    (gossipsubParameters slotDurationMs slotsPerEpoch).mcache_gossip ≤
      (gossipsubParameters slotDurationMs slotsPerEpoch).mcache_len := by
  simp [gossipsubParameters]

end EthLib.Networking.Proofs.Gossip.Payload
