module

public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Proofs.Snappy.Block

/-!
# `Networking.Proofs.Gossip.Payload`

Properties of the size limits on gossip, and of the gossipsub parameters.

- The worst-case compression of the payload cap is `32 + n + n / 6` bytes, with no overflow.
- The payload decoder accepts exactly the data within that length which decompresses to a
  payload within the cap and the bound of its type.
- It rejects data above either bound.
- It rejects a payload length above the bounds from the preamble alone, before it decompresses.
- The mesh bounds and the message cache windows are ordered.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Payload

open EthLib.Networking.Gossip
open EthLib.Networking.ReqResp (MAX_PAYLOAD_SIZE maxCompressedLen)

/-- The worst-case compression of the payload cap fits 64 bits: `32 + n + n / 6` bytes. -/
theorem maxCompressedLen_maxPayloadSize :
    maxCompressedLen MAX_PAYLOAD_SIZE =
      .ok (UInt64.ofNat (32 + MAX_PAYLOAD_SIZE.toNat + MAX_PAYLOAD_SIZE.toNat / 6)) := by
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
