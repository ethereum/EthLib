module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Networking.Gossip.Parameters
public import EthLib.Networking.Gossip.Payload
public import EthLib.Networking.Proofs.Snappy.Block
public import EthLib.Networking.Proofs.Snappy.CompressSize
import EthLib.Base.Proofs.CodeInjective

/-!
# `Networking.Proofs.Gossip.Payload`

Properties of the size limits on gossip, and of the gossipsub parameters.

Most theorems assume a payload cap of at most the largest Snappy block, `2^32 - 1` bytes.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.Payload

open EthLib.Networking.Gossip
open EthLib.Networking.ReqResp (maxCompressedLen maxMessageSize)

/-- Within the largest Snappy block, `32 + n + n / 6 + k` fits 64 bits for `k ≤ 1024`. -/
private theorem toNat_ofNat_compressed {maxPayloadSize : UInt64}
    (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength) {k : Nat} (hk : k ≤ 1024) :
    (UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 + k)).toNat =
      32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 + k := by
  unfold Snappy.maxUncompressedLength at hcap
  rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]

/-- The worst-case compression of the payload cap fits 64 bits: `32 + n + n / 6` bytes. -/
theorem maxCompressedLen_maxPayloadSize {maxPayloadSize : UInt64}
    (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength) :
    maxCompressedLen maxPayloadSize =
      .ok (UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6)) := by
  have value := toNat_ofNat_compressed hcap (k := 0) (Nat.zero_le _)
  unfold Snappy.maxUncompressedLength at hcap
  have hadd : (32 + maxPayloadSize).toNat = 32 + maxPayloadSize.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  simp only [maxCompressedLen, Base.Uint64.addChecked, Base.Uint64.divChecked, bind,
    Except.bind]
  rw [ite_eq_left (by simp; omega)]
  dsimp only
  rw [ite_eq_right (by decide)]
  dsimp only
  rw [ite_eq_left (by rw [hadd, UInt64.toNat_div]; simp; omega)]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, hadd, UInt64.toNat_div]
  simp only [Nat.add_zero] at value
  rw [value]
  simp
  omega

/-- The largest gossip message is the worst-case compression of the payload cap plus 1024 bytes.

It is at least 1 MiB, and it fits 64 bits. -/
theorem maxMessageSize_eq {maxPayloadSize : UInt64}
    (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength) :
    maxMessageSize maxPayloadSize =
      .ok (max (UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 + 1024))
        1048576) := by
  have value := toNat_ofNat_compressed hcap (k := 1024) (Nat.le_refl _)
  simp only [maxMessageSize, maxCompressedLen_maxPayloadSize hcap, bind, Except.bind,
    Base.Uint64.addChecked]
  have value0 := toNat_ofNat_compressed hcap (k := 0) (Nat.zero_le _)
  simp only [Nat.add_zero] at value0
  unfold Snappy.maxUncompressedLength at hcap
  have fits : (UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6)).toNat +
      (1024 : UInt64).toNat < 2 ^ 64 := by
    rw [value0]; simp; omega
  rw [ite_eq_left fits]
  have sum : UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6) + 1024 =
      UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 + 1024) := by
    apply UInt64.toNat_inj.mp
    rw [Base.Uint64.toNat_add_of_lt fits, value0, value]
    rfl
  rw [sum]
  rfl

/-- The decoder accepts data exactly when it fits the worst-case compression of the payload cap.

It must also decompress to a payload within the cap and the bound of its type. -/
theorem decodePayload_eq_ok_iff {maxPayloadSize typeBound : UInt64} {data payload : ByteArray}
    (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength) :
    decodePayload maxPayloadSize typeBound data = .ok payload ↔
      data.size ≤ 32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 ∧
      Snappy.decompress data = .ok payload ∧
      payload.size ≤ (min typeBound maxPayloadSize).toNat := by
  have cap : (UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6)).toNat =
      32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 := by
    simpa using toNat_ofNat_compressed hcap (k := 0) (Nat.zero_le _)
  unfold decodePayload
  simp only [maxCompressedLen_maxPayloadSize hcap, Except.mapError, bind, Except.bind, cap]
  by_cases long : 32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 < data.size
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
      by_cases over : (min typeBound maxPayloadSize).toNat < decoded.size
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
theorem size_add_le_maxMessageSize_of_decodePayload {maxPayloadSize typeBound : UInt64}
    {data payload : ByteArray} (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength)
    (h : decodePayload maxPayloadSize typeBound data = .ok payload) :
    ∃ limit, maxMessageSize maxPayloadSize = .ok limit ∧ data.size + 1024 ≤ limit.toNat := by
  refine ⟨_, maxMessageSize_eq hcap, ?_⟩
  have within := (decodePayload_eq_ok_iff hcap).mp h |>.1
  have value := toNat_ofNat_compressed hcap (k := 1024) (Nat.le_refl _)
  rw [Base.Uint64.toNat_max, value]
  omega

/-- The decoder accepts the block of the compressor for a payload exactly when the payload fits.

It fits when it is within the payload cap and the bound of its type.

The block then takes at most `32 + n + n / 6` bytes, within the worst-case compression of the cap.
-/
theorem decodePayload_compress_eq_ok_iff {maxPayloadSize typeBound : UInt64} {payload : ByteArray}
    (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength) :
    decodePayload maxPayloadSize typeBound (Snappy.compress payload) = .ok payload ↔
      payload.size ≤ (min typeBound maxPayloadSize).toNat := by
  refine ⟨fun h => ((decodePayload_eq_ok_iff hcap).mp h).2.2, fun within => ?_⟩
  have hle : (min typeBound maxPayloadSize).toNat ≤ maxPayloadSize.toNat :=
    UInt64.le_iff_toNat_le.mp (Std.min_le_right)
  have hmax : payload.size ≤ Snappy.maxUncompressedLength := by omega
  refine (decodePayload_eq_ok_iff hcap).mpr
    ⟨?_, Proofs.Snappy.Compress.decompress_compress hmax, within⟩
  have := Proofs.Snappy.CompressSize.size_compress_le payload
  omega

/-- Data longer than the worst-case compression of the payload cap is rejected. -/
theorem decodePayload_compressed_too_long {maxPayloadSize typeBound : UInt64} {data : ByteArray}
    (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength)
    (long : 32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 < data.size) :
    ∀ payload, decodePayload maxPayloadSize typeBound data ≠ .ok payload := fun _ accepted =>
  absurd ((decodePayload_eq_ok_iff hcap).mp accepted).1 (Nat.not_le.mpr long)

/-- A payload above the payload cap or the bound of its type is rejected. -/
theorem decodePayload_payload_too_long {maxPayloadSize typeBound : UInt64}
    {data payload : ByteArray} (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength)
    (decompressed : Snappy.decompress data = .ok payload)
    (long : (min typeBound maxPayloadSize).toNat < payload.size) :
    ∀ other, decodePayload maxPayloadSize typeBound data ≠ .ok other := fun other accepted => by
  obtain ⟨_, same, within⟩ := (decodePayload_eq_ok_iff hcap).mp accepted
  rw [decompressed] at same
  cases same
  omega

/-- A payload whose preamble declares a length above the bounds is rejected unread.

The result does not depend on the rest of the data, so nothing is decompressed. -/
theorem decodePayload_declared_too_long {maxPayloadSize typeBound : UInt64} {data : ByteArray}
    {declared : Nat} (hcap : maxPayloadSize.toNat ≤ Snappy.maxUncompressedLength)
    (short : data.size ≤ 32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6)
    (hd : Snappy.declaredLength data = .ok declared)
    (long : (min typeBound maxPayloadSize).toNat < declared) :
    decodePayload maxPayloadSize typeBound data =
      .error (.payloadTooLong declared (min typeBound maxPayloadSize).toNat) := by
  have cap : (UInt64.ofNat (32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6)).toNat =
      32 + maxPayloadSize.toNat + maxPayloadSize.toNat / 6 := by
    simpa using toNat_ofNat_compressed hcap (k := 0) (Nat.zero_le _)
  unfold decodePayload
  simp only [maxCompressedLen_maxPayloadSize hcap, Except.mapError, bind, Except.bind, cap,
    Nat.not_lt.mpr short, ite_false, hd, long, ite_true, throw, throwThe, MonadExceptOf.throw]

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Gossip.PayloadError.code_injective
    (e₁ e₂ : PayloadError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective PayloadError.code

/-- The gossipsub parameters exist exactly when two epochs in milliseconds are below 2^64. -/
theorem gossipsubParameters_isOk_iff (slotDurationMs slotsPerEpoch : UInt64) :
    (∃ p, gossipsubParameters slotDurationMs slotsPerEpoch = .ok p) ↔
      slotDurationMs.toNat * slotsPerEpoch.toNat * 2 < 2 ^ 64 := by
  simp only [gossipsubParameters, bind, Except.bind]
  cases h1 : Base.Uint64.mulChecked slotDurationMs slotsPerEpoch with
  | error e =>
    -- The product of one epoch already overflows, so twice it does too.
    have : ¬ slotDurationMs.toNat * slotsPerEpoch.toNat < 2 ^ 64 := fun h => by
      simp [Base.Uint64.mulChecked_of_lt h] at h1
    simp only [reduceCtorEq, exists_false, false_iff]
    omega
  | ok epochMs =>
    obtain ⟨-, he⟩ := Base.Uint64.mulChecked_ok_iff.mp h1
    simp only
    cases h2 : Base.Uint64.mulChecked epochMs 2 with
    | error e =>
      -- Twice the epoch overflows.
      have : ¬ epochMs.toNat * (2 : UInt64).toNat < 2 ^ 64 := fun h => by
        simp [Base.Uint64.mulChecked_of_lt h] at h2
      simp only [reduceCtorEq, exists_false, false_iff]
      simp only [UInt64.reduceToNat, he] at this
      omega
    | ok twoEpochsMs =>
      obtain ⟨hlt, -⟩ := Base.Uint64.mulChecked_ok_iff.mp h2
      simp only [UInt64.reduceToNat, he] at hlt
      simpa [pure, Except.pure] using hlt

/-- When the parameters exist, a seen message ID lasts two epochs, in whole seconds.

That lifetime is never a wrapped value. -/
theorem gossipsubParameters_seen_ttl {slotDurationMs slotsPerEpoch : UInt64}
    {p : GossipsubParameters} (h : gossipsubParameters slotDurationMs slotsPerEpoch = .ok p) :
    p.seen_ttl = slotDurationMs.toNat * slotsPerEpoch.toNat * 2 / 1000 := by
  simp only [gossipsubParameters, bind, Except.bind] at h
  cases h1 : Base.Uint64.mulChecked slotDurationMs slotsPerEpoch with
  | error e => simp [h1] at h
  | ok epochMs =>
    cases h2 : Base.Uint64.mulChecked epochMs 2 with
    | error e => simp [h1, h2] at h
    | ok twoEpochsMs =>
      simp only [h1, h2, pure, Except.pure, Except.ok.injEq] at h
      subst h
      obtain ⟨-, he⟩ := Base.Uint64.mulChecked_ok_iff.mp h1
      obtain ⟨-, htwo⟩ := Base.Uint64.mulChecked_ok_iff.mp h2
      simp [UInt64.toNat_div, htwo, he]

/-- The mesh bounds are ordered: `D_low ≤ D ≤ D_high`, and gossip goes to `D_lazy` peers. -/
theorem gossipsubParameters_mesh {slotDurationMs slotsPerEpoch : UInt64} {p : GossipsubParameters}
    (h : gossipsubParameters slotDurationMs slotsPerEpoch = .ok p) :
    p.D_low ≤ p.D ∧ p.D ≤ p.D_high ∧ 0 < p.D_lazy := by
  simp only [gossipsubParameters, bind, Except.bind] at h
  split at h <;> try split at h
  all_goals first | cases h | skip
  all_goals simp_all

/-- The message cache windows are ordered.

The gossip windows are at most the history windows.

So a node tells peers only of messages that it still keeps whole. -/
theorem gossipsubParameters_mcache {slotDurationMs slotsPerEpoch : UInt64}
    {p : GossipsubParameters} (h : gossipsubParameters slotDurationMs slotsPerEpoch = .ok p) :
    p.mcache_gossip ≤ p.mcache_len := by
  simp only [gossipsubParameters, bind, Except.bind] at h
  split at h <;> try split at h
  all_goals first | cases h | skip
  all_goals simp_all

end EthLib.Networking.Proofs.Gossip.Payload
