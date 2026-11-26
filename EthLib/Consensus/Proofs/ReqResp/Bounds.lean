module

public import EthLib.Consensus.Proofs.ForkDigest
public import EthLib.Consensus.ReqResp.Bounds
public import EthLib.Networking.Proofs.ReqResp.Bounds
public import EthLib.Serialization.Proofs.Ssz.Typed.Class
import EthLib.Base.Proofs.CodeInjective

/-!
# `Consensus.Proofs.ReqResp.Bounds`

The request of a protocol passes the length check of its protocol.

- Take a request payload that decodes at the bounds of its protocol.
  Its length is within the bounds of its SSZ type.
- Take a request that a client serializes, within the payload cap.
  It decodes at those bounds and reads back as itself.
- A received digest names the fork of its first epoch, below the far future epoch.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.Bounds

open EthLib.Consensus
open EthLib.Networking.ReqResp
open EthLib.Networking.Proofs.ReqResp.Bounds
open EthLib.Serialization.Ssz

variable {preset : Preset} {config : Config} {fork : Base.Fork} {id : ProtocolId}

/-- The bounds of a request are the payload bounds of its SSZ type. -/
theorem requestBounds_eq {shape : Desc} (h : requestDesc preset config fork id = some shape) :
    requestBounds preset config fork id = some (payloadBounds config.MAX_PAYLOAD_SIZE shape) := by
  simp [requestBounds, h]

/-- A request payload that decodes at the bounds of its protocol is within its type's bounds. -/
theorem withinBounds_of_decodePayload_request {shape : Desc} {lo hi : UInt64}
    {bs data : ByteArray} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : requestDesc preset config fork id = some shape)
    (hb : requestBounds preset config fork id = some (lo, hi))
    (hd : decodePayload config.MAX_PAYLOAD_SIZE lo hi bs = .ok data) :
    shape.minSize ≤ data.size ∧ ∀ bound, shape.maxSize = some bound → data.size ≤ bound := by
  rw [requestBounds_eq h, Option.some.injEq] at hb
  obtain ⟨rfl, rfl⟩ : (payloadBounds config.MAX_PAYLOAD_SIZE shape).1 = lo ∧
      (payloadBounds config.MAX_PAYLOAD_SIZE shape).2 = hi := by
    rw [hb]
    exact ⟨rfl, rfl⟩
  exact withinBounds_of_decodePayload hcap hd

/-- A request that a client serializes, within the payload cap, decodes at its bounds.

The payload then reads back as the request. -/
theorem decodePayload_request {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : requestDesc preset config fork id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (within : data.size ≤ config.MAX_PAYLOAD_SIZE.toNat) :
    ∃ lo hi, requestBounds preset config fork id = some (lo, hi) ∧
      decodePayload config.MAX_PAYLOAD_SIZE lo hi (encodePayload data) = .ok data ∧
      SszType.deserialize α data = .ok a := by
  refine ⟨(payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc α)).1,
    (payloadBounds config.MAX_PAYLOAD_SIZE (SszType.desc α)).2,
    requestBounds_eq h, ?_, SszType.deserialize_serialize wrote⟩
  have untyped := SszType.serialize_ok_iff.mp wrote
  have := decodePayload_encodePayload_of_serialize hcap (LawfulSszType.fits a) untyped within
  simpa using this

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Consensus.BoundsError.code_injective (e₁ e₂ : BoundsError)
    (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  code_injective BoundsError.code

/-- Every code is above 300, past the codes of custody, subnet and shuffle errors. -/
theorem _root_.EthLib.Consensus.BoundsError.code_gt (e : BoundsError) : 300 < e.code := by
  cases e <;> simp [BoundsError.code]

/-- A digest whose first epoch is below the far future one names the fork of that epoch. -/
theorem forkOfScheduledDigest_of_found {genesisValidatorsRoot : Root} {digest : ForkDigest}
    {start : Epoch} (found : forkOfDigest config genesisValidatorsRoot digest = some start)
    (scheduled : start ≠ FAR_FUTURE_EPOCH) :
    forkOfScheduledDigest config genesisValidatorsRoot digest = .ok (config.forkAtEpoch start) := by
  simp [forkOfScheduledDigest, found, scheduled, pure, Except.pure]

/-- A digest that only the far future epoch has is refused, with the digest. -/
theorem forkOfScheduledDigest_unscheduled {genesisValidatorsRoot : Root} {digest : ForkDigest}
    (found : forkOfDigest config genesisValidatorsRoot digest = some FAR_FUTURE_EPOCH) :
    forkOfScheduledDigest config genesisValidatorsRoot digest =
      .error (.unscheduledDigest digest) := by
  simp [forkOfScheduledDigest, found, throw, throwThe, MonadExceptOf.throw]

/-- A digest that no epoch has is refused, with the digest. -/
theorem forkOfScheduledDigest_unknown {genesisValidatorsRoot : Root} {digest : ForkDigest}
    (found : forkOfDigest config genesisValidatorsRoot digest = none) :
    forkOfScheduledDigest config genesisValidatorsRoot digest = .error (.unknownDigest digest) := by
  simp [forkOfScheduledDigest, found, throw, throwThe, MonadExceptOf.throw]

/-- The fork of a digest is that of its first epoch, which is below the far future one. -/
theorem forkOfScheduledDigest_eq_ok {genesisValidatorsRoot : Root} {digest : ForkDigest}
    {found : Base.Fork}
    (h : forkOfScheduledDigest config genesisValidatorsRoot digest = .ok found) :
    ∃ start, forkOfDigest config genesisValidatorsRoot digest = some start ∧
      start ≠ FAR_FUTURE_EPOCH ∧ config.forkAtEpoch start = found := by
  cases hf : forkOfDigest config genesisValidatorsRoot digest with
  | none => simp [forkOfScheduledDigest_unknown hf] at h
  | some start =>
    by_cases far : start = FAR_FUTURE_EPOCH
    · rw [far] at hf
      simp [forkOfScheduledDigest_unscheduled hf] at h
    · rw [forkOfScheduledDigest_of_found hf far, Except.ok.injEq] at h
      exact ⟨start, rfl, far, h⟩

/-- On a chain whose digests identify their forks, the digest of an epoch names its fork.

The epoch is not the far future one, which no slot has. -/
theorem forkOfScheduledDigest_computed {genesisValidatorsRoot : Root} {epoch : Epoch}
    {digest : ForkDigest} (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (scheduled : epoch ≠ FAR_FUTURE_EPOCH) :
    forkOfScheduledDigest config genesisValidatorsRoot digest = .ok (config.forkAtEpoch epoch) := by
  obtain ⟨start, found⟩ := Option.isSome_iff_exists.mp (forkOfDigest_isSome computed)
  have recovers := forkOfDigest_recovers identify computed
  rw [found, Option.map_some, Option.some.injEq] at recovers
  rw [forkOfScheduledDigest_of_found found (forkOfDigest_ne_farFuture computed scheduled found),
    recovers]

/-- On a chain whose digests identify their forks, the fork of an epoch's digest is its fork. -/
theorem forkOfScheduledDigest_eq_ok_of_computed {genesisValidatorsRoot : Root} {epoch : Epoch}
    {digest : ForkDigest} {found : Base.Fork}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (h : forkOfScheduledDigest config genesisValidatorsRoot digest = .ok found) :
    found = config.forkAtEpoch epoch := by
  obtain ⟨start, hf, -, rfl⟩ := forkOfScheduledDigest_eq_ok h
  have recovers := forkOfDigest_recovers identify computed
  rw [hf, Option.map_some, Option.some.injEq] at recovers
  exact recovers

end EthLib.Consensus.Proofs.ReqResp.Bounds
