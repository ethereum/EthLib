module

public import EthLib.Consensus.Proofs.ReqResp.ResponseBounds
public import EthLib.Consensus.ReqResp.Chunk
public import EthLib.Networking.Proofs.ReqResp.Encoding

/-!
# `Consensus.Proofs.ReqResp.Chunk`

The decoder of a response chunk finds the fork of the chunk, then decodes at that fork's bounds.

On a chain whose digests identify their forks, that is the fork of the digest's epoch.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.Chunk

open Base Networking.ReqResp Serialization.Ssz
open Networking.Proofs.ReqResp.Encoding
open Consensus.Proofs.ReqResp.ResponseBounds

variable {preset : Preset} {config : Config} {genesisValidatorsRoot : Root} {fork : Fork}
  {id : ProtocolId}

/-- Each protocol version that a fork defines has a response type, at the fork of any chunk. -/
theorem responseDesc_isSome (mem : id ∈ protocolIds fork) (chunkFork : Fork) :
    (responseDesc preset config chunkFork id).isSome := by
  obtain ⟨protocol, version⟩ := id
  simp only [protocolIds, List.mem_flatMap, List.mem_map, ProtocolId.mk.injEq] at mem
  obtain ⟨p, -, v, hv, rfl, rfl⟩ := mem
  -- Only status and metadata can lack a type, at a version that no fork defines.
  cases p <;> simp only [responseDesc, Option.isSome_some, Option.isSome_map]
  all_goals
    simp only [ReqRespProtocol.versions] at hv
    split_ifs at hv <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv <;>
      rcases hv with rfl | rfl | rfl <;> rfl

/-- A decoded chunk is one that the chunk decoder accepts at the bounds of the fork it returns.

That fork is the one that the bytes and the fork of the exchange name. -/
theorem decodeChunkAtFork_eq_ok {bs : ByteArray} {chunkFork' : Fork} {chunk : ResponseChunk}
    (h : decodeChunkAtFork preset config genesisValidatorsRoot fork id bs =
      .ok (chunkFork', chunk)) :
    id ∈ protocolIds fork ∧
      responseChunkFork config genesisValidatorsRoot fork id bs = .ok chunkFork' ∧
      id.protocol.firstChunkFork ≤ chunkFork' ∧
      ∃ low high, responseBounds preset config chunkFork' id = some (low, high) ∧
        decodeResponseChunk config.MAX_PAYLOAD_SIZE id.contextBytes low high bs = .ok chunk := by
  unfold decodeChunkAtFork at h
  by_cases mem : (protocolIds fork).contains id
  · simp only [mem, ↓reduceIte, bind, Except.bind] at h
    cases hf : responseChunkFork config genesisValidatorsRoot fork id bs with
    | error e => simp [hf] at h
    | ok found =>
      simp only [hf] at h
      -- The digest names a fork at or after the first one of the protocol.
      by_cases first : id.protocol.firstChunkFork ≤ found
      swap
      · simp [first, throw, throwThe, MonadExceptOf.throw] at h
      simp only [first, ↓reduceIte] at h
      cases hb : responseBounds preset config found id with
      | none => simp [hb, throw, throwThe, MonadExceptOf.throw] at h
      | some bounds =>
        obtain ⟨low, high⟩ := bounds
        cases hd : decodeResponseChunk config.MAX_PAYLOAD_SIZE id.contextBytes low high bs with
        | error e => simp [hb, hd, Except.mapError] at h
        | ok decoded =>
          simp only [hb, hd, Except.mapError, pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨List.contains_iff_mem.mp mem, rfl, first, low, high, hb, hd⟩
  · have notMem : id ∉ protocolIds fork := fun m => mem (List.contains_iff_mem.mpr m)
    simp [notMem, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- A protocol that sends no digest keeps the fork of the exchange. -/
theorem responseChunkFork_of_sendsDigest_false {bs : ByteArray} (h : id.sendsDigest = false) :
    responseChunkFork config genesisValidatorsRoot fork id bs = .ok fork := by
  unfold responseChunkFork
  split <;> simp [h, pure, Except.pure]

/-- An error chunk keeps the fork of the exchange. -/
theorem responseChunkFork_of_error {b : UInt8} {rest : ByteArray}
    (h : ResponseCode.ofByte b ≠ .success) :
    responseChunkFork config genesisValidatorsRoot fork id (⟨#[b]⟩ ++ rest) = .ok fork := by
  unfold responseChunkFork
  split
  · rename_i heq
    simp only [ByteArray.data_append, Array.toList_append, List.cons_append,
      List.nil_append, List.cons.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    simp [h, pure, Except.pure]
  · rfl

/-- The fork of a successful chunk whose digest an epoch other than the far future one has. -/
theorem responseChunkFork_digest {digest : ForkDigest} {rest : ByteArray} {start : Epoch}
    (sends : id.sendsDigest = true)
    (found : forkOfDigest config genesisValidatorsRoot digest = some start)
    (scheduled : start ≠ FAR_FUTURE_EPOCH) :
    responseChunkFork config genesisValidatorsRoot fork id
      (⟨#[ResponseCode.success.toByte]⟩ ++ ⟨digest.toArray⟩ ++ rest) =
      .ok (config.forkAtEpoch start) := by
  obtain ⟨⟨d⟩, hd⟩ := digest
  match d, hd with
  | [d₀, d₁, d₂, d₃], _ =>
    unfold responseChunkFork
    simp [sends, ResponseCode.toByte, ResponseCode.ofByte, found, scheduled, pure, Except.pure]

/-- The fork of a successful chunk fails when only the far future epoch has its digest.

The protocol sends a digest. -/
theorem responseChunkFork_unscheduled {digest : ForkDigest} {rest : ByteArray}
    (sends : id.sendsDigest = true)
    (found : forkOfDigest config genesisValidatorsRoot digest = some FAR_FUTURE_EPOCH) :
    responseChunkFork config genesisValidatorsRoot fork id
      (⟨#[ResponseCode.success.toByte]⟩ ++ ⟨digest.toArray⟩ ++ rest) =
      .error (.bounds (.unscheduledDigest digest)) := by
  obtain ⟨⟨d⟩, hd⟩ := digest
  match d, hd with
  | [d₀, d₁, d₂, d₃], _ =>
    unfold responseChunkFork
    simp [sends, ResponseCode.toByte, ResponseCode.ofByte, found, throw, throwThe,
      MonadExceptOf.throw]

/-- The decoder rejects a successful chunk whose digest only the far future epoch has.

The fork of the exchange defines the protocol version, which sends a digest. -/
theorem decodeChunkAtFork_unscheduled {digest : ForkDigest} {rest : ByteArray}
    (mem : id ∈ protocolIds fork) (sends : id.sendsDigest = true)
    (found : forkOfDigest config genesisValidatorsRoot digest = some FAR_FUTURE_EPOCH) :
    decodeChunkAtFork preset config genesisValidatorsRoot fork id
        (⟨#[ResponseCode.success.toByte]⟩ ++ ⟨digest.toArray⟩ ++ rest) =
      .error (.bounds (.unscheduledDigest digest)) := by
  unfold decodeChunkAtFork
  simp only [List.contains_iff_mem.mpr mem, ↓reduceIte, responseChunkFork_unscheduled sends found,
    bind, Except.bind]

/-- A protocol that sends no digest keeps the fork of the exchange, for every chunk. -/
theorem decodeChunkAtFork_fork_of_sendsDigest_false {bs : ByteArray} {found : Fork}
    {chunk : ResponseChunk} (sends : id.sendsDigest = false)
    (h : decodeChunkAtFork preset config genesisValidatorsRoot fork id bs = .ok (found, chunk)) :
    found = fork := by
  obtain ⟨-, hf, -, -⟩ := decodeChunkAtFork_eq_ok h
  rw [responseChunkFork_of_sendsDigest_false sends] at hf
  cases hf
  rfl

/-- An error chunk keeps the fork of the exchange. -/
theorem decodeChunkAtFork_fork_of_error {bs : ByteArray} {found : Fork} {chunk : ResponseChunk}
    (h : decodeChunkAtFork preset config genesisValidatorsRoot fork id bs = .ok (found, chunk))
    (error : chunk.code ≠ .success) :
    found = fork := by
  obtain ⟨-, hf, -, low, high, -, hd⟩ := decodeChunkAtFork_eq_ok h
  obtain ⟨hc, -, p, rfl, -⟩ := decodeResponseChunk_eq_ok_iff.mp hd
  rw [ByteArray.append_assoc, responseChunkFork_of_error (by rw [hc]; exact error)] at hf
  cases hf
  rfl

/-- On a chain whose digests identify their forks, a successful chunk has the fork of its digest.

That is the fork of the epoch whose digest the chunk carries. -/
theorem decodeChunkAtFork_fork_of_digest {bs : ByteArray} {found : Fork} {chunk : ResponseChunk}
    {epoch : Epoch} {digest : ForkDigest}
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (sends : id.sendsDigest = true)
    (h : decodeChunkAtFork preset config genesisValidatorsRoot fork id bs = .ok (found, chunk))
    (success : chunk.code = .success) (context : chunk.context = ⟨digest.toArray⟩) :
    found = config.forkAtEpoch epoch := by
  obtain ⟨-, hf, -, low, high, -, hd⟩ := decodeChunkAtFork_eq_ok h
  obtain ⟨-, -, p, rfl, -⟩ := decodeResponseChunk_eq_ok_iff.mp hd
  obtain ⟨start, start_found⟩ := Option.isSome_iff_exists.mp (forkOfDigest_isSome computed)
  have recovers := forkOfDigest_recovers identify computed
  rw [start_found] at recovers
  rw [success, context] at hf
  -- The decoder rejects a digest that only the far future epoch has.
  by_cases scheduled : start = FAR_FUTURE_EPOCH
  · rw [scheduled] at start_found
    rw [responseChunkFork_unscheduled sends start_found] at hf
    cases hf
  rw [responseChunkFork_digest sends start_found scheduled] at hf
  cases hf
  simpa using recovers

/-- A served value decodes at the fork of the epoch whose digest it carries, and reads back.

The digests identify the forks, and the value fits the network's cap and the protocol's limit.

The fork of the epoch is at or after the first fork of the protocol.

The epoch is not the far future one, which no slot has. -/
theorem decodeChunkAtFork_response {α : Type} [SszType α] [LawfulSszType α] {a : α}
    {data : ByteArray} {epoch : Epoch} {digest : ForkDigest}
    (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (identify : digestsIdentify config genesisValidatorsRoot = true)
    (computed : computeForkDigest config genesisValidatorsRoot epoch = .ok digest)
    (mem : id ∈ protocolIds fork) (sends : id.sendsDigest = true)
    (first : id.protocol.firstChunkFork ≤ config.forkAtEpoch epoch)
    (scheduled : epoch ≠ FAR_FUTURE_EPOCH)
    (h : responseDesc preset config (config.forkAtEpoch epoch) id = some (SszType.desc α))
    (wrote : SszType.serialize a = .ok data) (within : data.size ≤ config.MAX_PAYLOAD_SIZE.toNat)
    (hlimit : ∀ limit, id.protocol.sizeLimit preset config (config.forkAtEpoch epoch) =
      some limit → data.size ≤ limit.toNat) :
    decodeChunkAtFork preset config genesisValidatorsRoot fork id
        (encodeResponseChunk ⟨.success, ⟨digest.toArray⟩, data⟩) =
      .ok (config.forkAtEpoch epoch, ⟨.success, ⟨digest.toArray⟩, data⟩) ∧
      SszType.deserialize α data = .ok a := by
  obtain ⟨start, low, high, found, same, bounds, decoded, read⟩ :=
    decodeResponseChunk_forkOfDigest hcap identify computed h wrote within hlimit
  have four : id.contextBytes = 4 := by simp [ProtocolId.contextBytes, sends]
  -- The epoch found is at or before the epoch, so it is not the far future one either.
  have early : start ≠ FAR_FUTURE_EPOCH := by
    rintro rfl
    have le := forkOfDigest_le computed found
    have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have below : epoch.toNat < 2 ^ 64 := epoch.toNat_lt_size
    rw [UInt64.le_iff_toNat_le, far] at le
    apply scheduled
    apply UInt64.toNat_inj.mp
    rw [far]
    omega
  refine ⟨?_, read⟩
  unfold decodeChunkAtFork
  -- The chunk is the code of a success, then the digest, then the payload.
  have bytes : encodeResponseChunk ⟨.success, ⟨digest.toArray⟩, data⟩ =
      ⟨#[ResponseCode.success.toByte]⟩ ++ ⟨digest.toArray⟩ ++ encodePayload data := rfl
  rw [bytes] at decoded ⊢
  simp only [List.contains_iff_mem.mpr mem, ↓reduceIte,
    responseChunkFork_digest sends found early, same ▸ bounds, four, decoded, bind, Except.bind,
    Except.mapError, pure, Except.pure, same, first]

/-- The payload of a successful chunk is within the bounds of the type of its fork. -/
theorem withinBounds_of_decodeChunkAtFork {bs : ByteArray} {found : Fork} {chunk : ResponseChunk}
    {shape : Desc} (hcap : config.MAX_PAYLOAD_SIZE.toNat < 2 ^ 63)
    (h : decodeChunkAtFork preset config genesisValidatorsRoot fork id bs = .ok (found, chunk))
    (success : chunk.code = .success) (typed : responseDesc preset config found id = some shape) :
    shape.minSize ≤ chunk.payload.size ∧
      ∀ bound, shape.maxSize = some bound → chunk.payload.size ≤ bound := by
  obtain ⟨-, -, -, low, high, bounds, decoded⟩ := decodeChunkAtFork_eq_ok h
  exact withinBounds_of_decodeResponseChunk hcap typed bounds decoded success

end EthLib.Consensus.Proofs.ReqResp.Chunk
