module

public import EthLib.Engine.GetPayload
public import EthLib.Engine.Proofs.Json
public import EthLib.Execution.Proofs.Transactions.Network
import EthLib.Base.Proofs.Toolchain.JsonBasic
import EthLib.Engine.Proofs.NewPayload

/-!
# Proofs: `engine_getPayload`

A version returns exactly the forks whose fields are its own.

A returned payload is the payload form of the stored block, at a fork that its version accepts.

The result of a response reads back at its version and its fork.

The payload of a response, sent back to `engine_newPayload`, passes its checks and gives its block.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Cryptography.Kzg
open EthLib.Cryptography.Kzg.Constants
open EthLib.Execution.Blocks (Block MAX_EXTRA_DATA_BYTES)
open EthLib.Execution.Transactions

/-- A version returns a payload of a fork exactly when its fields are those of the fork.

Versions 3 to 6 start at the forks that add their fields: Dencun, Pectra, Fusaka and Glamsterdam.

Each ends where the next one starts, and version 6 ends after Glamsterdam.

Version 2 returns Paris and Shapella, and version 1 Paris alone. -/
theorem acceptsGetPayloadFork_eq_true_iff (version : Nat) (fork : Fork) :
    acceptsGetPayloadFork version fork = true ↔
      1 ≤ version ∧ version ≤ 6 ∧ .paris ≤ fork ∧ fork < .hegota ∧
        (version = 1 → fork < .shapella) ∧ (3 ≤ version ↔ .dencun ≤ fork) ∧
        (4 ≤ version ↔ .pectra ≤ fork) ∧ (5 ≤ version ↔ .fusaka ≤ fork) ∧
        (6 ≤ version ↔ .glamsterdam ≤ fork) := by
  match version with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 => cases fork <;> decide
  | n + 7 => simp [acceptsGetPayloadFork]

/-- Some version returns a payload of a fork exactly when the fork is from Paris to Glamsterdam. -/
theorem exists_acceptsGetPayloadFork_iff (fork : Fork) :
    (∃ version, acceptsGetPayloadFork version fork = true) ↔ .paris ≤ fork ∧ fork < .hegota := by
  constructor
  · rintro ⟨version, h⟩
    obtain ⟨-, -, hLow, hHigh, -⟩ := (acceptsGetPayloadFork_eq_true_iff version fork).mp h
    exact ⟨hLow, hHigh⟩
  · intro ⟨hLow, hHigh⟩
    cases fork <;> first
      | exact absurd hLow (by decide)
      | exact absurd hHigh (by decide)
      | exact ⟨1, rfl⟩
      | exact ⟨2, rfl⟩
      | exact ⟨3, rfl⟩
      | exact ⟨4, rfl⟩
      | exact ⟨5, rfl⟩
      | exact ⟨6, rfl⟩

/-- A missing build process returns unknown payload, before any fork or bundle check. -/
theorem getPayload_eq_error_of_store_eq_none (config : ChainConfig) (setup : TrustedSetup)
    (store : PayloadStore) (version : Nat) (id : PayloadId) (h : store id = none) :
    getPayload config setup store version id = .error (.engine (.unknownPayload id)) := by
  simp [getPayload, h, throw, throwThe, MonadExceptOf.throw]

/-- A returned payload is the stored block's, at its configured fork, with a checked bundle. -/
theorem of_getPayload_eq_ok {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) :
    store id = some r.stored ∧
      config.activeFork r.stored.built.block.header.number
        r.stored.built.block.header.timestamp.toNat = some r.stored.fork ∧
      acceptsGetPayloadFork version r.stored.fork = true ∧
      requestsOfFork r.stored.fork r.stored.built.requests = true ∧
      r.stored.built.blockValue < 2 ^ 256 ∧
      payloadOfBlock r.stored.built.block = some r.payload ∧
      (∃ block, r.stored.blockOfPayload r.payload = .ok block) ∧
      (3 ≤ version → validateBlobs setup r.stored.fork
        (ExecutionPayload.blobVersionedHashes r.stored.built.block.transactions)
        r.stored.bundle.blobs r.stored.bundle.commitments r.stored.bundle.proofs = .ok ()) := by
  have ok_of_ne_error {α ε : Type} {x : Except ε α} (H : ∀ e, x = .error e → False) :
      ∃ a, x = .ok a := by
    cases x with
    | error e => exact (H e rfl).elim
    | ok a => exact ⟨a, rfl⟩
  unfold getPayload at h
  cases hs : store id with
  | none => simp [hs, throw, throwThe, MonadExceptOf.throw] at h
  | some stored =>
    simp only [hs, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      Except.mapError] at h
    repeat' split at h
    all_goals cases h
    · refine ⟨rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ok_of_ne_error ‹_›, fun _ => ?_⟩
      rename_i hb _
      split at hb <;> simp_all
    · exact ⟨rfl, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›, ok_of_ne_error ‹_›, fun hv => absurd hv ‹_›⟩

/-- From version 3, the bundle has the block's hashes in order and its counts.

Its proofs pass the KZG check. -/
theorem getPayload_bundle {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 3 ≤ version) :
    r.stored.bundle.commitments.map versionedHash =
        ExecutionPayload.blobVersionedHashes r.stored.built.block.transactions ∧
      r.stored.bundle.commitments.length = r.stored.bundle.blobs.length ∧
      r.stored.bundle.proofs.length =
        proofCount r.stored.fork r.stored.bundle.blobs.length ∧
      verifyBlobBundle setup r.stored.fork r.stored.bundle.blobs r.stored.bundle.commitments
        r.stored.bundle.proofs = .ok true := by
  obtain ⟨hc, hh, hp⟩ := (validateBlobs_eq_ok_iff _ _ _ _ _ _).mp
    ((of_getPayload_eq_ok h).2.2.2.2.2.2.2 hv)
  obtain ⟨h₁, h₂, h₃⟩ := (blobCountsMatch_iff _ _ _ _ _).mp hc
  exact ⟨(hashesMatch_iff_map (h₁.trans h₂.symm)).mp hh, h₂, h₃, hp⟩

/-- Versions 3 and 4 return exactly one blob proof for each blob. -/
theorem getPayload_blob_proof_count {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 3 ≤ version)
    (hv' : version ≤ 4) :
    r.stored.bundle.proofs.length = r.stored.bundle.blobs.length := by
  have hf := (of_getPayload_eq_ok h).2.2.1
  have hc := (getPayload_bundle h hv).2.2.1
  obtain rfl | rfl : version = 3 ∨ version = 4 := by omega
  all_goals
    simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
    simp only [proofCount, hf] at hc
    split at hc
    · rename_i hle
      exact absurd hle (by decide)
    · exact hc

/-- Versions 5 and 6 return exactly 128 cell proofs for each blob. -/
theorem getPayload_cell_proof_count {config : ChainConfig} {setup : TrustedSetup}
    {store : PayloadStore} {version : Nat} {id : PayloadId} {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 5 ≤ version) :
    r.stored.bundle.proofs.length = CELLS_PER_EXT_BLOB * r.stored.bundle.blobs.length := by
  have hf := (of_getPayload_eq_ok h).2.2.1
  have hfork : .fusaka ≤ r.stored.fork := by
    match version, hv, hf with
    | 5, _, hf =>
      simp only [acceptsGetPayloadFork, Bool.and_eq_true, decide_eq_true_eq] at hf
      exact hf.1
    | 6, _, hf =>
      simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
      rw [hf]; decide
    | n + 7, _, hf => simp [acceptsGetPayloadFork] at hf
  have hc := (getPayload_bundle h (by omega)).2.2.1
  simpa [proofCount, hfork] using hc

/-! ## The other refusals of the method

Each refusal happens when its check fails and every earlier check passes.
-/

variable {config : ChainConfig} {setup : TrustedSetup} {store : PayloadStore} {version : Nat}
  {id : PayloadId} {stored : StoredPayload}

/-- A stored build whose fork is not the one the configuration gives at its block is refused. -/
theorem getPayload_eq_error_of_activeFork_ne (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat ≠ some stored.fork) :
    getPayload config setup store version id =
      .error (.wrongFork stored.fork (config.activeFork stored.built.block.header.number
        stored.built.block.header.timestamp.toNat)) := by
  simp [getPayload, hs, hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A build at a fork that the requested version does not return is refused. -/
theorem getPayload_eq_error_of_acceptsGetPayloadFork_eq_false (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat = some stored.fork)
    (hv : acceptsGetPayloadFork version stored.fork = false) :
    getPayload config setup store version id =
      .error (.engine (.unsupportedFork (some stored.fork))) := by
  simp [getPayload, hs, hf, hv, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A build whose stored requests do not have the shape of its fork is refused. -/
theorem getPayload_eq_error_of_requestsOfFork_eq_false (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat = some stored.fork)
    (hv : acceptsGetPayloadFork version stored.fork = true)
    (hr : requestsOfFork stored.fork stored.built.requests = false) :
    getPayload config setup store version id = .error .requests := by
  simp [getPayload, hs, hf, hv, hr, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A build whose stored block value does not fit in 256 bits is refused. -/
theorem getPayload_eq_error_of_blockValue_ge (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat = some stored.fork)
    (hv : acceptsGetPayloadFork version stored.fork = true)
    (hr : requestsOfFork stored.fork stored.built.requests = true)
    (hb : ¬stored.built.blockValue < 2 ^ 256) :
    getPayload config setup store version id = .error (.blockValue stored.built.blockValue) := by
  simp [getPayload, hs, hf, hv, hr, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

/-- A build whose block has no payload form is refused. -/
theorem getPayload_eq_error_of_payloadOfBlock_eq_none (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat = some stored.fork)
    (hv : acceptsGetPayloadFork version stored.fork = true)
    (hr : requestsOfFork stored.fork stored.built.requests = true)
    (hb : stored.built.blockValue < 2 ^ 256)
    (hp : payloadOfBlock stored.built.block = none) :
    getPayload config setup store version id = .error .noPayload := by
  simp [getPayload, hs, hf, hv, hr, hb, hp, throw, throwThe, MonadExceptOf.throw]

/-- A build whose payload gives no block with the stored block hash is refused, with that error. -/
theorem getPayload_eq_error_of_blockOfPayload_eq_error
    {payload : ExecutionPayload stored.fork} {error : PayloadError}
    (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat = some stored.fork)
    (hv : acceptsGetPayloadFork version stored.fork = true)
    (hr : requestsOfFork stored.fork stored.built.requests = true)
    (hb : stored.built.blockValue < 2 ^ 256)
    (hp : payloadOfBlock stored.built.block = some payload)
    (hh : stored.blockOfPayload payload = .error error) :
    getPayload config setup store version id = .error (.header error) := by
  simp [getPayload, hs, hf, hv, hr, hb, hp, hh, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- From version 3, a build whose bundle fails a count, a hash or the KZG check is refused. -/
theorem getPayload_eq_error_of_validateBlobs_eq_error
    {payload : ExecutionPayload stored.fork} {block : Block stored.fork Transaction}
    {error : NetworkError}
    (hs : store id = some stored)
    (hf : config.activeFork stored.built.block.header.number
      stored.built.block.header.timestamp.toNat = some stored.fork)
    (hv : acceptsGetPayloadFork version stored.fork = true)
    (hr : requestsOfFork stored.fork stored.built.requests = true)
    (hb : stored.built.blockValue < 2 ^ 256)
    (hp : payloadOfBlock stored.built.block = some payload)
    (hh : stored.blockOfPayload payload = .ok block)
    (hversion : 3 ≤ version)
    (hv3 : validateBlobs setup stored.fork
      (ExecutionPayload.blobVersionedHashes stored.built.block.transactions)
      stored.bundle.blobs stored.bundle.commitments stored.bundle.proofs = .error error) :
    getPayload config setup store version id = .error (.bundle error) := by
  simp [getPayload, hs, hf, hv, hr, hb, hp, hh, hversion, hv3, bind, Except.bind,
    Except.mapError]

/-- A JSON value reads as the parameters exactly when it is an array of one payload ID.

The ID is `0x` and 16 lowercase hex digits, two for each of its 8 bytes. -/
theorem getPayloadParams_eq_ok_iff {params : Lean.Json} {id : PayloadId} :
    getPayloadParams params = .ok id ↔ params = .arr #[.str (hexString id.toList)] := by
  cases params with
  | arr items =>
    obtain ⟨xs⟩ := items
    simp only [getPayloadParams, Serialization.JsonRpc.paramsArray]
    match xs with
    | [] => simp [bind, Except.bind, pure, Except.pure]
    | [j] =>
      simp only [Lean.Json.arr.injEq, Array.mk.injEq, List.cons.injEq, and_true,
        ← Serialization.JsonRpc.fixed_false_eq_ok_iff (what := "payloadId")]
      simp [bind, Except.bind, pure, Except.pure]
    | _ :: _ :: _ => simp [bind, Except.bind, pure, Except.pure]
  | _ => simp [getPayloadParams, Serialization.JsonRpc.paramsArray, bind, Except.bind]

/-- The decoder of the parameters reads back the payload ID that the writer writes. -/
theorem getPayloadParams_json (id : PayloadId) :
    getPayloadParams (getPayloadParamsJson id) = .ok id :=
  getPayloadParams_eq_ok_iff.mpr rfl

/-! ## The result -/

/-- A bundle that passes the length rules of a version reads back from its JSON at that version. -/
theorem blobsBundleOfJson_json (version : Nat) (b : BlobsBundle)
    (h : b.lengthsHold version = true) :
    blobsBundleOfJson version (blobsBundleJson b) = .ok b := by
  have hd : [("blobs", Serialization.JsonRpc.listJson (Serialization.JsonRpc.dataJson ·.toList)
      b.blobs), ("commitments", Serialization.JsonRpc.listJson
      (Serialization.JsonRpc.dataJson ·.bytes.toList) b.commitments), ("proofs",
      Serialization.JsonRpc.listJson (Serialization.JsonRpc.dataJson ·.toList) b.proofs)].Pairwise
      fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := Serialization.JsonRpc.fields_mkObj "blobsBundle" hd
    (by simp [Serialization.JsonRpc.listJson])
  have hex : Serialization.JsonRpc.hasExactly fs blobsBundleFields = true :=
    Serialization.JsonRpc.hasExactly_of_perm hp
  unfold blobsBundleOfJson blobsBundleJson
  have r1 := Serialization.JsonRpc.field_of_perm (what := "blobsBundle") hp hd
    (List.mem_cons_self ..)
  have r2 := Serialization.JsonRpc.field_of_perm (what := "blobsBundle") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have r3 := Serialization.JsonRpc.field_of_perm (what := "blobsBundle") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  -- A commitment is written as its bytes, and read back as the bytes it holds.
  have commitments : Serialization.JsonRpc.array "commitments"
      (Serialization.JsonRpc.fixed "commitment" 48)
      (Serialization.JsonRpc.listJson (Serialization.JsonRpc.dataJson ·.bytes.toList)
        b.commitments) = .ok (b.commitments.map (·.bytes)) := by
    have read := Serialization.JsonRpc.array_fixed_listJson "commitments" "commitment"
      (b.commitments.map (·.bytes))
    simpa [Serialization.JsonRpc.listJson, Array.map_map, Function.comp_def] using read
  simp only [hfs, hex, r1, r2, r3, Serialization.JsonRpc.array_fixed_listJson, commitments,
    Json.liftM_ok, bind, Except.bind, ite_true]
  simp [List.map_map, Function.comp_def]
  cases b
  simp_all [pure, Except.pure]

/-- A payload form of a block holds at most 32 bytes of extra data. -/
theorem payloadOfBlock_extraData {fork : Fork} {block : Block fork Transaction}
    {p : ExecutionPayload fork} (h : payloadOfBlock block = some p) :
    p.extraData.size ≤ MAX_EXTRA_DATA_BYTES := by
  unfold payloadOfBlock at h
  split at h
  · exact of_decide_eq_true (Option.filter_eq_some_iff.mp h).2
  · cases h

/-- A bundle that decodes at a version passes the length rules of that version. -/
theorem blobsBundleOfJson_lengths {version : Nat} {j : Lean.Json} {b : BlobsBundle}
    (h : blobsBundleOfJson version j = .ok b) : b.lengthsHold version = true := by
  unfold blobsBundleOfJson at h
  simp only [bind, Except.bind, pure, Except.pure, Json.invalid_eq] at h
  repeat' split at h
  all_goals cases h
  assumption

/-- A bundle reads back from its JSON at a version exactly when it passes its length rules. -/
theorem blobsBundleOfJson_json_iff (version : Nat) (b : BlobsBundle) :
    blobsBundleOfJson version (blobsBundleJson b) = .ok b ↔ b.lengthsHold version = true :=
  ⟨blobsBundleOfJson_lengths, blobsBundleOfJson_json version b⟩

/-- From version 3, the bundle of a response passes the length rules of the bundle it returns.

So the bundle that the execution layer writes is one that the consensus layer accepts. -/
theorem getPayloadResultJson_bundle {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) (hv : 3 ≤ version) :
    r.stored.bundle.lengthsHold (blobsBundleVersion version) = true := by
  have hc := (getPayload_bundle h hv).2.1
  by_cases h5 : 5 ≤ version
  · simp [BlobsBundle.lengthsHold, blobsBundleVersion, BlobsBundle.proofsPerBlob, hc, h5,
      getPayload_cell_proof_count h h5]
  · simp [BlobsBundle.lengthsHold, blobsBundleVersion, BlobsBundle.proofsPerBlob, hc, h5,
      getPayload_blob_proof_count h hv (by omega)]

/-- The payload of a result reads back with its access list and slot, in the form of its fork. -/
private theorem resultPayloadOfJson_payloadJson {fork : Fork} (r : GetPayloadResult fork)
    (extra : r.payload.extraData.size ≤ MAX_EXTRA_DATA_BYTES) (v4 : Bool)
    (hv4 : v4 = true ↔ .glamsterdam ≤ fork) :
    resultPayloadOfJson v4 fork r.payloadJson =
      .ok (r.payload, r.blockAccessList, r.slotNumber) := by
  by_cases hg : Fork.glamsterdam ≤ fork
  · obtain rfl := hv4.mpr hg
    obtain ⟨any, hany, hat⟩ := Json.payloadV4_executionPayloadV4Json r.payload
      (r.blockAccessList hg) (r.slotNumber hg) (Std.le_trans (by decide) hg) extra
    have h1 : Json.since "blockAccessList" (some (r.blockAccessList hg)) =
        .ok r.blockAccessList := Json.since_eq_ok_iff.mpr (by simp [sinceValue, hg])
    have h2 : Json.since "slotNumber" (some (r.slotNumber hg)) = .ok r.slotNumber :=
      Json.since_eq_ok_iff.mpr (by simp [sinceValue, hg])
    simp only [resultPayloadOfJson, GetPayloadResult.payloadJson, hg, dite_true, ite_true, hany,
      hat, Functor.map, Except.map, bind, Except.bind, Option.map, h1, h2, pure, Except.pure]
  · have hf : v4 = false := by simpa [hg] using hv4
    subst hf
    obtain ⟨any, hany, hat⟩ := Json.anyPayload_executionPayloadJson r.payload extra
    have h1 : Json.since "blockAccessList" (none : Option ByteArray) = .ok r.blockAccessList :=
      Json.since_eq_ok_iff.mpr (by simp [sinceValue, hg])
    have h2 : Json.since "slotNumber" (none : Option UInt64) = .ok r.slotNumber :=
      Json.since_eq_ok_iff.mpr (by simp [sinceValue, hg])
    simp only [resultPayloadOfJson, GetPayloadResult.payloadJson, hg, dite_false, hany,
      Bool.false_eq_true, ite_false,
      hat, Functor.map, Except.map, bind, Except.bind, Option.map, h1, h2, pure, Except.pure]

/-- At a fork that a version serves, the payload is of version 4 exactly in version 6.

From version 4, the fork is Pectra or later. -/
private theorem fork_of_accepts {version : Nat} {fork : Fork}
    (hf : acceptsGetPayloadFork version fork = true) :
    (decide (version = 6) = true ↔ .glamsterdam ≤ fork) ∧ (4 ≤ version → .pectra ≤ fork) := by
  match version, hf with
  | 0, hf => simp [acceptsGetPayloadFork] at hf
  | 1, hf =>
    simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
    subst hf; decide
  | 2, hf =>
    simp only [acceptsGetPayloadFork, Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with rfl | rfl <;> decide
  | 3, hf =>
    simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
    subst hf; decide
  | 4, hf =>
    simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
    subst hf; decide
  | 5, hf =>
    simp only [acceptsGetPayloadFork, Bool.and_eq_true, decide_eq_true_eq] at hf
    refine ⟨⟨fun h => absurd h (by decide), fun h => absurd (Nat.lt_of_lt_of_le hf.2 h)
      (Nat.lt_irrefl _)⟩, fun _ => Std.le_trans (by decide) hf.1⟩
  | 6, hf =>
    simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
    subst hf; decide
  | n + 7, hf => simp [acceptsGetPayloadFork] at hf

/-- The payload of a result is an object, so not `null`. -/
private theorem payloadJson_isNull {fork : Fork} (r : GetPayloadResult fork) :
    r.payloadJson.isNull = false := by
  unfold GetPayloadResult.payloadJson Json.executionPayloadV4Json Json.executionPayloadJson
  split <;> exact Base.Toolchain.Json.isNull_mkObj _

/-- The result of a response, written and read back at its version and its fork, is that result.

So the reader gets the payload and each field that the version returns. -/
theorem getPayloadResultOfJson_json {r : GetPayloadResponse}
    (h : getPayload config setup store version id = .ok r) :
    getPayloadResultOfJson version r.stored.fork (getPayloadResultJson (r.result version)) =
      .ok (r.result version) := by
  obtain ⟨-, -, hf, hreq, hbv, hpb, -, -⟩ := of_getPayload_eq_ok h
  have extra := payloadOfBlock_extraData hpb
  have hpay := resultPayloadOfJson_payloadJson (r.result version) extra
  by_cases h1 : version = 1
  · subst h1
    have hg : ¬Fork.glamsterdam ≤ r.stored.fork := by
      simp only [acceptsGetPayloadFork, beq_iff_eq] at hf
      rw [hf]; decide
    have hp := hpay false (by simp [hg])
    have hb : (r.result 1).blockValue = none := rfl
    simp only [getPayloadResultOfJson, getPayloadResultJson, hb, hf, hp, ite_true, bind,
      Except.bind, pure, Except.pure]
    rfl
  have h2 : 2 ≤ version := by
    rcases Nat.lt_or_ge version 2 with hl | hl
    · obtain rfl | rfl : version = 0 ∨ version = 1 := by omega
      · simp [acceptsGetPayloadFork] at hf
      · exact absurd rfl h1
    · exact hl
  have hb : (r.result version).blockValue = some r.stored.built.blockValue := by
    simp [GetPayloadResponse.result, h2]
  obtain ⟨hg6, hpec⟩ := fork_of_accepts hf
  have hp := hpay _ hg6
  have hq := Serialization.JsonRpc.quantity_toDigits "blockValue" hbv
  have hbb : (r.result version).blobsBundle =
      if 3 ≤ version then some r.stored.bundle else none := rfl
  have hso : (r.result version).shouldOverrideBuilder =
      if 3 ≤ version then some r.stored.shouldOverrideBuilder else none := rfl
  have her : (r.result version).executionRequests =
      if 4 ≤ version then some r.stored.built.requests else none := rfl
  -- The pairs of the result object, which hold the fields of its version.
  obtain ⟨L, hL⟩ : ∃ L : List (String × Lean.Json), L =
      [("executionPayload", (r.result version).payloadJson),
        ("blockValue", Serialization.JsonRpc.quantityJson r.stored.built.blockValue)] ++
      ((r.result version).blobsBundle.map fun b => ("blobsBundle", blobsBundleJson b)).toList ++
      ((r.result version).shouldOverrideBuilder.map fun o =>
        ("shouldOverrideBuilder", Lean.Json.bool o)).toList ++
      ((r.result version).executionRequests.map fun rs => ("executionRequests",
        Serialization.JsonRpc.listJson (Serialization.JsonRpc.dataJson ·.data.toList) rs)).toList :=
    ⟨_, rfl⟩
  have hj : getPayloadResultJson (r.result version) = Lean.Json.mkObj L := by
    simp only [getPayloadResultJson, hb, hL]
  have hd : L.Pairwise fun a b => a.1 ≠ b.1 := by
    by_cases h3 : 3 ≤ version <;> by_cases h4 : 4 ≤ version <;> simp [hL, hbb, hso, her, h3, h4]
  have hbn : (blobsBundleJson r.stored.bundle).isNull = false := by
    unfold blobsBundleJson; exact Base.Toolchain.Json.isNull_mkObj _
  have hpres : ∀ p ∈ L, p.2.isNull = false := by
    by_cases h3 : 3 ≤ version <;> by_cases h4 : 4 ≤ version <;>
      simp [hL, hbb, hso, her, h3, h4, hbn, payloadJson_isNull,
        Serialization.JsonRpc.quantityJson, Serialization.JsonRpc.listJson]
  obtain ⟨fs, hfs, hperm⟩ := Serialization.JsonRpc.fields_mkObj "result" hd hpres
  have hex : Serialization.JsonRpc.hasExactly fs (getPayloadResultFields version) = true := by
    have := Serialization.JsonRpc.hasExactly_of_perm hperm
    have hn : L.map Prod.fst = getPayloadResultFields version := by
      by_cases h3 : 3 ≤ version <;> by_cases h4 : 4 ≤ version <;>
        simp [hL, hbb, hso, her, h3, h4, getPayloadResultFields]
    rwa [hn] at this
  have rd : ∀ k v, (k, v) ∈ L → Serialization.JsonRpc.field "result" fs k = .ok v :=
    fun _ _ hm => Serialization.JsonRpc.field_of_perm hperm hd hm
  have r1 := rd "executionPayload" (r.result version).payloadJson (by simp [hL])
  have r2 := rd "blockValue" (Serialization.JsonRpc.quantityJson r.stored.built.blockValue)
    (by simp [hL])
  rw [hj]
  simp only [getPayloadResultOfJson, hf, h1, hfs, hex, r1, r2, hp, hq, Json.liftM_ok, ite_true,
    ite_false, bind, Except.bind, pure, Except.pure]
  by_cases h3 : 3 ≤ version
  · have r3 := rd "blobsBundle" (blobsBundleJson r.stored.bundle) (by simp [hL, hbb, h3])
    have r4 := rd "shouldOverrideBuilder" (.bool r.stored.shouldOverrideBuilder)
      (by simp [hL, hso, h3])
    have hbj := blobsBundleOfJson_json _ _ (getPayloadResultJson_bundle h h3)
    by_cases h4 : 4 ≤ version
    · have r5 := rd "executionRequests" (Serialization.JsonRpc.listJson
        (Serialization.JsonRpc.dataJson ·.data.toList) r.stored.built.requests)
        (by simp [hL, her, h4])
      have hvr : validRequests r.stored.built.requests = true := by
        simpa [requestsOfFork, hpec h4] using hreq
      simp only [h3, h4, r3, r4, r5, hbj, Serialization.JsonRpc.array_bytes_listJson, hvr,
        Json.liftM_ok, ite_true, Functor.map, Except.map, Json.lift, Serialization.JsonRpc.bool,
        Except.mapError, pure, Except.pure]
      simp only [GetPayloadResponse.result, h2, h3, h4, ite_true]
    · simp only [h3, h4, r3, r4, hbj, Json.liftM_ok, ite_true, ite_false, Functor.map,
        Except.map, Json.lift, Serialization.JsonRpc.bool, Except.mapError, pure,
        Except.pure]
      simp only [GetPayloadResponse.result, h2, h3, h4, ite_true, ite_false]
  · have h4 : ¬4 ≤ version := by omega
    simp only [h3, h4, ite_false]
    simp only [GetPayloadResponse.result, h2, h3, h4, ite_true, ite_false]

/-! ## The payload sent back -/

/-- The payload of a response, sent back to `engine_newPayload`, passes the checks of the method.

The stored block must come back from its payload form, with the requests and access list stored.

The version of `engine_newPayload` must take the fork of the build.

From version 5, the parameters hold the access list and the slot of the build with the payload.

From version 3, they hold the versioned hashes of the commitments of the bundle.

From version 3, they also hold the parent beacon block root of the block.

From version 4, they hold the requests of the build.

The checks then give the stored block, at the fork of the build. -/
theorem checkNewPayload_of_getPayload {r : GetPayloadResponse} {version' : Nat}
    (h : getPayload config setup store version id = .ok r)
    (hBlock : r.stored.blockOfPayload r.payload = .ok r.stored.built.block)
    (accepts : acceptsFork version' r.stored.fork = true) :
    checkNewPayload config version' (newPayloadParamsJson version' r.payload
        (if hf : .glamsterdam ≤ r.stored.fork then
          some (r.stored.built.blockAccessList hf, r.stored.built.block.header.slotNumber hf)
        else none)
        (r.stored.bundle.commitments.map versionedHash)
        ((sinceValue r.stored.built.block.header.parentBeaconBlockRoot).getD 0)
        r.stored.built.requests) =
      .ok (.ok ⟨r.stored.fork, accepts, r.stored.built.block⟩) := by
  obtain ⟨-, hActive, hServes, hReq, -, hPay, -, -⟩ := of_getPayload_eq_ok h
  obtain ⟨-, -, -, -, three, four, five, six⟩ :=
    (acceptsFork_eq_true_iff version' r.stored.fork).mp accepts
  obtain ⟨-, -, -, hHegota, -, threeGet, -⟩ :=
    (acceptsGetPayloadFork_eq_true_iff version r.stored.fork).mp hServes
  -- A fork that a version of the request serves comes before Hegotá, so version 6 is not taken.
  have below : version' < 6 :=
    Nat.lt_of_not_le fun hv => absurd (six.mp hv) (Std.not_le.mpr hHegota)
  -- The parameters read back, with the payload at the fork of the build.
  obtain ⟨any, hDecode, hAt⟩ := newPayloadParams_json r.payload
    (if hf : .glamsterdam ≤ r.stored.fork then
      some (r.stored.built.blockAccessList hf, r.stored.built.block.header.slotNumber hf)
    else none)
    (r.stored.bundle.commitments.map versionedHash)
    ((sinceValue r.stored.built.block.header.parentBeaconBlockRoot).getD 0)
    r.stored.built.requests accepts below (payloadOfBlock_extraData hPay)
    (by
      by_cases hf : Fork.glamsterdam ≤ r.stored.fork
      · simpa [hf] using five.mpr hf
      · simpa [hf] using Nat.lt_of_not_le (mt five.mp hf))
  -- The payload has the number and the time of the block, so the fork of the build is active.
  have hCommon := Json.AnyPayload.atFork_common hAt
  obtain ⟨hNumber, hTime⟩ := ExecutionPayload.toBlock_number_timestamp hBlock
  have hActive' : config.activeFork any.common.blockNumber.toNat any.common.timestamp.toNat =
      some r.stored.fork := by
    rw [← hCommon.1, ← hCommon.2.1, ← hNumber, ← hTime]
    exact hActive
  refine checkNewPayload_eq_ok hDecode ?_ hActive' accepts hAt ?_ ?_ ?_ ?_ hBlock ?_
  -- From version 4 the requests are those of the build, which pass their check from Pectra.
  · intro rs e
    by_cases h4 : 4 ≤ version'
    · simp only [h4, ite_true, Option.some.injEq] at e
      subst e
      simpa [requestsOfFork, four.mp h4] using hReq
    · simp [h4] at e
  -- Each field from a later fork is present exactly from its fork, with the value of the block.
  · refine Json.since_eq_ok_iff.mpr ?_
    by_cases hf : Fork.dencun ≤ r.stored.fork <;> simp [sinceValue, hf, three]
  · refine Json.since_eq_ok_iff.mpr ?_
    by_cases hf : Fork.pectra ≤ r.stored.fork <;> simp [sinceValue, hf, four]
  · refine Json.since_eq_ok_iff.mpr ?_
    by_cases hf : Fork.glamsterdam ≤ r.stored.fork <;> simp [sinceValue, hf]
  · refine Json.since_eq_ok_iff.mpr ?_
    by_cases hf : Fork.glamsterdam ≤ r.stored.fork <;> simp [sinceValue, hf]
  -- From version 3 the commitments of the bundle hash to the blob hashes of the block.
  · intro hs e
    by_cases h3 : 3 ≤ version'
    · simp only [h3, ite_true, Option.some.injEq] at e
      subst e
      exact ((getPayload_bundle h (threeGet.mpr (three.mp h3))).1).symm
    · simp [h3] at e

end EthLib.Engine
