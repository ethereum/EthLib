module

public import EthLib.Consensus.RemoteSigningApi.Request
public import EthLib.Consensus.Proofs.BeaconApi.Encoding
public import EthLib.Consensus.Proofs.Containers.Attestation
public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Containers.BuilderApi
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Containers.SyncCommittee
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Container
import EthLib.Base.Proofs.Toolchain.JsonBasic

/-!
# Proofs: the requests of the Remote-signing API read back as written

Every request that the writer writes reads back as the same request.

The field `type` of a document decides the kind of the request that it reads as.

The field `version` of a versioned body decides the version of the request.

A document whose `type` names no kind is refused with that name.
-/

@[expose] public section

namespace EthLib.Consensus.RemoteSigningApi

open Lean Base Serialization.Ssz BeaconApi

instance : LawfulSszType ForkInfo := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType AggregationSlot := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType RandaoReveal := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SyncCommitteeMessageData :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType DepositSigningData :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-! ## Names -/

/-- A version reads back from its name. -/
theorem versionOfName?_versionName (version : ConsensusVersion) :
    versionOfName? (versionName version) = some version := by
  cases version <;> rfl

/-- A name reads as a version only when it is the name of that version. -/
theorem versionName_of_versionOfName? {name : String} {version : ConsensusVersion}
    (h : versionOfName? name = some version) : versionName version = name := by
  simpa using List.find?_some h

/-- A kind of request reads back from its name. -/
theorem RequestType.ofName?_name (type : RequestType) :
    RequestType.ofName? type.name = some type := by
  cases type <;> rfl

/-- A name reads as a kind of request only when it is the name of that kind. -/
theorem RequestType.name_of_ofName? {name : String} {type : RequestType}
    (h : RequestType.ofName? name = some type) : type.name = name := by
  simpa using List.find?_some h

/-! ## The steps of the reader -/

/-- A key whose value the writer wrote from a value reads back as that value. -/
theorem readValue_of_getObjVal? {α : Type} [SszType α] [LawfulSszType α] [ApiSpelling α]
    {document value : Json} {key : String} {x : α} (h : document.getObjVal? key = .ok value)
    (wrote : toApiJson x = .ok value) : readValue α document key = .ok x := by
  simp [readValue, field, h, bind, Except.bind, ofApiJson_toApiJson wrote]

/-- A versioned body that the writer wrote reads back as its version. -/
theorem readVersion_versionedJson (version : ConsensusVersion) {key : String} (data : Json)
    (outer : String) (distinct : key ≠ "version") :
    readVersion (versionedJson version key data) outer = .ok version := by
  have h : (versionedJson version key data).getObjVal? "version" =
      .ok (.str (versionName version)) :=
    getObjVal?_mkObj (by simpa using distinct.symm) (by simp)
  simp [readVersion, field, h, versionOfName?_versionName, bind, Except.bind, pure, Except.pure]

/-- A versioned body that the writer wrote holds its data under its key. -/
theorem versionedJson_getObjVal? (version : ConsensusVersion) {key : String} (data : Json)
    (distinct : key ≠ "version") : (versionedJson version key data).getObjVal? key = .ok data :=
  getObjVal?_mkObj (by simpa using distinct.symm) (by simp)

/-- The signing root that the writer wrote, or left out, reads back. -/
private theorem readSigningRoot_mkObj {pairs : List (String × Json)}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) (signingRoot : Option Root)
    (present : ∀ root, signingRoot = some root →
      ("signingRoot", Json.str (toHex root.toArray)) ∈ pairs)
    (absent : signingRoot = none → "signingRoot" ∉ pairs.map Prod.fst) :
    readSigningRoot (Json.mkObj pairs) = .ok signingRoot := by
  simp [readSigningRoot, readKey_mkObj distinct (write := fun root => .str (toHex root.toArray))
    readRoot_toHex signingRoot present absent, Except.mapError]

/-- The block of a request of the second block kind reads back as written. -/
theorem BlockV2Body.ofJson_toJson {preset : Preset} [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    {body : BlockV2Body preset} {document : Json} (wrote : body.toJson = .ok document) :
    BlockV2Body.ofJson preset document = .ok body := by
  cases body with
  | phase0 block =>
    obtain ⟨j, hj⟩ := toApiJson_total block
    simp only [BlockV2Body.toJson, hj, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at wrote
    subst wrote
    have early : ¬ ConsensusVersion.bellatrix ≤ .phase0 := by decide
    simp [BlockV2Body.ofJson, readVersion_versionedJson, early, bind, Except.bind, pure,
      Except.pure,
      readValue_of_getObjVal? (versionedJson_getObjVal? .phase0 (key := "block") j (by decide)) hj]
  | altair block =>
    obtain ⟨j, hj⟩ := toApiJson_total block
    simp only [BlockV2Body.toJson, hj, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at wrote
    subst wrote
    have early : ¬ ConsensusVersion.bellatrix ≤ .altair := by decide
    simp [BlockV2Body.ofJson, readVersion_versionedJson, early, bind, Except.bind, pure,
      Except.pure,
      readValue_of_getObjVal? (versionedJson_getObjVal? .altair (key := "block") j (by decide)) hj]
  | header version blockHeader =>
    obtain ⟨j, hj⟩ := toApiJson_total blockHeader
    simp only [BlockV2Body.toJson, hj, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at wrote
    subst wrote
    simp [BlockV2Body.ofJson, readVersion_versionedJson, version.2, bind, Except.bind, pure,
      Except.pure,
      readValue_of_getObjVal? (versionedJson_getObjVal? _ (key := "block_header") j (by decide)) hj]

/-! ## The whole request -/

/-- What a document that the writer built for a request with a shared part holds.

Its `type` holds the name, its body key holds the body, and its shared part reads back. -/
private theorem signingDocument {name key : String} {body forkInfo : Json} {signing : Signing}
    (wrote : toApiJson signing.forkInfo = .ok forkInfo)
    (fresh : key ≠ "type" ∧ key ≠ "fork_info" ∧ key ≠ "signingRoot") :
    let document := Json.mkObj
      (("type", .str name) :: (key, body) :: ("fork_info", forkInfo) ::
        signingRootFields signing.signingRoot)
    document.getObjVal? "type" = .ok (.str name) ∧ document.getObjVal? key = .ok body ∧
      readSigning document = .ok signing := by
  obtain ⟨info, signingRoot⟩ := signing
  obtain ⟨t, f, s⟩ := fresh
  have distinct : ((("type", Json.str name) :: (key, body) :: ("fork_info", forkInfo) ::
      signingRootFields signingRoot)).Pairwise fun a b => a.1 ≠ b.1 := by
    cases signingRoot <;> simp [signingRootFields] <;> grind
  refine ⟨getObjVal?_mkObj distinct (by simp), getObjVal?_mkObj distinct (by simp), ?_⟩
  have root : readSigningRoot (Json.mkObj
      (("type", .str name) :: (key, body) :: ("fork_info", forkInfo) ::
        signingRootFields signingRoot)) = .ok signingRoot := by
    refine readSigningRoot_mkObj distinct signingRoot (fun r hr => ?_) (fun hr => ?_)
    · simp [hr, signingRootFields]
    · simp [hr, signingRootFields, Ne.symm s]
  simp [readSigning, root, readValue_of_getObjVal?
    (getObjVal?_mkObj (name := "fork_info") (value := forkInfo) distinct (by simp)) wrote,
    bind, Except.bind, pure, Except.pure]

/-- What a document that the writer built for a request without a shared part holds. -/
private theorem plainDocument {name key : String} {body : Json} {signingRoot : Option Root}
    (fresh : key ≠ "type" ∧ key ≠ "signingRoot") :
    let document := Json.mkObj
      (("type", .str name) :: (key, body) :: signingRootFields signingRoot)
    document.getObjVal? "type" = .ok (.str name) ∧ document.getObjVal? key = .ok body ∧
      readSigningRoot document = .ok signingRoot := by
  obtain ⟨t, s⟩ := fresh
  have distinct : ((("type", Json.str name) :: (key, body) ::
      signingRootFields signingRoot)).Pairwise fun a b => a.1 ≠ b.1 := by
    cases signingRoot <;> simp [signingRootFields] <;> grind
  refine ⟨getObjVal?_mkObj distinct (by simp), getObjVal?_mkObj distinct (by simp), ?_⟩
  refine readSigningRoot_mkObj distinct signingRoot (fun r hr => ?_) (fun hr => ?_)
  · simp [hr, signingRootFields]
  · simp [hr, signingRootFields, Ne.symm s]

/-- The kind that the field `type` of an object names, when it names one. -/
theorem readType_eq_ok_of_getObjVal? {document : Json} {type : RequestType}
    (h : document.getObjVal? "type" = .ok (.str type.name)) : readType document = .ok type := by
  simp [readType, field, h, RequestType.ofName?_name, bind, Except.bind, pure, Except.pure]

/-- An object that the writer built is an object. -/
private theorem mkObj_isObj (pairs : List (String × Json)) : ∃ m, Json.mkObj pairs = .obj m :=
  ⟨_, Toolchain.Json.mkObj_eq pairs⟩

/-- The block of a request of the second block kind is written as an object. -/
theorem BlockV2Body.toJson_isObj {preset : Preset} {body : BlockV2Body preset} {document : Json}
    (wrote : body.toJson = .ok document) : ∃ m, document = .obj m := by
  cases body <;>
  · rename_i value
    cases hj : toApiJson value with
    | error e => simp [BlockV2Body.toJson, hj, bind, Except.bind] at wrote
    | ok j =>
      simp only [BlockV2Body.toJson, hj, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at wrote
      subst wrote
      exact mkObj_isObj _

variable {preset : Preset}

/-- A request with a shared part reads back, when its body reads back from what was written.

The body is written under its key.

The reader must give the request back from any object whose tags and parts read as written. -/
private theorem ofJson_of_signing {request : SigningRequest preset} {key : String}
    {write : Except Err Json} {signing : Signing} {document : Json}
    (hfields : request.fields = (do return (key, ← write) :: (← signingFields signing)))
    (fresh : key ≠ "type" ∧ key ≠ "fork_info" ∧ key ≠ "signingRoot")
    (wrote : request.toJson = .ok document)
    (reads : ∀ m j, write = .ok j → readType (.obj m) = .ok request.type →
      readSigning (.obj m) = .ok signing → (Json.obj m).getObjVal? key = .ok j →
      SigningRequest.ofJson preset (.obj m) = .ok request) :
    SigningRequest.ofJson preset document = .ok request := by
  obtain ⟨f, hf⟩ := toApiJson_total signing.forkInfo
  cases hw : write with
  | error e => simp [SigningRequest.toJson, hfields, hw, bind, Except.bind] at wrote
  | ok j =>
    simp only [SigningRequest.toJson, hfields, signingFields, hw, hf, bind, Except.bind, pure,
      Except.pure, Except.ok.injEq] at wrote
    subst wrote
    obtain ⟨ht, hb, hs⟩ := signingDocument (name := request.type.name) (key := key) (body := j)
      hf fresh
    obtain ⟨m, hm⟩ := mkObj_isObj (("type", .str request.type.name) :: (key, j) ::
      ("fork_info", f) :: signingRootFields signing.signingRoot)
    rw [hm] at ht hb hs ⊢
    exact reads m j hw (readType_eq_ok_of_getObjVal? ht) hs hb

/-- A request without a shared part reads back, when its body reads back from what was written.

The body is written under its key, beside the signing root of the request. -/
private theorem ofJson_of_plain {request : SigningRequest preset} {key : String}
    {write : Except Err Json} {signingRoot : Option Root} {document : Json}
    (hfields : request.fields = (do return (key, ← write) :: signingRootFields signingRoot))
    (fresh : key ≠ "type" ∧ key ≠ "signingRoot")
    (wrote : request.toJson = .ok document)
    (reads : ∀ m j, write = .ok j → readType (.obj m) = .ok request.type →
      readSigningRoot (.obj m) = .ok signingRoot → (Json.obj m).getObjVal? key = .ok j →
      SigningRequest.ofJson preset (.obj m) = .ok request) :
    SigningRequest.ofJson preset document = .ok request := by
  cases hw : write with
  | error e => simp [SigningRequest.toJson, hfields, hw, bind, Except.bind] at wrote
  | ok j =>
    simp only [SigningRequest.toJson, hfields, hw, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at wrote
    subst wrote
    obtain ⟨ht, hb, hs⟩ := plainDocument (name := request.type.name) (key := key) (body := j)
      (signingRoot := signingRoot) fresh
    obtain ⟨m, hm⟩ := mkObj_isObj (("type", .str request.type.name) :: (key, j) ::
      signingRootFields signingRoot)
    rw [hm] at ht hb hs ⊢
    exact reads m j hw (readType_eq_ok_of_getObjVal? ht) hs hb

/-- The writer never fails on the block of a request of the second block kind. -/
theorem BlockV2Body.toJson_total [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (body : BlockV2Body preset) : ∃ document, body.toJson = .ok document := by
  cases body <;>
  · rename_i value
    obtain ⟨j, hj⟩ := toApiJson_total value
    simp [BlockV2Body.toJson, hj, bind, Except.bind, pure, Except.pure]

/-- The writer never fails on a request.

So the round trip below covers every request, of every kind and every version. -/
theorem SigningRequest.toJson_total [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [NeZero (syncSubcommitteeSize preset)]
    (request : SigningRequest preset) : ∃ document, request.toJson = .ok document := by
  -- The shared part writes its fork info, which never fails.
  have shared : ∀ signing : Signing, ∃ fields, signingFields signing = .ok fields := by
    intro signing
    obtain ⟨f, hf⟩ := toApiJson_total signing.forkInfo
    simp [signingFields, hf, bind, Except.bind, pure, Except.pure]
  cases request
  case blockV2 signing body =>
    obtain ⟨j, hj⟩ := BlockV2Body.toJson_total body
    obtain ⟨l, hl⟩ := shared signing
    simp [SigningRequest.toJson, SigningRequest.fields, hj, hl, bind, Except.bind,
      pure, Except.pure]
  case aggregateAndProofV2 signing version body =>
    obtain ⟨j, hj⟩ := toApiJson_total body
    obtain ⟨l, hl⟩ := shared signing
    simp [SigningRequest.toJson, SigningRequest.fields, hj, hl, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map]
  case deposit signingRoot body =>
    obtain ⟨j, hj⟩ := toApiJson_total body
    simp [SigningRequest.toJson, SigningRequest.fields, hj, bind, Except.bind,
      pure, Except.pure]
  case validatorRegistration signingRoot body =>
    obtain ⟨j, hj⟩ := toApiJson_total body
    simp [SigningRequest.toJson, SigningRequest.fields, hj, bind, Except.bind,
      pure, Except.pure]
  all_goals
    rename_i signing body
    obtain ⟨j, hj⟩ := toApiJson_total body
    obtain ⟨l, hl⟩ := shared signing
    simp [SigningRequest.toJson, SigningRequest.fields, hj, hl, bind, Except.bind,
      pure, Except.pure]

/-- The reader gives back every request that the writer writes.

The preset must give each bounded list and vector of the bodies a positive size.

The round trip of their containers needs it. -/
theorem SigningRequest.ofJson_toJson [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    [NeZero (syncSubcommitteeSize preset)]
    {request : SigningRequest preset} {document : Json} (wrote : request.toJson = .ok document) :
    SigningRequest.ofJson preset document = .ok request := by
  cases request
  case aggregateAndProofV2 signing version body =>
    refine ofJson_of_signing rfl (by decide) wrote fun m j hj ht hs hb => ?_
    obtain ⟨d, hd⟩ := toApiJson_total body
    simp only [hd, Functor.map, Except.map, Except.ok.injEq] at hj
    subst hj
    obtain ⟨n, hn⟩ := mkObj_isObj [("version", .str (versionName version)), ("data", d)]
    have hv := readVersion_versionedJson version (key := "data") d "aggregate_and_proof"
      (by decide)
    have hx := readValue_of_getObjVal? (versionedJson_getObjVal? version (key := "data") d
      (by decide)) hd
    simp only [versionedJson] at hb hv hx
    rw [hn] at hb hv hx
    simp [SigningRequest.ofJson, SigningRequest.type, ht, hs,
      readObject, field, hb, hv, hx, bind, Except.bind, pure,
      Except.pure]
  case blockV2 signing body =>
    refine ofJson_of_signing rfl (by decide) wrote fun m j hj ht hs hb => ?_
    obtain ⟨n, rfl⟩ := BlockV2Body.toJson_isObj hj
    simp [SigningRequest.ofJson, SigningRequest.type, ht, hs,
      readObject, field, hb, BlockV2Body.ofJson_toJson hj, bind,
      Except.bind, pure, Except.pure]
  case deposit signingRoot body =>
    refine ofJson_of_plain rfl (by decide) wrote fun m j hj ht hs hb => ?_
    simp [SigningRequest.ofJson, SigningRequest.type, ht, hs,
      readValue_of_getObjVal? hb hj, bind, Except.bind, pure,
      Except.pure]
  case validatorRegistration signingRoot body =>
    refine ofJson_of_plain rfl (by decide) wrote fun m j hj ht hs hb => ?_
    simp [SigningRequest.ofJson, SigningRequest.type, ht, hs,
      readValue_of_getObjVal? hb hj, bind, Except.bind, pure,
      Except.pure]
  all_goals
    refine ofJson_of_signing rfl (by decide) wrote fun m j hj ht hs hb => ?_
    simp [SigningRequest.ofJson, SigningRequest.type, ht, hs,
      readValue_of_getObjVal? hb hj, bind, Except.bind, pure,
      Except.pure]

/-! ## The tags of a document -/

/-- A key that reads as a value is a key that the object holds with that value. -/
theorem getObjVal?_of_field {document value : Json} {key : String}
    (h : field document key = .ok value) : document.getObjVal? key = .ok value := by
  unfold field at h
  split at h <;> simp_all

/-- An object read under a key is the value that the object holds there. -/
theorem getObjVal?_of_readObject {document body : Json} {key : String}
    (h : readObject document key = .ok body) : document.getObjVal? key = .ok body := by
  unfold readObject at h
  cases hf : field document key with
  | error e => simp [hf, bind, Except.bind] at h
  | ok value =>
    simp only [hf, bind, Except.bind] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact getObjVal?_of_field hf
    · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A version read from a body is the version whose exact name the body holds. -/
theorem getObjVal?_of_readVersion {body : Json} {key : String} {version : ConsensusVersion}
    (h : readVersion body key = .ok version) :
    body.getObjVal? "version" = .ok (.str (versionName version)) := by
  unfold readVersion at h
  cases hf : field body "version" with
  | error e => simp [hf, bind, Except.bind] at h
  | ok value =>
    cases value <;> simp [hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    rename_i name
    cases hv : versionOfName? name with
    | none => simp [hv] at h
    | some found =>
      simp only [hv, pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [getObjVal?_of_field hf, versionName_of_versionOfName? hv]

/-- A kind read from a document is the kind whose exact name its field `type` holds. -/
theorem getObjVal?_of_readType {document : Json} {type : RequestType}
    (h : readType document = .ok type) :
    document.getObjVal? "type" = .ok (.str type.name) := by
  unfold readType at h
  cases hf : field document "type" with
  | error e => simp [hf, bind, Except.bind] at h
  | ok value =>
    cases value <;> simp [hf, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
    rename_i name
    cases hv : RequestType.ofName? name with
    | none => simp [hv] at h
    | some found =>
      simp only [hv, pure, Except.pure, Except.ok.injEq] at h
      subst h
      rw [getObjVal?_of_field hf, RequestType.name_of_ofName? hv]

/-- The block of a request of the second block kind has the version that its body names. -/
theorem BlockV2Body.readVersion_of_ofJson {document : Json} {body : BlockV2Body preset}
    (h : BlockV2Body.ofJson preset document = .ok body) :
    readVersion document "beacon_block" = .ok body.version := by
  unfold BlockV2Body.ofJson at h
  cases hv : readVersion document "beacon_block" with
  | error e => simp [hv, bind, Except.bind] at h
  | ok version =>
    simp only [hv, bind_ok_iff, Except.ok.injEq, exists_eq_left'] at h
    split at h
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
      obtain ⟨_, _, rfl⟩ := h
      rfl
    · split at h
      · rename_i isPhase0
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        subst isPhase0
        rfl
      · rename_i early other
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at h
        obtain ⟨_, _, rfl⟩ := h
        cases version <;> first | rfl | exact absurd rfl other | exact absurd (by decide) early

/-- A request read from a document has the kind that its field `type` names. -/
theorem readType_of_ofJson {document : Json} {request : SigningRequest preset}
    (h : SigningRequest.ofJson preset document = .ok request) :
    readType document = .ok request.type := by
  unfold SigningRequest.ofJson at h
  split at h
  · cases ht : readType (.obj _) with
    | error e => simp [ht, bind, Except.bind] at h
    | ok type =>
      rw [ht] at h
      simp only [bind_ok_iff, Except.ok.injEq, exists_eq_left'] at h
      cases type <;> simp only [bind_ok_iff, Except.ok.injEq, pure, Except.pure] at h <;>
        aesop (add norm simp SigningRequest.type)
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The field `type` of a document decides the kind of the request it reads as.

So two documents whose `type` names differ never read as requests of the same kind. -/
theorem getObjVal?_type_of_ofJson {document : Json} {request : SigningRequest preset}
    (h : SigningRequest.ofJson preset document = .ok request) :
    document.getObjVal? "type" = .ok (.str request.type.name) :=
  getObjVal?_of_readType (readType_of_ofJson h)

/-- A document whose field `type` names no kind of request is refused with that name. -/
theorem ofJson_unknownType {m : Std.TreeMap.Raw String Json compare} {name : String}
    (h : (Json.obj m).getObjVal? "type" = .ok (.str name))
    (unknown : RequestType.ofName? name = none) :
    SigningRequest.ofJson preset (.obj m) = .error (.unknownType name) := by
  simp [SigningRequest.ofJson, readType, field, h, unknown, bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- The field `version` of the aggregate of a request decides the version that it reads as. -/
theorem version_of_ofJson_aggregateAndProofV2 {document : Json} {signing : Signing}
    {version : ConsensusVersion} {data : AggregateAndProof preset version.fork}
    (h : SigningRequest.ofJson preset document = .ok (.aggregateAndProofV2 signing version data)) :
    ∃ body, document.getObjVal? "aggregate_and_proof" = .ok body ∧
      body.getObjVal? "version" = .ok (.str (versionName version)) := by
  have ht := readType_of_ofJson h
  unfold SigningRequest.ofJson at h
  split at h
  · rw [ht] at h
    simp only [SigningRequest.type, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨_, _, body, hb, found, hv, _, _, equal⟩ := h
    cases equal
    exact ⟨body, getObjVal?_of_readObject hb, getObjVal?_of_readVersion hv⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The field `version` of the block of a request decides the version that it reads as. -/
theorem version_of_ofJson_blockV2 {document : Json} {signing : Signing}
    {block : BlockV2Body preset}
    (h : SigningRequest.ofJson preset document = .ok (.blockV2 signing block)) :
    ∃ body, document.getObjVal? "beacon_block" = .ok body ∧
      body.getObjVal? "version" = .ok (.str (versionName block.version)) := by
  have ht := readType_of_ofJson h
  unfold SigningRequest.ofJson at h
  split at h
  · rw [ht] at h
    simp only [SigningRequest.type, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      exists_eq_left'] at h
    obtain ⟨_, _, body, hb, found, hr, equal⟩ := h
    cases equal
    exact ⟨body, getObjVal?_of_readObject hb,
      getObjVal?_of_readVersion (BlockV2Body.readVersion_of_ofJson hr)⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

end EthLib.Consensus.RemoteSigningApi
