module

public import EthLib.Consensus.BeaconApi.Encoding
public import EthLib.Consensus.BeaconApi.Spelling
public import EthLib.Consensus.Proofs.ConsensusVersion
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonHexCase
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonRoundTrip
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonTotal
public import EthLib.Serialization.Proofs.Ssz.Typed.Class
-- The envelope proof unfolds how Lean builds a JSON object.
import all Lean.Data.Json.Basic

/-!
# Proofs: the shared encodings of the Beacon API

The JSON reader gives back every value that the writer writes.

The writer never fails on a value of a lawful type.

An envelope reads back as written, so a response reads as its data under its version.

A response read under one version names it, so data of one fork never reads as data of another.

A document reads as an envelope exactly when it is an object with data.

Each metadata key is then absent or holds its form.

A response reads under a version exactly when it also names that version and its data reads.

A document reads the same with any hex digits in uppercase, as the patterns of the source allow.

The error bodies read back as written.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Lean Serialization.Ssz

/-- The reader gives back every value that the writer writes. -/
theorem ofApiJson_toApiJson {α : Type} [SszType α] [LawfulSszType α] [ApiSpelling α] {x : α}
    {document : Json} (wrote : toApiJson x = .ok document) : ofApiJson α document = .ok x := by
  have back := valueOf_jsonOf (SszType.desc α) LawfulSszType.wellFormed (ApiSpelling.spelling α)
    (SszType.toValue x) document (LawfulSszType.fits x) wrote
  simp only [ofApiJson, back]
  exact LawfulSszType.ofValue_toValue x

/-- The writer never fails on a value of a lawful type, whatever its spelling. -/
theorem toApiJson_total {α : Type} [SszType α] [LawfulSszType α] [ApiSpelling α] (x : α) :
    ∃ document, toApiJson x = .ok document :=
  jsonOf_ok LawfulSszType.wellFormed (LawfulSszType.fits x) _

/-- A container whose marks carry no text mark carries none. -/
theorem fieldSpelling_hasText {shape : Desc} {marks : List (String × Spelling)}
    (plain : ∀ mark ∈ marks, mark.2.hasText = false) :
    (fieldSpelling shape marks).hasText = false := by
  have mark : ∀ (name : String) (marks : List (String × Spelling)),
      (∀ mark ∈ marks, mark.2.hasText = false) →
      ((marks.lookup name).getD .opaque).hasText = false := by
    intro name marks plain
    induction marks with
    | nil => simp [List.lookup, Spelling.opaque, Spelling.hasText, Spelling.anyText]
    | cons head rest ih =>
      have first := plain head (by simp)
      have others := ih fun mark inside => plain mark (by simp [inside])
      by_cases same : name == head.1
      · simp [List.lookup, same, first]
      · simp [List.lookup, same, others]
  have none : Spelling.opaque.hasText = false := by
    simp [Spelling.opaque, Spelling.hasText, Spelling.anyText]
  unfold fieldSpelling
  split <;> first
    | exact none
    | (simp only [Spelling.hasText, Spelling.anyText_eq_false, List.mem_map]
       rintro _ ⟨name, _, rfl⟩
       exact mark name marks plain)

/-- The spelling of a state carries no text mark. -/
theorem BeaconState.spelling_hasText {preset : Preset} {fork : Base.Fork} :
    (ApiSpelling.spelling (BeaconState preset fork)).hasText = false :=
  fieldSpelling_hasText (by simp [Spelling.hasText])

/-- A document reads the same with some hex digits of its strings in uppercase.

It holds for a type that writes no text, for a refusal as well as a value.

Builder entries and configurations are left out, since the case of a URL is part of the URL. -/
theorem ofApiJson_uppercase {α : Type} [SszType α] [ApiSpelling α]
    (plain : (ApiSpelling.spelling α).hasText = false) {left right : Json}
    (same : SameUpToCase left right) : ofApiJson α left = ofApiJson α right := by
  simp only [ofApiJson, valueOf_sameUpToCase _ plain same]

/-- A metadata key that was written reads back, and one that was not written reads as absent. -/
theorem readKey_mkObj {β : Type} {pairs : List (String × Json)}
    (distinct : pairs.Pairwise fun a b => a.1 ≠ b.1) {key : String} {read : Json → Option β}
    {write : β → Json} (back : ∀ b, read (write b) = some b) (o : Option β)
    (present : ∀ b, o = some b → (key, write b) ∈ pairs)
    (absent : o = none → key ∉ pairs.map Prod.fst) :
    ApiEnvelope.readKey (Json.mkObj pairs) key read = .ok o := by
  cases o with
  | none =>
    simp only [ApiEnvelope.readKey, getObjVal?_mkObj_of_not_mem (absent rfl)]
  | some b =>
    simp only [ApiEnvelope.readKey, getObjVal?_mkObj distinct (present b rfl), back]

/-- A root reads back from its hex. -/
theorem readRoot_toHex (r : Root) :
    ApiEnvelope.readRoot (.str (toHex r.toArray)) = some r := by
  simp [ApiEnvelope.readRoot, ofHex_toHex]

/-- An envelope reads back as written. -/
theorem ApiEnvelope.ofJson_toJson (envelope : ApiEnvelope) :
    ApiEnvelope.ofJson envelope.toJson = .ok envelope := by
  obtain ⟨version, executionOptimistic, finalized, dependentRoot, data⟩ := envelope
  show ApiEnvelope.ofJson (Json.mkObj
    ((version.map fun v => ("version", Json.str v.name)).toList ++
    (executionOptimistic.map fun b => ("execution_optimistic", Json.bool b)).toList ++
    (finalized.map fun b => ("finalized", Json.bool b)).toList ++
    (dependentRoot.map fun r => ("dependent_root", Json.str (toHex r.toArray))).toList ++
    [("data", data)])) = _
  generalize hP : ((version.map fun v => ("version", Json.str v.name)).toList ++
    (executionOptimistic.map fun b => ("execution_optimistic", Json.bool b)).toList ++
    (finalized.map fun b => ("finalized", Json.bool b)).toList ++
    (dependentRoot.map fun r => ("dependent_root", Json.str (toHex r.toArray))).toList ++
    [("data", data)]) = P
  have distinct : P.Pairwise fun a b => a.1 ≠ b.1 := by
    subst hP
    cases version <;> cases executionOptimistic <;> cases finalized <;> cases dependentRoot <;>
      simp
  have k1 := readKey_mkObj (pairs := P) distinct (key := "version")
    (read := ApiEnvelope.readVersion) (write := fun v => Json.str v.name)
    (fun v => by simp [ApiEnvelope.readVersion, ConsensusVersion.ofName?_name]) version
    (by rintro b rfl; simp [← hP]) (by rintro rfl; simp [← hP])
  have k2 := readKey_mkObj (pairs := P) distinct (key := "execution_optimistic")
    (read := ApiEnvelope.readBool) (write := Json.bool) (fun b => rfl) executionOptimistic
    (by rintro b rfl; simp [← hP]) (by rintro rfl; simp [← hP])
  have k3 := readKey_mkObj (pairs := P) distinct (key := "finalized")
    (read := ApiEnvelope.readBool) (write := Json.bool) (fun b => rfl) finalized
    (by rintro b rfl; simp [← hP]) (by rintro rfl; simp [← hP])
  have k4 := readKey_mkObj (pairs := P) distinct (key := "dependent_root")
    (read := ApiEnvelope.readRoot) (write := fun r => Json.str (toHex r.toArray))
    readRoot_toHex dependentRoot
    (by rintro b rfl; simp [← hP]) (by rintro rfl; simp [← hP])
  have hdata : (Json.mkObj P).getObjVal? "data" = .ok data :=
    getObjVal?_mkObj distinct (by simp [← hP])
  obtain ⟨m, hm⟩ : ∃ m, Json.mkObj P = .obj m := ⟨_, rfl⟩
  rw [hm] at hdata k1 k2 k3 k4 ⊢
  simp only [ApiEnvelope.ofJson, hdata, k1, k2, k3, k4]
  rfl

/-- A response reads as its data under its version, whatever its other metadata. -/
theorem readVersioned_envelope {α : Type} [SszType α] [LawfulSszType α] [ApiSpelling α]
    {x : α} {data : Json} (wrote : toApiJson x = .ok data) (version : ConsensusVersion)
    (executionOptimistic finalized : Option Bool) (dependentRoot : Option Root) :
    readVersioned α version
      (ApiEnvelope.toJson ⟨some version, executionOptimistic, finalized, dependentRoot, data⟩) =
      .ok x := by
  simp [readVersioned, ApiEnvelope.ofJson_toJson, bind, Except.bind,
    ofApiJson_toApiJson wrote]
  rfl
/-- A metadata key reads as absent exactly when the document lacks it.

It reads as a value exactly when the document holds the key and its reader reads that value. -/
theorem readKey_eq_ok_iff {β : Type} {document : Json} {key : String} {read : Json → Option β}
    {o : Option β} :
    ApiEnvelope.readKey document key read = .ok o ↔
      (document.getObjVal? key).toOption = none ∧ o = none ∨
        ∃ value b, document.getObjVal? key = .ok value ∧ read value = some b ∧ o = some b := by
  unfold ApiEnvelope.readKey
  cases h : document.getObjVal? key with
  | error e => cases o <;> simp [Except.toOption]
  | ok value =>
    cases r : read value <;> cases o <;> simp [Except.toOption, r, eq_comm]

/-- When a reader accepts only the written form of each value, a key reads as the value it holds.

The key reads as absent exactly when the document lacks it. -/
theorem readKey_eq_ok_iff_of {β : Type} {read : Json → Option β} {write : β → Json}
    (exact : ∀ j b, read j = some b ↔ j = write b) {document : Json} {key : String}
    {o : Option β} :
    ApiEnvelope.readKey document key read = .ok o ↔
      (document.getObjVal? key).toOption = o.map write := by
  rw [readKey_eq_ok_iff]
  cases h : document.getObjVal? key <;> cases o <;>
    simp [Except.toOption, exact, eq_comm]

/-- A version reads exactly from the string of its name. -/
private theorem readVersion_eq_some_iff (j : Json) (v : ConsensusVersion) :
    ApiEnvelope.readVersion j = some v ↔ j = .str v.name := by
  cases j with
  | str s =>
    simp only [ApiEnvelope.readVersion, Json.str.injEq]
    exact ⟨ConsensusVersion.name_of_ofName?, fun h => h ▸ ConsensusVersion.ofName?_name v⟩
  | _ => simp [ApiEnvelope.readVersion]

/-- A flag reads exactly from the JSON boolean of its value. -/
private theorem readBool_eq_some_iff (j : Json) (b : Bool) :
    ApiEnvelope.readBool j = some b ↔ j = .bool b := by
  cases j <;> simp [ApiEnvelope.readBool]

/-- A root reads exactly from a string that is its hex, with any digits after `0x` in uppercase.

That hex is `0x` and 64 lowercase digits, two per byte. -/
theorem readRoot_eq_some_iff {j : Json} {root : Root} :
    ApiEnvelope.readRoot j = some root ↔
      ∃ text, j = .str text ∧ HexCase (toHex root.toArray) text := by
  cases j with
  | str text =>
    simp only [ApiEnvelope.readRoot, Json.str.injEq, exists_eq_left', ← ofHex_eq_ok_iff]
    cases h : ofHex text with
    | error e => simp
    | ok data =>
      by_cases size : data.size = 32
      · obtain ⟨r, hr⟩ := root
        simp only [size, ↓reduceDIte, Option.some.injEq, Except.ok.injEq]
        constructor
        · intro same
          cases same
          rfl
        · intro same
          subst same
          rfl
      · simp only [size, ↓reduceDIte, reduceCtorEq, false_iff, Except.ok.injEq]
        intro same
        exact size (same ▸ root.size_toArray)
  | _ => simp [ApiEnvelope.readRoot]

/-- A document holds an envelope exactly when it is an object whose keys read as its parts. -/
private theorem ApiEnvelope.ofJson_eq_ok_iff_readKey {document : Json} {envelope : ApiEnvelope} :
    ApiEnvelope.ofJson document = .ok envelope ↔
      (∃ fields, document = .obj fields) ∧ document.getObjVal? "data" = .ok envelope.data ∧
        ApiEnvelope.readKey document "version" ApiEnvelope.readVersion = .ok envelope.version ∧
        ApiEnvelope.readKey document "execution_optimistic" ApiEnvelope.readBool =
          .ok envelope.executionOptimistic ∧
        ApiEnvelope.readKey document "finalized" ApiEnvelope.readBool = .ok envelope.finalized ∧
        ApiEnvelope.readKey document "dependent_root" ApiEnvelope.readRoot =
          .ok envelope.dependentRoot := by
  obtain ⟨version, executionOptimistic, finalized, dependentRoot, data⟩ := envelope
  cases document with
  | obj kv =>
    simp only [ApiEnvelope.ofJson]
    cases hd : (Json.obj kv).getObjVal? "data" <;>
      cases h1 : ApiEnvelope.readKey (.obj kv) "version" ApiEnvelope.readVersion <;>
      cases h2 : ApiEnvelope.readKey (.obj kv) "execution_optimistic" ApiEnvelope.readBool <;>
      cases h3 : ApiEnvelope.readKey (.obj kv) "finalized" ApiEnvelope.readBool <;>
      cases h4 : ApiEnvelope.readKey (.obj kv) "dependent_root" ApiEnvelope.readRoot <;>
      simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
        ApiEnvelope.mk.injEq, eq_comm, and_comm, and_left_comm]
  | _ => simp [ApiEnvelope.ofJson, throw, throwThe, MonadExceptOf.throw]

/-- An envelope that a document holds has the version that the document names. -/
theorem readKey_version_of_ofJson {document : Json} {envelope : ApiEnvelope}
    (read : ApiEnvelope.ofJson document = .ok envelope) :
    ApiEnvelope.readKey document "version" ApiEnvelope.readVersion = .ok envelope.version :=
  (ApiEnvelope.ofJson_eq_ok_iff_readKey.mp read).2.2.1

/-- A document holds an envelope exactly when it is an object with that data under `data`.

The version, the two flags and the root are absent exactly when the document lacks their keys.

A version present is the string of its name under `version`.

Each flag present is the JSON boolean of its value, under `execution_optimistic` or `finalized`.

A root present is a string under `dependent_root`: its hex, with any digits after `0x` in uppercase.

Every other key may hold any value. -/
theorem ApiEnvelope.ofJson_eq_ok_iff {document : Json} {envelope : ApiEnvelope} :
    ApiEnvelope.ofJson document = .ok envelope ↔
      (∃ fields, document = .obj fields) ∧ document.getObjVal? "data" = .ok envelope.data ∧
        (document.getObjVal? "version").toOption = envelope.version.map (.str ·.name) ∧
        (document.getObjVal? "execution_optimistic").toOption =
          envelope.executionOptimistic.map .bool ∧
        (document.getObjVal? "finalized").toOption = envelope.finalized.map .bool ∧
        ((document.getObjVal? "dependent_root").toOption = none ∧ envelope.dependentRoot = none ∨
          ∃ root text, envelope.dependentRoot = some root ∧
            document.getObjVal? "dependent_root" = .ok (.str text) ∧
            HexCase (toHex root.toArray) text) := by
  rw [ApiEnvelope.ofJson_eq_ok_iff_readKey, readKey_eq_ok_iff_of readVersion_eq_some_iff,
    readKey_eq_ok_iff_of readBool_eq_some_iff, readKey_eq_ok_iff_of readBool_eq_some_iff,
    readKey_eq_ok_iff]
  simp only [readRoot_eq_some_iff]
  constructor
  · rintro ⟨obj, data, version, optimistic, final, absent | ⟨value, root, held, ⟨text, rfl, cased⟩,
      named⟩⟩
    · exact ⟨obj, data, version, optimistic, final, .inl absent⟩
    · exact ⟨obj, data, version, optimistic, final, .inr ⟨root, text, named, held, cased⟩⟩
  · rintro ⟨obj, data, version, optimistic, final, absent | ⟨root, text, named, held, cased⟩⟩
    · exact ⟨obj, data, version, optimistic, final, .inl absent⟩
    · exact ⟨obj, data, version, optimistic, final,
        .inr ⟨.str text, root, held, ⟨text, rfl, cased⟩, named⟩⟩

/-- A key reads whenever it is absent or its reader accepts the value it holds. -/
private theorem readKey_ok_of {β : Type} {document : Json} {key : String}
    {read : Json → Option β}
    (form : ∀ value, document.getObjVal? key = .ok value → ∃ b, read value = some b) :
    ∃ o, ApiEnvelope.readKey document key read = .ok o := by
  unfold ApiEnvelope.readKey
  cases h : document.getObjVal? key with
  | error e => exact ⟨none, rfl⟩
  | ok value =>
    obtain ⟨b, hb⟩ := form value h
    exact ⟨some b, by simp [hb]⟩

/-- A response reads under a version exactly when it is an object that names that version.

Its `version` key holds the string of that name.

Its `data` key holds JSON that the reader of the API reads as the value.

Where present, `execution_optimistic` and `finalized` hold JSON booleans.

Where present, `dependent_root` holds the hex of a root, with any digits after `0x` in uppercase.

Every other key may hold any value. -/
theorem readVersioned_eq_ok_iff {α : Type} [SszType α] [ApiSpelling α]
    {version : ConsensusVersion} {document : Json} {x : α} :
    readVersioned α version document = .ok x ↔
      (∃ fields, document = .obj fields) ∧
        document.getObjVal? "version" = .ok (.str version.name) ∧
        (∃ data, document.getObjVal? "data" = .ok data ∧ ofApiJson α data = .ok x) ∧
        (∀ value, document.getObjVal? "execution_optimistic" = .ok value → ∃ b, value = .bool b) ∧
        (∀ value, document.getObjVal? "finalized" = .ok value → ∃ b, value = .bool b) ∧
        (∀ value, document.getObjVal? "dependent_root" = .ok value →
          ∃ (root : Root) (text : String), value = .str text ∧
            HexCase (toHex root.toArray) text) := by
  have flag : ∀ {key : String} {o : Option Bool},
      (document.getObjVal? key).toOption = o.map .bool →
        ∀ value, document.getObjVal? key = .ok value → ∃ b, value = .bool b := by
    intro key o h value held
    cases o <;> simp_all [Except.toOption]
  constructor
  · intro read
    unfold readVersioned at read
    cases h : ApiEnvelope.ofJson document with
    | error e => simp [h, bind, Except.bind] at read
    | ok envelope =>
      obtain ⟨obj, data, named, optimistic, final, root⟩ := ApiEnvelope.ofJson_eq_ok_iff.mp h
      have version_eq : envelope.version = some version := by
        by_cases n : envelope.version = some version
        · exact n
        · simp [h, bind, Except.bind, n] at read
      have decoded : ofApiJson α envelope.data = .ok x := by
        simp only [h, version_eq, bind, Except.bind, pure, Except.pure] at read
        cases hx : ofApiJson α envelope.data <;>
          simp [hx, throw, throwThe, MonadExceptOf.throw] at read ⊢
        exact read
      refine ⟨obj, ?_, ⟨envelope.data, data, decoded⟩, flag optimistic, flag final, ?_⟩
      · rw [version_eq] at named
        cases g : document.getObjVal? "version" <;> simp_all [Except.toOption]
      · intro value held
        rcases root with ⟨absent, -⟩ | ⟨r, text, -, held', cased⟩
        · simp [held, Except.toOption] at absent
        · rw [held] at held'
          cases held'
          exact ⟨r, text, rfl, cased⟩
  · rintro ⟨obj, named, ⟨data, held, decoded⟩, optimistic, final, root⟩
    obtain ⟨o2, h2⟩ := readKey_ok_of (read := ApiEnvelope.readBool) fun value h => by
      obtain ⟨b, rfl⟩ := optimistic value h
      exact ⟨b, rfl⟩
    obtain ⟨o3, h3⟩ := readKey_ok_of (read := ApiEnvelope.readBool) fun value h => by
      obtain ⟨b, rfl⟩ := final value h
      exact ⟨b, rfl⟩
    obtain ⟨o4, h4⟩ := readKey_ok_of (read := ApiEnvelope.readRoot) fun value h => by
      obtain ⟨r, text, rfl, cased⟩ := root value h
      exact ⟨r, readRoot_eq_some_iff.mpr ⟨text, rfl, cased⟩⟩
    have h1 : ApiEnvelope.readKey document "version" ApiEnvelope.readVersion =
        .ok (some version) := by
      simp [ApiEnvelope.readKey, named, ApiEnvelope.readVersion, ConsensusVersion.ofName?_name]
    have envelope : ApiEnvelope.ofJson document = .ok ⟨some version, o2, o3, o4, data⟩ :=
      ApiEnvelope.ofJson_eq_ok_iff_readKey.mpr ⟨obj, held, h1, h2, h3, h4⟩
    simp [readVersioned, envelope, bind, Except.bind, decoded, pure, Except.pure]

/-- A response read under a version names that version, exactly. -/
theorem readVersioned_version {α : Type} [SszType α] [ApiSpelling α] {version : ConsensusVersion}
    {document : Json} {x : α} (read : readVersioned α version document = .ok x) :
    document.getObjVal? "version" = .ok (.str version.name) :=
  (readVersioned_eq_ok_iff.mp read).2.1

/-- A code reads back from the number that the writer gives it. -/
theorem readCode_num (n : Nat) :
    ErrorMessage.readCode (Json.num (JsonNumber.fromNat n)) = some n := by
  simp [ErrorMessage.readCode, JsonNumber.fromNat]

/-- Lines of text read back from the array that the writer gives them. -/
theorem readStrings_arr (lines : List String) :
    ErrorMessage.readStrings (Json.arr (lines.map Json.str).toArray) = some lines := by
  simp only [ErrorMessage.readStrings]
  induction lines with
  | nil => rfl
  | cons line rest ih => simp_all [List.mapM_cons]

/-- An error body reads back as written. -/
theorem ErrorMessage.ofJson_toJson (error : ErrorMessage) :
    ErrorMessage.ofJson error.toJson = some error := by
  obtain ⟨code, message, stacktraces⟩ := error
  show ErrorMessage.ofJson (Json.mkObj ([("code", Json.num code), ("message", Json.str message)] ++
    (stacktraces.map fun lines => ("stacktraces", Json.arr (lines.map .str).toArray)).toList)) = _
  generalize hP : ([("code", Json.num code), ("message", Json.str message)] ++
    (stacktraces.map fun lines => ("stacktraces", Json.arr (lines.map .str).toArray)).toList) = P
  have distinct : P.Pairwise fun a b => a.1 ≠ b.1 := by
    subst hP
    cases stacktraces <;> simp
  have hcode : (Json.mkObj P).getObjVal? "code" = .ok (Json.num code) :=
    getObjVal?_mkObj distinct (by simp [← hP])
  have hmessage : (Json.mkObj P).getObjVal? "message" = .ok (Json.str message) :=
    getObjVal?_mkObj distinct (by simp [← hP])
  cases stacktraces with
  | none =>
    have hlines := getObjVal?_mkObj_of_not_mem (pairs := P) (name := "stacktraces")
      (by simp [← hP])
    simp [ErrorMessage.ofJson, hcode, hmessage, hlines, readCode_num, Except.toOption]
  | some lines =>
    have hlines : (Json.mkObj P).getObjVal? "stacktraces" =
        .ok (Json.arr (lines.map Json.str).toArray) :=
      getObjVal?_mkObj distinct (by simp [← hP])
    simp [ErrorMessage.ofJson, hcode, hmessage, hlines, readCode_num, readStrings_arr,
      Except.toOption]

/-- A failure reads back from the object that the writer gives it. -/
theorem readFailure_mkObj (index : Nat) (message : String) :
    IndexedErrorMessage.readFailure (Json.mkObj
      [("index", Json.num index), ("message", Json.str message)]) = some (index, message) := by
  have hindex : (Json.mkObj [("index", Json.num index), ("message", Json.str message)]).getObjVal?
      "index" = .ok (Json.num index) := getObjVal?_mkObj (by simp) (by simp)
  have hmessage : (Json.mkObj [("index", Json.num index), ("message", Json.str message)]
      ).getObjVal? "message" = .ok (Json.str message) := getObjVal?_mkObj (by simp) (by simp)
  simp [IndexedErrorMessage.readFailure, hindex, hmessage, readCode_num, Except.toOption]

/-- The failures read back from the objects that the writer gives them. -/
theorem mapM_readFailure (failures : List (Nat × String)) :
    failures.mapM (IndexedErrorMessage.readFailure ∘ fun x => Json.mkObj
      [("index", Json.num (JsonNumber.fromNat x.1)), ("message", Json.str x.2)]) =
        some failures := by
  induction failures with
  | nil => rfl
  | cons failure rest ih =>
    obtain ⟨index, message⟩ := failure
    simp_all [List.mapM_cons, readFailure_mkObj]

/-- An error body that lists failed items reads back as written. -/
theorem IndexedErrorMessage.ofJson_toJson (error : IndexedErrorMessage) :
    IndexedErrorMessage.ofJson error.toJson = some error := by
  obtain ⟨code, message, failures⟩ := error
  show IndexedErrorMessage.ofJson (Json.mkObj [("code", Json.num code),
    ("message", Json.str message), ("failures", Json.arr (failures.map fun (index, message) =>
      Json.mkObj [("index", Json.num index), ("message", Json.str message)]).toArray)]) = _
  generalize hP : [("code", Json.num code), ("message", Json.str message),
    ("failures", Json.arr (failures.map fun (index, message) =>
      Json.mkObj [("index", Json.num index), ("message", Json.str message)]).toArray)] = P
  have distinct : P.Pairwise fun a b => a.1 ≠ b.1 := by
    subst hP
    simp
  have hcode : (Json.mkObj P).getObjVal? "code" = .ok (Json.num code) :=
    getObjVal?_mkObj distinct (by simp [← hP])
  have hmessage : (Json.mkObj P).getObjVal? "message" = .ok (Json.str message) :=
    getObjVal?_mkObj distinct (by simp [← hP])
  have hfailures : (Json.mkObj P).getObjVal? "failures" = .ok (Json.arr (failures.map
      fun (index, message) => Json.mkObj
        [("index", Json.num index), ("message", Json.str message)]).toArray) :=
    getObjVal?_mkObj distinct (by simp [← hP])
  simp [IndexedErrorMessage.ofJson, hcode, hmessage, hfailures, readCode_num, mapM_readFailure,
    Except.toOption]

end EthLib.Consensus.BeaconApi
