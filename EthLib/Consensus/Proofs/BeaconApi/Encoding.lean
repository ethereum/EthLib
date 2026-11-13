module

public import EthLib.Consensus.BeaconApi.Encoding
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

Without a byte alias, the writer never fails on a value of a lawful type.

An envelope reads back as written, so a response reads as its data under its version.

A response read under one version names it, so data of one fork never reads as data of another.

Hex reads the same in either case, as the patterns of the source allow.

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

/-- Without a byte alias, the writer never fails on a value of a lawful type. -/
theorem toApiJson_total {α : Type} [SszType α] [LawfulSszType α] [ApiSpelling α]
    (plain : ApiSpelling.spelling α = .opaque) (x : α) :
    ∃ document, toApiJson x = .ok document := by
  unfold toApiJson
  rw [plain]
  exact jsonOf_opaque_ok LawfulSszType.wellFormed (LawfulSszType.fits x)

/-- A value of bytes reads the same from its hex in uppercase. -/
theorem ofApiJson_uppercase {α : Type} [SszType α] [ApiSpelling α] {length : Nat}
    (bytes : SszType.desc α = .byteVector length ∨ SszType.desc α = .byteList length)
    (digits : String) :
    ofApiJson α (.str ("0x" ++ digits.map Char.toUpper)) = ofApiJson α (.str ("0x" ++ digits)) := by
  rcases bytes with shape | shape <;>
    simp [ofApiJson, shape, valueOf, collectionHex, bind, Except.bind, ofHex_uppercase]

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
/-- An envelope that a document holds has the version that the document names. -/
theorem readKey_version_of_ofJson {document : Json} {envelope : ApiEnvelope}
    (read : ApiEnvelope.ofJson document = .ok envelope) :
    ApiEnvelope.readKey document "version" ApiEnvelope.readVersion = .ok envelope.version := by
  unfold ApiEnvelope.ofJson at read
  cases document with
  | obj kv =>
    simp only at read
    split at read
    · cases hk : ApiEnvelope.readKey (Json.obj kv) "version" ApiEnvelope.readVersion with
      | error e => simp [hk, bind, Except.bind] at read
      | ok v =>
        simp only [hk, bind, Except.bind] at read
        repeat' split at read
        all_goals first
          | (simp at read; done)
          | (simp only [pure, Except.pure] at read; cases read; simp)
    · simp at read
  | _ => simp at read

/-- A response read under a version names that version, exactly. -/
theorem readVersioned_version {α : Type} [SszType α] [ApiSpelling α] {version : ConsensusVersion}
    {document : Json} {x : α} (read : readVersioned α version document = .ok x) :
    document.getObjVal? "version" = .ok (.str version.name) := by
  unfold readVersioned at read
  cases h : ApiEnvelope.ofJson document with
  | error e => simp [h, bind, Except.bind] at read
  | ok envelope =>
    have named : envelope.version = some version := by
      by_cases n : envelope.version = some version
      · exact n
      · simp [h, bind, Except.bind, n] at read
    have hv := readKey_version_of_ofJson h
    rw [named] at hv
    cases hg : document.getObjVal? "version" with
    | error e => simp [ApiEnvelope.readKey, hg] at hv
    | ok value =>
      cases value with
      | str s =>
        simp only [ApiEnvelope.readKey, hg, ApiEnvelope.readVersion] at hv
        cases ho : ConsensusVersion.ofName? s with
        | none => simp [ho] at hv
        | some b =>
          simp only [ho, Except.ok.injEq, Option.some.injEq] at hv
          subst hv
          rw [ConsensusVersion.name_of_ofName? ho]
      | _ => simp [ApiEnvelope.readKey, hg, ApiEnvelope.readVersion] at hv

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
