module

public import EthLib.Consensus.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.Proofs.SlashingProtection

/-!
# Proofs: listing and deleting keys through the Keymanager API

A delete gives one status for each key of the request, in order, and keeps the record.

Afterwards the client holds no key of the request, unless it holds that key read-only.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-! ## Listing -/

/-- The list gives the public key of each key that the client holds, in order. -/
theorem map_validatingPubkey_listKeys (state : KeyState) :
    (listKeys state).map (·.validatingPubkey) = state.localKeys.map (·.pubkey) := by
  simp [listKeys]

/-! ## One key -/

/-- Deleting one key leaves the record as it was. -/
theorem protection_deleteLocalKey (state : KeyState) (pubkey : BLSPubkey) :
    (deleteLocalKey state pubkey).2.protection = state.protection := by
  unfold deleteLocalKey
  split
  · rfl
  · split <;> rfl

/-- Deleting one local key leaves the remote keys as they were. -/
theorem remoteKeys_deleteLocalKey (state : KeyState) (pubkey : BLSPubkey) :
    (deleteLocalKey state pubkey).2.remoteKeys = state.remoteKeys := by
  unfold deleteLocalKey
  split
  · rfl
  · split <;> rfl

/-- Deleting one key keeps each key held read-only, and adds none. -/
theorem isReadonly_deleteLocalKey (state : KeyState) (pubkey other : BLSPubkey) :
    (deleteLocalKey state pubkey).2.isReadonly other = state.isReadonly other := by
  unfold deleteLocalKey
  split
  · rfl
  · rename_i notReadonly
    split
    · apply Bool.eq_iff_iff.mpr
      simp only [KeyState.isReadonly, List.any_eq_true, List.mem_filter, Bool.and_eq_true,
        beq_iff_eq, bne_iff_ne, ne_eq] at notReadonly ⊢
      constructor
      · rintro ⟨key, ⟨member, -⟩, same, readonly⟩
        exact ⟨key, member, same, readonly⟩
      · rintro ⟨key, member, same, readonly⟩
        refine ⟨key, ⟨member, fun deleted => notReadonly ⟨key, member, ?_, readonly⟩⟩, same,
          readonly⟩
        exact deleted
    · rfl

/-- A key is active after one key is deleted only if it was active before. -/
theorem isActive_of_isActive_deleteLocalKey {state : KeyState} {pubkey other : BLSPubkey}
    (active : (deleteLocalKey state pubkey).2.isActive other = true) :
    state.isActive other = true := by
  unfold deleteLocalKey at active
  split at active
  · exact active
  · split at active
    · simp only [KeyState.isActive, List.any_eq_true, List.mem_filter] at active ⊢
      obtain ⟨key, ⟨member, -⟩, same⟩ := active
      exact ⟨key, member, same⟩
    · exact active

/-- A key that the client does not hold read-only is not active after its delete. -/
theorem isActive_deleteLocalKey_self {state : KeyState} {pubkey : BLSPubkey}
    (notReadonly : state.isReadonly pubkey = false) :
    (deleteLocalKey state pubkey).2.isActive pubkey = false := by
  unfold deleteLocalKey
  simp only [notReadonly, Bool.false_eq_true, ↓reduceIte]
  split
  · simp [KeyState.isActive, List.any_filter]
  · exact Bool.eq_false_iff.mpr ‹_›

/-! ## Keys one after another -/

/-- Deleting keys leaves the record as it was. -/
theorem protection_deleteLocalKeys (state : KeyState) (pubkeys : List BLSPubkey) :
    (deleteLocalKeys state pubkeys).2.protection = state.protection := by
  induction pubkeys generalizing state with
  | nil => rfl
  | cons pubkey rest ih => simp [deleteLocalKeys, ih, protection_deleteLocalKey]

/-- Deleting local keys leaves the remote keys as they were. -/
theorem remoteKeys_deleteLocalKeys (state : KeyState) (pubkeys : List BLSPubkey) :
    (deleteLocalKeys state pubkeys).2.remoteKeys = state.remoteKeys := by
  induction pubkeys generalizing state with
  | nil => rfl
  | cons pubkey rest ih => simp [deleteLocalKeys, ih, remoteKeys_deleteLocalKey]

/-- One status for each key. -/
theorem length_deleteLocalKeys (state : KeyState) (pubkeys : List BLSPubkey) :
    (deleteLocalKeys state pubkeys).1.length = pubkeys.length := by
  induction pubkeys generalizing state with
  | nil => rfl
  | cons pubkey rest ih => simp [deleteLocalKeys, ih]

/-- Deleting keys keeps each key held read-only, and adds none. -/
theorem isReadonly_deleteLocalKeys (state : KeyState) (pubkeys : List BLSPubkey)
    (other : BLSPubkey) :
    (deleteLocalKeys state pubkeys).2.isReadonly other = state.isReadonly other := by
  induction pubkeys generalizing state with
  | nil => rfl
  | cons pubkey rest ih => simp [deleteLocalKeys, ih, isReadonly_deleteLocalKey]

/-- A key is active after keys are deleted only if it was active before. -/
theorem isActive_of_isActive_deleteLocalKeys {state : KeyState} {pubkeys : List BLSPubkey}
    {other : BLSPubkey} (active : (deleteLocalKeys state pubkeys).2.isActive other = true) :
    state.isActive other = true := by
  induction pubkeys generalizing state with
  | nil => exact active
  | cons pubkey rest ih =>
    exact isActive_of_isActive_deleteLocalKey (ih (state := (deleteLocalKey state pubkey).2) active)

/-- Deleting the keys of two lists deletes those of the second from the state after the first. -/
theorem snd_deleteLocalKeys_append (state : KeyState) (front back : List BLSPubkey) :
    (deleteLocalKeys state (front ++ back)).2 =
      (deleteLocalKeys (deleteLocalKeys state front).2 back).2 := by
  induction front generalizing state with
  | nil => rfl
  | cons pubkey rest ih => simp [deleteLocalKeys, ih]

/-- The status of a key is that of its delete from the state that the keys before it leave. -/
theorem getElem?_deleteLocalKeys (state : KeyState) (pubkeys : List BLSPubkey) (i : Nat) :
    (deleteLocalKeys state pubkeys).1[i]? =
      pubkeys[i]?.map fun pubkey =>
        (deleteLocalKey (deleteLocalKeys state (pubkeys.take i)).2 pubkey).1 := by
  induction pubkeys generalizing state i with
  | nil => simp [deleteLocalKeys]
  | cons pubkey rest ih =>
    cases i with
    | zero => simp [deleteLocalKeys]
    | succ i => simp [deleteLocalKeys, ih]

/-! ## The call -/

variable {state new : KeyState} {request : DeleteKeysRequest} {response : DeleteKeysResponse}

/-- The final status of a key is that of its delete after the keys before it, read in the record. -/
theorem getElem?_data_deleteKeys (call : deleteKeys state request = (response, new)) (i : Nat) :
    response.data[i]? = request.pubkeys[i]?.map fun pubkey =>
      finalStatus state.protection pubkey
        (deleteLocalKey (deleteLocalKeys state (request.pubkeys.take i)).2 pubkey).1 := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨rfl, -⟩ := call
  simp only [List.getElem?_zipWith, getElem?_deleteLocalKeys]
  cases request.pubkeys[i]? <;> rfl

/-- A delete gives one status for each key of the request. -/
theorem length_data_deleteKeys (call : deleteKeys state request = (response, new)) :
    response.data.length = request.pubkeys.length := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨rfl, -⟩ := call
  simp [length_deleteLocalKeys]

/-- A delete keeps the record of the client, as the source requires. -/
theorem protection_of_deleteKeys (call : deleteKeys state request = (response, new)) :
    new.protection = state.protection := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨-, rfl⟩ := call
  exact protection_deleteLocalKeys _ _

/-- A delete keeps each key held read-only, and makes none read-only. -/
theorem isReadonly_of_deleteKeys (call : deleteKeys state request = (response, new))
    (pubkey : BLSPubkey) : new.isReadonly pubkey = state.isReadonly pubkey := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨-, rfl⟩ := call
  exact isReadonly_deleteLocalKeys _ _ _

/-- After a delete, the client holds no key of the request, unless it holds that key read-only. -/
theorem isReadonly_of_isActive_deleteKeys {pubkey : BLSPubkey}
    (call : deleteKeys state request = (response, new)) (requested : pubkey ∈ request.pubkeys)
    (active : new.isActive pubkey = true) : state.isReadonly pubkey = true := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨-, rfl⟩ := call
  obtain ⟨front, back, split⟩ := List.append_of_mem requested
  rw [split, snd_deleteLocalKeys_append] at active
  have afterKey := isActive_of_isActive_deleteLocalKeys
    (state := (deleteLocalKeys (deleteLocalKeys state front).2
    [pubkey]).2) (by simpa [deleteLocalKeys, snd_deleteLocalKeys_append] using active)
  cases readonly : state.isReadonly pubkey
  · have notReadonly : (deleteLocalKeys state front).2.isReadonly pubkey = false := by
      rw [isReadonly_deleteLocalKeys, readonly]
    simp [deleteLocalKeys, isActive_deleteLocalKey_self notReadonly] at afterKey
  · rfl

/-- The status of a key is an error exactly when the client holds that key read-only. -/
theorem error_iff_of_deleteKeys {i : Nat} {pubkey : BLSPubkey}
    (call : deleteKeys state request = (response, new))
    (atPubkey : request.pubkeys[i]? = some pubkey) :
    (∃ message, response.data[i]? = some (.error message)) ↔ state.isReadonly pubkey = true := by
  rw [getElem?_data_deleteKeys call, atPubkey]
  rw [← isReadonly_deleteLocalKeys state (request.pubkeys.take i) pubkey]
  generalize (deleteLocalKeys state (request.pubkeys.take i)).2 = before
  simp only [Option.map_some, Option.some.injEq]
  unfold deleteLocalKey
  cases readonly : before.isReadonly pubkey <;> cases active : before.isActive pubkey <;>
    simp [finalStatus] <;> split <;> simp

/-- A key named twice in a request is not deleted the second time. -/
theorem ne_deleted_of_deleteKeys {i j : Nat} {pubkey : BLSPubkey}
    (call : deleteKeys state request = (response, new)) (before : i < j)
    (atFirst : request.pubkeys[i]? = some pubkey) (atSecond : request.pubkeys[j]? = some pubkey) :
    response.data[j]? ≠ some .deleted := by
  rw [getElem?_data_deleteKeys call, atSecond]
  -- The keys before the second time hold the key at its first place.
  have taken : request.pubkeys.take j =
      request.pubkeys.take i ++ [pubkey] ++ (request.pubkeys.take j).drop (i + 1) := by
    have first : (request.pubkeys.take j).take (i + 1) = request.pubkeys.take i ++ [pubkey] := by
      rw [List.take_take, Nat.min_eq_left (by omega), List.take_add_one, atFirst]
      rfl
    rw [← first, List.take_append_drop]
  rw [taken, snd_deleteLocalKeys_append]
  generalize (request.pubkeys.take j).drop (i + 1) = rest
  generalize hstart : (deleteLocalKeys state (request.pubkeys.take i ++ [pubkey])).2 = start
  have readonlyStart : start.isReadonly pubkey = state.isReadonly pubkey := by
    rw [← hstart, isReadonly_deleteLocalKeys]
  intro deleted
  simp only [Option.map_some, Option.some.injEq] at deleted
  unfold deleteLocalKey at deleted
  split at deleted
  · simp [finalStatus] at deleted
  · rename_i notReadonlyThen
    split at deleted
    · rename_i activeThen
      have activeStart := isActive_of_isActive_deleteLocalKeys activeThen
      have notReadonly :
          (deleteLocalKeys state (request.pubkeys.take i)).2.isReadonly pubkey = false := by
        rw [isReadonly_deleteLocalKeys, ← readonlyStart, ← isReadonly_deleteLocalKeys start rest]
        simpa using notReadonlyThen
      rw [← hstart, snd_deleteLocalKeys_append] at activeStart
      simp [deleteLocalKeys, isActive_deleteLocalKey_self notReadonly] at activeStart
    · simp only [finalStatus] at deleted
      split at deleted <;> simp at deleted

/-- A key is exported exactly when a status of it in the request lets its data be returned. -/
theorem mem_exportedKeys {pubkeys : List BLSPubkey} {statuses : List DeleteStatus}
    {pubkey : BLSPubkey} :
    pubkey ∈ exportedKeys pubkeys statuses ↔
      ∃ (i : Nat) (status : DeleteStatus), pubkeys[i]? = some pubkey ∧
        statuses[i]? = some status ∧
        status.carriesData = true := by
  rw [exportedKeys, List.mem_filterMap]
  constructor
  · rintro ⟨⟨key, status⟩, member, kept⟩
    obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp member
    obtain ⟨at_i, status_i⟩ := List.getElem?_zip_eq_some.mp found
    by_cases exports : status.carriesData = true
    · simp only [exports, ↓reduceIte, Option.some.injEq] at kept
      subst kept
      exact ⟨i, status, at_i, status_i, exports⟩
    · simp [exports] at kept
  · rintro ⟨i, status, at_i, status_i, exports⟩
    refine ⟨(pubkey, status), List.mem_iff_getElem?.mpr ⟨i, ?_⟩, by simp [exports]⟩
    exact List.getElem?_zip_eq_some.mpr ⟨at_i, status_i⟩

/-- The data returned names only keys of the request whose status is deleted or not active. -/
theorem exists_of_mem_slashingProtection_deleteKeys {entry : InterchangeEntry}
    (call : deleteKeys state request = (response, new))
    (member : entry ∈ response.slashingProtection.data) :
    ∃ (i : Nat) (status : DeleteStatus), request.pubkeys[i]? = some entry.pubkey ∧
      response.data[i]? = some status ∧ status.carriesData = true := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨rfl, -⟩ := call
  simp only [Interchange.entriesOf, List.mem_filter, decide_eq_true_eq] at member
  exact mem_exportedKeys.mp member.2

/-- For a key whose status is deleted or not active, the data returned holds all its blocks. -/
theorem blocksOf_slashingProtection_deleteKeys {i : Nat} {pubkey : BLSPubkey}
    {status : DeleteStatus} (call : deleteKeys state request = (response, new))
    (atPubkey : request.pubkeys[i]? = some pubkey) (atStatus : response.data[i]? = some status)
    (exports : status.carriesData = true) :
    response.slashingProtection.blocksOf pubkey = state.protection.blocksOf pubkey := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨rfl, -⟩ := call
  exact blocksOf_entriesOf (mem_exportedKeys.mpr ⟨i, status, atPubkey, atStatus, exports⟩)

/-- For a key whose status is deleted or not active, the data returned holds all its votes. -/
theorem attestationsOf_slashingProtection_deleteKeys {i : Nat} {pubkey : BLSPubkey}
    {status : DeleteStatus} (call : deleteKeys state request = (response, new))
    (atPubkey : request.pubkeys[i]? = some pubkey) (atStatus : response.data[i]? = some status)
    (exports : status.carriesData = true) :
    response.slashingProtection.attestationsOf pubkey = state.protection.attestationsOf pubkey := by
  simp only [deleteKeys, Prod.mk.injEq] at call
  obtain ⟨rfl, -⟩ := call
  exact attestationsOf_entriesOf (mem_exportedKeys.mpr ⟨i, status, atPubkey, atStatus, exports⟩)

/-- A key that the record names is exported exactly when the request names it, if not read-only. -/
private theorem mem_exportedKeys_deleteKeys {pubkey : BLSPubkey}
    (call : deleteKeys state request = (response, new))
    (named : Interchange.namesKey state.protection pubkey = true) :
    pubkey ∈ exportedKeys request.pubkeys response.data ↔
      pubkey ∈ request.pubkeys ∧ state.isReadonly pubkey = false := by
  rw [mem_exportedKeys]
  constructor
  · rintro ⟨i, status, at_i, status_i, exports⟩
    refine ⟨List.mem_of_getElem? at_i, ?_⟩
    cases readonly : state.isReadonly pubkey
    · rfl
    · obtain ⟨message, isError⟩ := (error_iff_of_deleteKeys call at_i).mpr readonly
      rw [status_i, Option.some.injEq] at isError
      subst isError
      simp [DeleteStatus.carriesData] at exports
  · rintro ⟨requested, notReadonly⟩
    obtain ⟨i, at_i⟩ := List.mem_iff_getElem?.mp requested
    have status_i := getElem?_data_deleteKeys call i
    rw [at_i] at status_i
    refine ⟨i, finalStatus state.protection pubkey
      (deleteLocalKey (deleteLocalKeys state (request.pubkeys.take i)).2 pubkey).1, at_i, status_i,
      ?_⟩
    have before : (deleteLocalKeys state (request.pubkeys.take i)).2.isReadonly pubkey = false := by
      rw [isReadonly_deleteLocalKeys, notReadonly]
    generalize (deleteLocalKeys state (request.pubkeys.take i)).2 = start at before
    unfold deleteLocalKey
    simp only [before, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [finalStatus, named, DeleteStatus.carriesData]

/-- A delete sent again to the state that it leaves returns the same data, as the source asks. -/
theorem slashingProtection_deleteKeys_again (call : deleteKeys state request = (response, new)) :
    (deleteKeys new request).1.slashingProtection = response.slashingProtection := by
  have kept := protection_of_deleteKeys call
  have again : deleteKeys new request = ((deleteKeys new request).1, (deleteKeys new request).2) :=
    rfl
  have first : response.slashingProtection =
      state.protection.entriesOf (exportedKeys request.pubkeys response.data) := by
    simp only [deleteKeys, Prod.mk.injEq] at call
    obtain ⟨rfl, -⟩ := call
    rfl
  have second : (deleteKeys new request).1.slashingProtection =
      new.protection.entriesOf (exportedKeys request.pubkeys (deleteKeys new request).1.data) :=
    rfl
  rw [first, second, kept]
  simp only [Interchange.entriesOf, Interchange.mk.injEq, true_and]
  apply List.filter_congr
  intro entry member
  have named : Interchange.namesKey state.protection entry.pubkey = true :=
    List.any_eq_true.mpr ⟨entry, member, by simp⟩
  have namedAgain : Interchange.namesKey new.protection entry.pubkey = true := by
    rw [kept]
    exact named
  rw [decide_eq_decide, mem_exportedKeys_deleteKeys again namedAgain,
    mem_exportedKeys_deleteKeys call named, isReadonly_of_deleteKeys call]

/-- The call that deletes keystores leaves the remote keys as they were. -/
theorem remoteKeys_deleteKeystores (text : JsonText) (state : KeyState) (body : Json) :
    (deleteKeystores text state body).2.remoteKeys = state.remoteKeys := by
  unfold deleteKeystores deleteKeys
  split
  · rfl
  · exact remoteKeys_deleteLocalKeys _ _

end EthLib.Consensus.KeymanagerApi
