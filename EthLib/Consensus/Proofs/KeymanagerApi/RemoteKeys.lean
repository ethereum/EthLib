module

public import EthLib.Consensus.KeymanagerApi.RemoteKeys

/-!
# Proofs: remote keys through the Keymanager API

An import and a delete give one status for each key of the request, in order.

Each status is the one that the key gets on the state that the keys before it leave.

After an import, each key with the status imported is a remote key.

After a delete, no key with the status deleted is a remote key.

Importing one new key and then deleting it gives back the remote keys before.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-- An import gives one status for each key. -/
theorem length_importRemoteKeys (state : KeyState)
    (definitions : List ImportRemoteSignerDefinition) :
    (importRemoteKeys state definitions).1.length = definitions.length := by
  induction definitions generalizing state with
  | nil => rfl
  | cons definition rest ih => simp [importRemoteKeys, ih]

/-- A delete gives one status for each key. -/
theorem length_deleteRemoteKeys (state : KeyState) (pubkeys : List BLSPubkey) :
    (deleteRemoteKeys state pubkeys).1.length = pubkeys.length := by
  induction pubkeys generalizing state with
  | nil => rfl
  | cons pubkey rest ih => simp [deleteRemoteKeys, ih]

/-- The status of one key of an import: duplicate exactly when the client knows the key. -/
theorem fst_importRemoteKey (state : KeyState) (definition : ImportRemoteSignerDefinition) :
    (importRemoteKey state definition).1 =
      if state.isKnown definition.pubkey then .duplicate else .imported := by
  unfold importRemoteKey
  split <;> rfl

/-- The status of one key of a delete: error if read-only, deleted if remote, else not found. -/
theorem fst_deleteRemoteKey (state : KeyState) (pubkey : BLSPubkey) :
    (deleteRemoteKey state pubkey).1 =
      if state.remoteKeys.any (fun key => key.pubkey == pubkey && key.readonly == some true) then
        .error "the key is read-only"
      else if state.remoteKeys.any (·.pubkey == pubkey) then .deleted else .notFound := by
  unfold deleteRemoteKey
  split
  · rfl
  · split <;> rfl

/-- The status of each key of an import is that of the key on the state that those before leave. -/
theorem getElem?_importRemoteKeys (state : KeyState)
    (definitions : List ImportRemoteSignerDefinition) (i : Nat) :
    (importRemoteKeys state definitions).1[i]? = definitions[i]?.map fun definition =>
      (importRemoteKey (importRemoteKeys state (definitions.take i)).2 definition).1 := by
  induction definitions generalizing state i with
  | nil => simp [importRemoteKeys]
  | cons definition rest ih =>
    cases i with
    | zero => simp [importRemoteKeys]
    | succ i => simp [importRemoteKeys, ih]

/-- The status of each key of a delete is that of the key on the state that those before leave. -/
theorem getElem?_deleteRemoteKeys (state : KeyState) (pubkeys : List BLSPubkey) (i : Nat) :
    (deleteRemoteKeys state pubkeys).1[i]? = pubkeys[i]?.map fun pubkey =>
      (deleteRemoteKey (deleteRemoteKeys state (pubkeys.take i)).2 pubkey).1 := by
  induction pubkeys generalizing state i with
  | nil => simp [deleteRemoteKeys]
  | cons pubkey rest ih =>
    cases i with
    | zero => simp [deleteRemoteKeys]
    | succ i => simp [deleteRemoteKeys, ih]

/-- An import of one key keeps every remote key, in order, first. -/
theorem remoteKeys_prefix_importRemoteKey (state : KeyState)
    (definition : ImportRemoteSignerDefinition) :
    state.remoteKeys <+: (importRemoteKey state definition).2.remoteKeys := by
  unfold importRemoteKey
  split
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

/-- A key with the status imported is a remote key afterwards. -/
theorem mem_remoteKeys_importRemoteKey {state : KeyState}
    {definition : ImportRemoteSignerDefinition}
    (imported : (importRemoteKey state definition).1 = .imported) :
    ⟨definition.pubkey, definition.url, some false⟩ ∈
      (importRemoteKey state definition).2.remoteKeys := by
  unfold importRemoteKey at imported ⊢
  split at imported
  · simp at imported
  · simp_all

/-- A delete of one key removes keys only. -/
theorem remoteKeys_sublist_deleteRemoteKey (state : KeyState) (pubkey : BLSPubkey) :
    (deleteRemoteKey state pubkey).2.remoteKeys.Sublist state.remoteKeys := by
  unfold deleteRemoteKey
  split
  · exact List.Sublist.refl _
  · split
    · exact List.filter_sublist
    · exact List.Sublist.refl _

/-- A key with the status deleted is no remote key afterwards. -/
theorem not_mem_remoteKeys_deleteRemoteKey {state : KeyState} {pubkey : BLSPubkey}
    (deleted : (deleteRemoteKey state pubkey).1 = .deleted) :
    ∀ key ∈ (deleteRemoteKey state pubkey).2.remoteKeys, key.pubkey ≠ pubkey := by
  unfold deleteRemoteKey at deleted ⊢
  split at deleted
  · simp at deleted
  · split at deleted
    · simp only [Bool.false_eq_true, ↓reduceIte, *, List.mem_filter, bne_iff_ne, ne_eq]
      exact fun _ member => member.2
    · simp at deleted

/-- An import keeps every remote key, in order, first. -/
theorem remoteKeys_prefix_importRemoteKeys (state : KeyState)
    (definitions : List ImportRemoteSignerDefinition) :
    state.remoteKeys <+: (importRemoteKeys state definitions).2.remoteKeys := by
  induction definitions generalizing state with
  | nil => exact List.prefix_refl _
  | cons definition rest ih =>
    exact (remoteKeys_prefix_importRemoteKey state definition).trans (ih _)

/-- After an import, each key with the status imported is a remote key. -/
theorem mem_remoteKeys_importRemoteKeys (state : KeyState)
    (definitions : List ImportRemoteSignerDefinition) (i : Nat)
    (definition : ImportRemoteSignerDefinition) (found : definitions[i]? = some definition)
    (imported : (importRemoteKeys state definitions).1[i]? = some .imported) :
    ⟨definition.pubkey, definition.url, some false⟩ ∈
      (importRemoteKeys state definitions).2.remoteKeys := by
  induction definitions generalizing state i with
  | nil => simp at found
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [importRemoteKeys, List.getElem?_cons_zero, Option.some.injEq] at imported ⊢
      exact (remoteKeys_prefix_importRemoteKeys _ rest).subset
        (mem_remoteKeys_importRemoteKey imported)
    | succ i =>
      simp only [List.getElem?_cons_succ] at found
      simp only [importRemoteKeys, List.getElem?_cons_succ] at imported ⊢
      exact ih _ i found imported

/-- Deleting remote keys removes keys only. -/
theorem remoteKeys_sublist_deleteRemoteKeys (state : KeyState) (pubkeys : List BLSPubkey) :
    (deleteRemoteKeys state pubkeys).2.remoteKeys.Sublist state.remoteKeys := by
  induction pubkeys generalizing state with
  | nil => exact List.Sublist.refl _
  | cons pubkey rest ih =>
    exact (ih _).trans (remoteKeys_sublist_deleteRemoteKey state pubkey)

/-- After a delete, no key with the status deleted is a remote key. -/
theorem not_mem_remoteKeys_deleteRemoteKeys (state : KeyState) (pubkeys : List BLSPubkey)
    (i : Nat) (pubkey : BLSPubkey) (found : pubkeys[i]? = some pubkey)
    (deleted : (deleteRemoteKeys state pubkeys).1[i]? = some .deleted) :
    ∀ key ∈ (deleteRemoteKeys state pubkeys).2.remoteKeys, key.pubkey ≠ pubkey := by
  induction pubkeys generalizing state i with
  | nil => simp at found
  | cons first rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst found
      simp only [deleteRemoteKeys, List.getElem?_cons_zero, Option.some.injEq] at deleted ⊢
      intro key member
      exact not_mem_remoteKeys_deleteRemoteKey deleted key
        ((remoteKeys_sublist_deleteRemoteKeys _ rest).subset member)
    | succ i =>
      simp only [List.getElem?_cons_succ] at found
      simp only [deleteRemoteKeys, List.getElem?_cons_succ] at deleted ⊢
      exact ih _ i found deleted

/-- Importing one key that the client does not know imports it, and deleting it then deletes it. -/
theorem fst_deleteRemoteKeys_importRemoteKeys (state : KeyState)
    (definition : ImportRemoteSignerDefinition)
    (unknown : state.isKnown definition.pubkey = false) :
    (importRemoteKeys state [definition]).1 = [.imported] ∧
      (deleteRemoteKeys (importRemoteKeys state [definition]).2 [definition.pubkey]).1 =
        [.deleted] := by
  have absent : ∀ key ∈ state.remoteKeys, key.pubkey ≠ definition.pubkey := by
    intro key member same
    simp only [KeyState.isKnown, Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq] at unknown
    exact unknown.2 key member same
  have notReadonly : (state.remoteKeys.any fun key =>
      key.pubkey == definition.pubkey && key.readonly == some true) = false := by
    simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
    exact fun key member same => absurd same (absent key member)
  simp [importRemoteKeys, importRemoteKey, unknown, deleteRemoteKeys, deleteRemoteKey,
    List.any_append, notReadonly]

/-- Importing one key that the client does not know, then deleting it, restores the remote keys. -/
theorem remoteKeys_deleteRemoteKeys_importRemoteKeys (state : KeyState)
    (definition : ImportRemoteSignerDefinition)
    (unknown : state.isKnown definition.pubkey = false) :
    (deleteRemoteKeys (importRemoteKeys state [definition]).2 [definition.pubkey]).2.remoteKeys =
      state.remoteKeys := by
  have absent : ∀ key ∈ state.remoteKeys, key.pubkey ≠ definition.pubkey := by
    intro key member same
    simp only [KeyState.isKnown, Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq] at unknown
    exact unknown.2 key member same
  simp only [importRemoteKeys, importRemoteKey, unknown, Bool.false_eq_true, ↓reduceIte,
    deleteRemoteKeys, deleteRemoteKey]
  simp only [List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.true_and,
    Bool.or_false]
  have notReadonly : (state.remoteKeys.any fun key =>
      key.pubkey == definition.pubkey && key.readonly == some true) = false := by
    simp only [List.any_eq_false, Bool.and_eq_true, beq_iff_eq, not_and]
    exact fun key member same => absurd same (absent key member)
  simp [notReadonly, List.filter_append]
  exact absent

end EthLib.Consensus.KeymanagerApi
