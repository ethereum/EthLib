module

public import EthLib.Consensus.Proofs.KeymanagerApi.BuilderConfig
public import EthLib.Consensus.Proofs.KeymanagerApi.DeleteKeys
public import EthLib.Consensus.Proofs.KeymanagerApi.LocalKeys
public import EthLib.Consensus.Proofs.KeymanagerApi.Run

/-!
# Proofs: remote keys through the Keymanager API

An import and a delete give one status for each key of the request, in order.

Each status is the one that the key gets on the state that the keys before it leave.

After an import, each key with the status imported is a remote key.

After a delete, no key with the status deleted is a remote key.

Importing one new key and then deleting it gives back the remote keys before.

The remote keys keep distinct public keys under every run of calls.
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

/-! ## Distinct public keys -/

/-- The remote keys of a client have distinct public keys. -/
def KeyState.RemoteDistinct (state : KeyState) : Prop :=
  (state.remoteKeys.map (·.pubkey)).Nodup

/-- An import of one key keeps the public keys of the remote keys distinct. -/
theorem remoteDistinct_importRemoteKey {state : KeyState} (distinct : state.RemoteDistinct)
    (definition : ImportRemoteSignerDefinition) :
    (importRemoteKey state definition).2.RemoteDistinct := by
  unfold importRemoteKey
  split
  · exact distinct
  · rename_i unknown
    -- A key that the client does not know has the public key of no remote key.
    simp only [KeyState.isKnown, Bool.or_eq_true, List.any_eq_true, beq_iff_eq, not_or,
      not_exists, not_and] at unknown
    simp only [KeyState.RemoteDistinct, List.map_append, List.map_cons, List.map_nil,
      List.nodup_append, List.nodup_cons, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
      and_self, List.mem_map, List.mem_singleton, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, true_and]
    exact ⟨distinct, fun key member _ same => same ▸ unknown.2 key member⟩

/-- An import of remote keys keeps their public keys distinct. -/
theorem remoteDistinct_importRemoteKeys {state : KeyState} (distinct : state.RemoteDistinct)
    (definitions : List ImportRemoteSignerDefinition) :
    (importRemoteKeys state definitions).2.RemoteDistinct := by
  induction definitions generalizing state with
  | nil => exact distinct
  | cons definition rest ih => exact ih (remoteDistinct_importRemoteKey distinct definition)

/-- A delete of remote keys keeps their public keys distinct, since it removes keys only. -/
theorem remoteDistinct_deleteRemoteKeys {state : KeyState} (distinct : state.RemoteDistinct)
    (pubkeys : List BLSPubkey) : (deleteRemoteKeys state pubkeys).2.RemoteDistinct :=
  ((remoteKeys_sublist_deleteRemoteKeys state pubkeys).map _).nodup distinct

/-- Every call of the Keymanager API keeps the public keys of the remote keys distinct. -/
theorem remoteDistinct_handle {state : KeyState} (distinct : state.RemoteDistinct)
    (text : JsonText) (config : ClientConfig) (chain : Option ChainView) (method path : String)
    (body : Json) : (handle text config chain state method path body).2.RemoteDistinct := by
  -- A call that keeps the remote keys keeps them distinct.
  have kept : ∀ after : KeyState, after.remoteKeys = state.remoteKeys → after.RemoteDistinct :=
    fun after same => by rw [KeyState.RemoteDistinct, same]; exact distinct
  -- The calls on the settings of a key change only their own mappings.
  have setting : ∀ {α : Type} (calls : SettingCalls α), calls.setting.Lawful →
      ∀ method pubkey body, (calls.handle config state method pubkey body).2.RemoteDistinct :=
    fun _ lawful method pubkey body =>
      kept _ (SettingCalls.remoteKeys_handle lawful config state method pubkey body)
  unfold handle
  dsimp only
  split
  · exact distinct
  · exact kept _ (remoteKeys_postKeystores state body)
  · exact kept _ (remoteKeys_deleteKeystores text state body)
  · exact distinct
  · unfold postRemoteKeys
    split
    · exact distinct
    · exact remoteDistinct_importRemoteKeys distinct _
  · unfold deleteRemoteKeysCall
    split
    · exact distinct
    · exact remoteDistinct_deleteRemoteKeys distinct _
  · exact KeyState.of_withPubkey distinct fun _ => setting _ feeRecipientSetting_lawful _ _ body
  · exact KeyState.of_withPubkey distinct fun _ => setting _ gasLimitSetting_lawful _ _ body
  · exact KeyState.of_withPubkey distinct fun _ => setting _ graffitiSetting_lawful _ _ body
  · exact KeyState.of_withPubkey distinct fun _ => setting _ builderConfigSetting_lawful _ _ body
  · exact KeyState.of_withPubkey distinct fun _ => distinct
  · exact distinct

/-- After a run of calls, the remote keys of a client still have distinct public keys.

Each state of the run is the one that a call leaves from the state before it. -/
theorem remoteDistinct_of_run {states : Nat → KeyState} {k : Nat}
    (start : (states 0).RemoteDistinct)
    (run : ∀ i < k, ∃ text client chain method path body,
      states (i + 1) = (handle text client chain (states i) method path body).2) :
    (states k).RemoteDistinct :=
  KeyState.of_run (fun _ distinct => remoteDistinct_handle distinct) start run

end EthLib.Consensus.KeymanagerApi
