module

public import EthLib.Consensus.KeymanagerApi.Settings

/-!
# Proofs: the settings of a key through the Keymanager API

The statements hold for the fee recipient, the gas limit and the graffiti alike.

A set then a get of the key gives the value set.

A delete then a get of the key gives the default.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

namespace Setting

variable {α : Type} {setting : Setting α} {config : ClientConfig} {state : KeyState}
  {pubkey other : BLSPubkey}

/-- A setting whose state gives back the mappings put into it, and keeps the keys of the client. -/
def Lawful (setting : Setting α) : Prop :=
  ∀ state mappings, setting.mappings (setting.withMappings state mappings) = mappings ∧
    (setting.withMappings state mappings).localKeys = state.localKeys ∧
    (setting.withMappings state mappings).remoteKeys = state.remoteKeys

/-- The value that the mappings give a key, after those of another key are filtered out. -/
private theorem lookup_filter_ne {mappings : List (BLSPubkey × α)} (different : other ≠ pubkey) :
    (mappings.filter (·.1 != pubkey)).lookup other = mappings.lookup other := by
  induction mappings with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    by_cases same : key = pubkey
    · subst same
      rw [List.filter_cons_of_neg (by simp), ih]
      have : (other == key) = false := by simpa using different
      simp [List.lookup_cons, this]
    · rw [List.filter_cons_of_pos (by simpa using same)]
      simp only [List.lookup_cons]
      split <;> simp_all

/-- The mappings give no value to a key whose mappings are filtered out. -/
private theorem lookup_filter_self (mappings : List (BLSPubkey × α)) :
    (mappings.filter (·.1 != pubkey)).lookup pubkey = none := by
  induction mappings with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨key, value⟩ := head
    by_cases same : key = pubkey
    · subst same
      rw [List.filter_cons_of_neg (by simp), ih]
    · rw [List.filter_cons_of_pos (by simpa using same)]
      have : (pubkey == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      simp [List.lookup_cons, this, ih]

/-- A set then a get of the key gives the value set. -/
theorem get_set (lawful : setting.Lawful) (value : α) :
    setting.get config (setting.set state pubkey value) pubkey = value := by
  rw [get, set, (lawful _ _).1]
  simp

/-- A set on one key leaves the value of every other key unchanged. -/
theorem get_set_of_ne (lawful : setting.Lawful) (value : α) (different : other ≠ pubkey) :
    setting.get config (setting.set state pubkey value) other = setting.get config state other := by
  have : (other == pubkey) = false := by simpa using different
  rw [get, set, (lawful _ _).1, get]
  simp [List.lookup_cons, this, lookup_filter_ne different]

/-- A delete then a get of the key gives the default. -/
theorem get_of_delete {after : KeyState} (lawful : setting.Lawful)
    (deleted : setting.delete state pubkey = .ok after) :
    setting.get config after pubkey = setting.default config := by
  unfold delete at deleted
  split at deleted
  · cases deleted
    rw [get, (lawful _ _).1, lookup_filter_self]
    rfl
  · cases deleted

/-- A delete on one key leaves the value of every other key unchanged. -/
theorem get_of_delete_of_ne {after : KeyState} (lawful : setting.Lawful)
    (deleted : setting.delete state pubkey = .ok after) (different : other ≠ pubkey) :
    setting.get config after other = setting.get config state other := by
  unfold delete at deleted
  split at deleted
  · cases deleted
    rw [get, (lawful _ _).1, lookup_filter_ne different, get]
  · cases deleted

/-- A delete on a key that the client does not manage gets HTTP 404. -/
theorem delete_of_isManaged_eq_false (unmanaged : state.isManaged pubkey = false) :
    setting.delete state pubkey = .error notManaged := by
  simp [delete, unmanaged]

/-- A delete on a key that the client manages succeeds, and removes its mappings. -/
theorem delete_of_isManaged (managed : state.isManaged pubkey = true) :
    setting.delete state pubkey =
      .ok (setting.withMappings state ((setting.mappings state).filter (·.1 != pubkey))) := by
  simp [delete, managed]

end Setting

/-- The fee recipient keeps its mappings. -/
theorem feeRecipientSetting_lawful : feeRecipientSetting.Lawful := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- The gas limit keeps its mappings. -/
theorem gasLimitSetting_lawful : gasLimitSetting.Lawful := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- The graffiti keeps its mappings. -/
theorem graffitiSetting_lawful : graffitiSetting.Lawful := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- A call through the API on a key that the client does not manage gets HTTP 404.

The state does not change. -/
theorem handle_of_isManaged_eq_false {α : Type} {calls : SettingCalls α}
    {config : ClientConfig} {state : KeyState} {method : String} {pubkey : BLSPubkey}
    {body : Json} (unmanaged : state.isManaged pubkey = false) :
    calls.handle config state method pubkey body = (Setting.notManaged, state) := by
  simp [SettingCalls.handle, unmanaged]

/-- A set through the API that gets HTTP 202, then a get of the key, answers the value set. -/
theorem handle_get_of_handle_set {α : Type} {calls : SettingCalls α} {config : ClientConfig}
    {state : KeyState} {pubkey : BLSPubkey} {body : Json} {value : α}
    (lawful : calls.setting.Lawful) (managed : state.isManaged pubkey = true)
    (read : calls.read body = .ok value) (allowed : calls.refuse value = none) (other : Json) :
    calls.handle config (calls.handle config state "POST" pubkey body).2 "GET" pubkey other =
      (calls.answer config pubkey value, calls.setting.set state pubkey value) := by
  have stillManaged : (calls.setting.set state pubkey value).isManaged pubkey = true := by
    obtain ⟨-, locals, remotes⟩ := lawful state
      ((pubkey, value) :: (calls.setting.mappings state).filter (·.1 != pubkey))
    simpa [Setting.set, KeyState.isManaged, KeyState.isActive, locals, remotes] using managed
  simp [SettingCalls.handle, managed, read, allowed, stillManaged, Setting.get_set lawful]

/-- A call through the API on a lawful setting keeps the local and the remote keys. -/
private theorem keys_handle {α : Type} {calls : SettingCalls α} (lawful : calls.setting.Lawful)
    (config : ClientConfig) (state : KeyState) (method : String) (pubkey : BLSPubkey)
    (body : Json) :
    (calls.handle config state method pubkey body).2.localKeys = state.localKeys ∧
      (calls.handle config state method pubkey body).2.remoteKeys = state.remoteKeys := by
  unfold SettingCalls.handle
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split
        · exact ⟨rfl, rfl⟩
        · exact (lawful _ _).2
    · split
      · rename_i deleted
        unfold Setting.delete at deleted
        split at deleted
        · cases deleted
          exact (lawful _ _).2
        · cases deleted
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

/-- A call through the API on a lawful setting keeps the local keys. -/
theorem SettingCalls.localKeys_handle {α : Type} {calls : SettingCalls α}
    (lawful : calls.setting.Lawful) (config : ClientConfig) (state : KeyState) (method : String)
    (pubkey : BLSPubkey) (body : Json) :
    (calls.handle config state method pubkey body).2.localKeys = state.localKeys :=
  (keys_handle lawful config state method pubkey body).1

/-- A call through the API on a lawful setting keeps the remote keys. -/
theorem SettingCalls.remoteKeys_handle {α : Type} {calls : SettingCalls α}
    (lawful : calls.setting.Lawful) (config : ClientConfig) (state : KeyState) (method : String)
    (pubkey : BLSPubkey) (body : Json) :
    (calls.handle config state method pubkey body).2.remoteKeys = state.remoteKeys :=
  (keys_handle lawful config state method pubkey body).2

/-- A set of the zero fee recipient on a managed key gets HTTP 400 and changes nothing. -/
theorem handle_feeRecipient_zero {config : ClientConfig} {state : KeyState}
    {pubkey : BLSPubkey} {body : Json} (managed : state.isManaged pubkey = true)
    (zero : feeRecipientCalls.read body = .ok (Vector.replicate 20 0)) :
    feeRecipientCalls.handle config state "POST" pubkey body =
      (badRequest "Cannot specify the 0x00 fee recipient address through the API", state) := by
  have read : requiredField "" "ethaddress" readEthAddress body = .ok (Vector.replicate 20 0) :=
    zero
  simp [SettingCalls.handle, feeRecipientCalls, read, managed]

end EthLib.Consensus.KeymanagerApi
