module

public import EthLib.Consensus.KeymanagerApi.Settings
public import EthLib.Consensus.Proofs.KeymanagerApi.Settings
public import EthLib.Consensus.Proofs.KeymanagerApi.Types

/-!
# Proofs: the builder configuration of the Keymanager API

A set, then a get, gives the configuration set, resolved.

A delete, then a get, gives what a key never set gets: the configuration of the client.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography.Bls

/-! ## Resolution -/

/-- A resolved entry, stored with every term set, resolves to itself. -/
theorem ResolvedBuilderEntry.resolve_toSetting (client : ClientBuilderConfig)
    (minBid builderBoostFactor : UInt64) (entry : ResolvedBuilderEntry) :
    entry.toSetting.resolve client minBid builderBoostFactor = .ok entry := by
  rfl

/-- A resolved configuration, stored with every value set, resolves to itself. -/
theorem ResolvedBuilderConfig.resolve_toSetting (client : ClientBuilderConfig)
    (config : ResolvedBuilderConfig) : config.toSetting.resolve client = .ok config := by
  obtain ⟨minBid, factor, builders⟩ := config
  -- Each stored entry resolves to the entry it came from.
  have resolved : (builders.map ResolvedBuilderEntry.toSetting).mapM
      (BuilderEntrySetting.resolve client minBid factor) = .ok builders := by
    induction builders with
    | nil => rfl
    | cons entry rest ih =>
      simp only [List.map_cons, List.mapM_cons, ResolvedBuilderEntry.resolve_toSetting, ih, bind,
        Except.bind, pure, Except.pure]
  simp [BuilderConfigSetting.resolve, ResolvedBuilderConfig.toSetting, resolved, bind,
    Except.bind, pure, Except.pure]

/-- The empty configuration resolves to the configuration of the client.

The defaults of the client fill the key, and its builders resolve with them. -/
theorem BuilderConfigSetting.resolve_empty (client : ClientBuilderConfig) :
    ({} : BuilderConfigSetting).resolve client = (do
      let builders ← client.builders.mapM
        (BuilderEntrySetting.resolve client client.minBid client.builderBoostFactor)
      return { minBid := client.minBid, builderBoostFactor := client.builderBoostFactor,
               builders }) := by
  rfl

/-! ## The JSON form -/

/-- Whether a resolved entry is within the bounds of the schema.

Its URL has 1 to 2048 bytes, its authentication data 1 to 4096 bytes, and it has at most 64 keys.
-/
def ResolvedBuilderEntry.WithinBounds (entry : ResolvedBuilderEntry) : Prop :=
  1 ≤ entry.url.utf8ByteSize ∧ entry.url.utf8ByteSize ≤ MAX_BUILDER_URL_SIZE ∧
    1 ≤ entry.authData.size ∧ entry.authData.size ≤ MAX_BUILDER_AUTH_DATA_SIZE ∧
    entry.terms.builderPubkeys.length ≤ MAX_BUILDER_PUBKEYS

/-- Authentication data reads back as itself. -/
private theorem readAuthData_authDataJson (path : String) {data : ByteArray}
    (low : 1 ≤ data.size) (high : data.size ≤ MAX_BUILDER_AUTH_DATA_SIZE) :
    readAuthData path (authDataJson data) = .ok data := by
  have text : readString path (authDataJson data) = .ok (Serialization.Ssz.toHex data) := rfl
  simp [readAuthData, text, Serialization.Ssz.ofHex_toHex, bind, Except.bind, low, high]

/-- A resolved entry within the bounds of the schema reads back as its stored form. -/
private theorem readBuilderEntrySetting_resolvedBuilderEntryJson (path : String)
    (entry : ResolvedBuilderEntry) (bounded : entry.WithinBounds) :
    readBuilderEntrySetting path (resolvedBuilderEntryJson entry) = .ok entry.toSetting := by
  obtain ⟨url, authData, keys, maxPayment, minBid, factor⟩ := entry
  obtain ⟨urlLow, urlHigh, authLow, authHigh, fewKeys⟩ := bounded
  have readUrl : ∀ path, readBuilderUrl path (stringJson url) = .ok url := by
    intro path
    simp [readBuilderUrl, readString_stringJson, urlLow, urlHigh, bind, Except.bind]
  have readKeys : ∀ path,
      readBuilderPubkeys path (.arr (keys.map Interchange.bytesJson).toArray) = .ok keys := by
    intro path
    have arr := Interchange.readArray_arr path (fun path => Interchange.readBytes path 48)
      Interchange.bytesJson (fun path key => Interchange.readBytes_bytesJson path key) keys
    simp [readBuilderPubkeys, readPubkeys, arr, ofProtection, fewKeys, bind, Except.bind]
  simp (disch := simp) [readBuilderEntrySetting, resolvedBuilderEntryJson, requiredField,
    optionalField, Interchange.field, getObjVal?_mkObj_eq, List.lookup, readUrl,
    readAuthData_authDataJson _ authLow authHigh, readKeys, readUint64_uint64Json, ofProtection,
    bind, Except.bind, pure, Except.pure, ResolvedBuilderEntry.toSetting]

/-- At most 64 resolved entries within the bounds of the schema read back in their stored form. -/
private theorem readBuilderEntries_arr (path : String) (entries : List ResolvedBuilderEntry)
    (few : entries.length ≤ MAX_BUILDER_ENTRIES)
    (bounded : ∀ entry ∈ entries, entry.WithinBounds) :
    readBuilderEntries path (.arr (entries.map resolvedBuilderEntryJson).toArray) =
      .ok (entries.map ResolvedBuilderEntry.toSetting) := by
  -- Count the positions from any start, as the recursion on the list does.
  have each : ∀ n, (((entries.map resolvedBuilderEntryJson).zipIdx n).mapM
      fun (element, index) => readBuilderEntrySetting s!"{path}[{index}]" element) =
      .ok (entries.map ResolvedBuilderEntry.toSetting) := by
    induction entries with
    | nil => intro n; rfl
    | cons entry rest ih =>
      intro n
      simp only [List.map_cons, List.zipIdx_cons, List.mapM_cons,
        readBuilderEntrySetting_resolvedBuilderEntryJson _ _ (bounded entry (by simp)),
        ih (by simp at few; omega) (fun other mem => bounded other (by simp [mem])), bind,
        Except.bind, pure, Except.pure]
  rw [readBuilderEntries, List.toList_toArray, each 0]
  simp [bind, Except.bind, few]

/-- The reader of a configuration reads a resolved one back, as its stored form.

Each entry must be within the bounds of the schema, and there are at most 64 of them. -/
theorem readBuilderConfigSetting_resolvedBuilderConfigJson (config : ResolvedBuilderConfig)
    (few : config.builders.length ≤ MAX_BUILDER_ENTRIES)
    (bounded : ∀ entry ∈ config.builders, entry.WithinBounds) :
    readBuilderConfigSetting (resolvedBuilderConfigJson config) = .ok config.toSetting := by
  simp (disch := simp) [readBuilderConfigSetting, resolvedBuilderConfigJson, optionalField,
    getObjVal?_mkObj_eq, List.lookup, readUint64_uint64Json,
    readBuilderEntries_arr _ config.builders few bounded, bind, Except.bind, pure,
    Except.pure, ResolvedBuilderConfig.toSetting]

/-! ## The calls -/

/-- The builder configuration keeps its mappings. -/
theorem builderConfigSetting_lawful : builderConfigSetting.Lawful := fun _ _ => ⟨rfl, rfl, rfl⟩

/-- The rules of a set allow a resolved configuration whose entries differ in URL or data. -/
private theorem refusal_toSetting (resolved : ResolvedBuilderConfig)
    (distinct : (resolved.builders.map fun entry => (entry.url, entry.authData)).Nodup) :
    resolved.toSetting.refusal = none := by
  simp only [BuilderConfigSetting.refusal, ResolvedBuilderConfig.toSetting, Option.getD_some,
    List.mapM_map]
  rw [Base.mapM_eq_ok_map (g := fun entry => (entry.url, entry.authData))]
  · -- A pair is read back from the bytes of its URL and its data, so distinct pairs stay apart.
    have keyed := distinct.map (S := fun a b => a ≠ b)
      (fun (url, data) => [String.toByteArray url, data])
      fun _ _ differ same => differ (by simpa [String.toByteArray_inj, Prod.ext_iff] using same)
    simp only [List.map_map] at keyed
    simpa [List.map_map, List.Nodup] using keyed
  · intro _ _
    rfl

/-- A get on a key that the client manages answers its configuration, resolved. -/
theorem builderConfigCalls_get {config : ClientConfig} {state : KeyState} {pubkey : BLSPubkey}
    {body : Json} (managed : state.isManaged pubkey = true) :
    builderConfigCalls.handle config state "GET" pubkey body =
      (builderConfigGet config (builderConfigSetting.get config state pubkey), state) := by
  simp [SettingCalls.handle, builderConfigCalls, managed]

/-- A set of a configuration that reads and that the rules allow answers HTTP 202.

A get then answers that configuration resolved, with HTTP 200.

The set replaces the stored configuration in full. -/
theorem builderConfigCalls_get_of_set {config : ClientConfig} {state : KeyState}
    {pubkey : BLSPubkey} {body other : Json} {value : BuilderConfigSetting}
    {resolved : ResolvedBuilderConfig} (managed : state.isManaged pubkey = true)
    (read : readBuilderConfigSetting body = .ok value) (allowed : value.refusal = none)
    (resolves : value.resolve config.builder = .ok resolved) :
    (builderConfigCalls.handle config state "POST" pubkey body).1 = ⟨202, .null⟩ ∧
      (builderConfigCalls.handle config (builderConfigCalls.handle config state "POST" pubkey
        body).2 "GET" pubkey other).1 = dataResponse (resolvedBuilderConfigJson resolved) := by
  refine ⟨by simp [SettingCalls.handle, builderConfigCalls, managed, read, allowed], ?_⟩
  rw [handle_get_of_handle_set (calls := builderConfigCalls) builderConfigSetting_lawful managed
    read allowed other]
  simp [builderConfigCalls, builderConfigGet, resolves]

/-- A delete answers HTTP 204, and a get then answers what a key never set gets.

That is the empty configuration resolved, which is the configuration of the client. -/
theorem builderConfigCalls_get_of_delete {config : ClientConfig} {state : KeyState}
    {pubkey : BLSPubkey} {body other : Json} (managed : state.isManaged pubkey = true) :
    (builderConfigCalls.handle config state "DELETE" pubkey body).1 = ⟨204, .null⟩ ∧
      (builderConfigCalls.handle config (builderConfigCalls.handle config state "DELETE" pubkey
        body).2 "GET" pubkey other).1 = builderConfigGet config {} := by
  have deleted := Setting.delete_of_isManaged (setting := builderConfigSetting) managed
  have stillManaged : (builderConfigSetting.withMappings state
      ((builderConfigSetting.mappings state).filter (·.1 != pubkey))).isManaged pubkey = true := by
    simpa [builderConfigSetting, KeyState.isManaged, KeyState.isActive] using managed
  refine ⟨by simp [SettingCalls.handle, builderConfigCalls, managed, deleted], ?_⟩
  simp [SettingCalls.handle, builderConfigCalls, managed, deleted, stillManaged,
    Setting.get_of_delete builderConfigSetting_lawful deleted]
  rfl

/-- A get answers a resolved configuration with HTTP 200 and that configuration as its data. -/
theorem builderConfigGet_toSetting (config : ClientConfig) (resolved : ResolvedBuilderConfig) :
    builderConfigGet config resolved.toSetting =
      dataResponse (resolvedBuilderConfigJson resolved) := by
  simp [builderConfigGet, ResolvedBuilderConfig.resolve_toSetting]

/-- A set of a resolved configuration, then a get, answers that configuration again.

It must be within the bounds of the schema, and its entries must differ in URL or data.

So the data of a get, set again, is answered again whenever it meets those conditions. -/
theorem builderConfigCalls_get_of_set_resolved {config : ClientConfig} {state : KeyState}
    {pubkey : BLSPubkey} {other : Json} {resolved : ResolvedBuilderConfig}
    (managed : state.isManaged pubkey = true)
    (few : resolved.builders.length ≤ MAX_BUILDER_ENTRIES)
    (bounded : ∀ entry ∈ resolved.builders, entry.WithinBounds)
    (distinct : (resolved.builders.map fun entry => (entry.url, entry.authData)).Nodup) :
    (builderConfigCalls.handle config
        (builderConfigCalls.handle config state "POST" pubkey
          (resolvedBuilderConfigJson resolved)).2
        "GET" pubkey other).1 = dataResponse (resolvedBuilderConfigJson resolved) := by
  exact (builderConfigCalls_get_of_set (other := other) managed
    (readBuilderConfigSetting_resolvedBuilderConfigJson resolved few bounded)
    (refusal_toSetting resolved distinct)
    (ResolvedBuilderConfig.resolve_toSetting config.builder resolved)).2

end EthLib.Consensus.KeymanagerApi
