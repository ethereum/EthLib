module

public import EthLib.Consensus.KeymanagerApi.Server
public import EthLib.Consensus.Proofs.KeymanagerApi.BuilderConfig
public import EthLib.Consensus.Proofs.KeymanagerApi.Run
public import EthLib.Consensus.Proofs.KeymanagerApi.VoluntaryExit

/-!
# Proofs: every key of a client has the public key of its secret key

A keyed client is one whose local keys each have the public key of their own secret key.

An import derives the public key from the secret, and a delete only removes keys.

No other call of the Keymanager API changes the local keys.

So every call keeps a client keyed, and so does every run of calls.

An exit that a keyed client signs verifies under the key of its validator.
-/

@[expose] public section

namespace EthLib.Consensus.KeymanagerApi

open Lean Base Cryptography Cryptography.Bls

/-- A client with no local key is keyed. -/
theorem KeyState.keyed_of_localKeys_eq_nil {state : KeyState} (h : state.localKeys = []) :
    state.Keyed := by
  intro key mem
  simp [h] at mem

/-- A keystore that decodes gives a key with the public key of its secret key. -/
theorem pubkey_of_decodeKeystore {text : JsonText} {limits : Keystore.KdfLimits}
    {keystore password : String} {key : LocalKey}
    (h : decodeKeystore text limits keystore password = .ok key) :
    key.pubkey = Signatures.skToPk key.secretKey := by
  -- The key is built with the public key of its secret key; only the early exits remain.
  unfold decodeKeystore at h
  simp only [bind, Except.bind] at h
  split at h <;> try (cases h)
  split at h <;> try (cases h)
  split at h <;> cases h
  rfl

/-- Importing one keystore keeps a client keyed. -/
private theorem keyed_importKeystore {text : JsonText} {limits : Keystore.KdfLimits}
    {file : Option Interchange} {state : KeyState} (keyed : state.Keyed)
    (keystore password : String) :
    (importKeystore text limits file state keystore password).2.Keyed := by
  unfold importKeystore
  split
  · exact keyed
  · rename_i key decoded
    split
    · exact keyed
    · intro k mem
      simp only [List.mem_append, List.mem_singleton] at mem
      rcases mem with mem | rfl
      · exact keyed k mem
      · exact pubkey_of_decodeKeystore decoded

/-- Importing keystores one after another keeps a client keyed. -/
theorem keyed_importAll {text : JsonText} {limits : Keystore.KdfLimits}
    {file : Option Interchange} {state : KeyState} (keyed : state.Keyed)
    (pairs : List (String × String)) : (importAll text limits file state pairs).2.Keyed := by
  induction pairs generalizing state with
  | nil => exact keyed
  | cons head rest ih =>
    obtain ⟨keystore, password⟩ := head
    exact ih (keyed_importKeystore keyed keystore password)

/-- Deleting one key keeps a client keyed. -/
private theorem keyed_deleteLocalKey {state : KeyState} (keyed : state.Keyed)
    (pubkey : BLSPubkey) : (deleteLocalKey state pubkey).2.Keyed := by
  unfold deleteLocalKey
  split
  · exact keyed
  · split
    · intro k mem
      exact keyed k (List.mem_of_mem_filter mem)
    · exact keyed

/-- Deleting keys one after another keeps a client keyed. -/
private theorem keyed_deleteLocalKeys {state : KeyState} (keyed : state.Keyed)
    (pubkeys : List BLSPubkey) : (deleteLocalKeys state pubkeys).2.Keyed := by
  induction pubkeys generalizing state with
  | nil => exact keyed
  | cons head rest ih => exact ih (keyed_deleteLocalKey keyed head)

/-- Deleting keys keeps a client keyed. -/
theorem keyed_deleteKeys {state : KeyState} (keyed : state.Keyed) (request : DeleteKeysRequest) :
    (deleteKeys state request).2.Keyed := by
  simpa [deleteKeys] using keyed_deleteLocalKeys keyed request.pubkeys

/-- Importing remote keys does not change the local keys. -/
private theorem localKeys_importRemoteKeys (state : KeyState)
    (definitions : List ImportRemoteSignerDefinition) :
    (importRemoteKeys state definitions).2.localKeys = state.localKeys := by
  induction definitions generalizing state with
  | nil => rfl
  | cons head rest ih =>
    simp only [importRemoteKeys]
    rw [ih]
    unfold importRemoteKey
    split <;> rfl

/-- Deleting remote keys does not change the local keys. -/
private theorem localKeys_deleteRemoteKeys (state : KeyState) (pubkeys : List BLSPubkey) :
    (deleteRemoteKeys state pubkeys).2.localKeys = state.localKeys := by
  induction pubkeys generalizing state with
  | nil => rfl
  | cons head rest ih =>
    simp only [deleteRemoteKeys]
    rw [ih]
    unfold deleteRemoteKey
    split
    · rfl
    · split <;> rfl

/-- A call on a lawful setting keeps a client keyed. -/
private theorem keyed_settingCalls {α : Type} {calls : SettingCalls α}
    (lawful : calls.setting.Lawful) {config : ClientConfig} {state : KeyState}
    (keyed : state.Keyed) (method : String) (pubkey : BLSPubkey) (body : Json) :
    (calls.handle config state method pubkey body).2.Keyed := by
  intro k mem
  rw [SettingCalls.localKeys_handle lawful config state method pubkey body] at mem
  exact keyed k mem

/-- A request to import keystores keeps a client keyed.

This is the import of a move between two clients. -/
theorem keyed_importKeystores {text : JsonText} {limits : Keystore.KdfLimits}
    {state after : KeyState} {request : ImportKeystoresRequest} {statuses : List ImportStatus}
    (keyed : state.Keyed)
    (imported : importKeystores text limits state request = .ok (statuses, after)) :
    after.Keyed := by
  unfold importKeystores at imported
  -- Every exit of the call either returns the state or imports one by one.
  simp only [bind, Except.bind, pure, Except.pure] at imported
  repeat'
    first
      | (cases imported; exact keyed)
      | (cases imported)
      | exact (congrArg (fun p : List ImportStatus × KeyState => p.2.Keyed)
          (Except.ok.inj imported)).mp (keyed_importAll keyed _)
      | split at imported

/-- The call that imports keystores keeps a client keyed. -/
private theorem keyed_postKeystores {state : KeyState} (keyed : state.Keyed) (text : JsonText)
    (limits : Keystore.KdfLimits) (body : Json) :
    (postKeystores text limits state body).2.Keyed := by
  unfold postKeystores
  split
  · exact keyed
  · split
    · exact keyed
    · exact keyed
    · exact keyed_importKeystores keyed (by assumption)

/-- The call that deletes keystores keeps a client keyed. -/
private theorem keyed_deleteKeystores {state : KeyState} (keyed : state.Keyed) (text : JsonText)
    (body : Json) : (deleteKeystores text state body).2.Keyed := by
  unfold deleteKeystores
  split
  · exact keyed
  · exact keyed_deleteKeys keyed _

/-- The call that imports remote keys keeps a client keyed. -/
private theorem keyed_postRemoteKeys {state : KeyState} (keyed : state.Keyed) (body : Json) :
    (postRemoteKeys state body).2.Keyed := by
  unfold postRemoteKeys
  split
  · exact keyed
  · intro k mem
    exact keyed k (by simpa [localKeys_importRemoteKeys] using mem)

/-- The call that deletes remote keys keeps a client keyed. -/
private theorem keyed_deleteRemoteKeysCall {state : KeyState} (keyed : state.Keyed)
    (body : Json) : (deleteRemoteKeysCall state body).2.Keyed := by
  unfold deleteRemoteKeysCall
  split
  · exact keyed
  · intro k mem
    exact keyed k (by simpa [localKeys_deleteRemoteKeys] using mem)

/-- Every call of the Keymanager API keeps a client keyed, whatever its method, path and body. -/
theorem keyed_handle {state : KeyState} (keyed : state.Keyed) (text : JsonText)
    (config : ClientConfig) (chain : Option ChainView) (method path : String) (body : Json) :
    (handle text config chain state method path body).2.Keyed := by
  unfold handle
  dsimp only
  split
  · exact keyed
  · exact keyed_postKeystores keyed text config.limits body
  · exact keyed_deleteKeystores keyed text body
  · exact keyed
  · exact keyed_postRemoteKeys keyed body
  · exact keyed_deleteRemoteKeysCall keyed body
  · exact KeyState.of_withPubkey keyed fun _ =>
      keyed_settingCalls feeRecipientSetting_lawful keyed _ _ body
  · exact KeyState.of_withPubkey keyed fun _ =>
      keyed_settingCalls gasLimitSetting_lawful keyed _ _ body
  · exact KeyState.of_withPubkey keyed fun _ =>
      keyed_settingCalls graffitiSetting_lawful keyed _ _ body
  · exact KeyState.of_withPubkey keyed fun _ =>
      keyed_settingCalls builderConfigSetting_lawful keyed _ _ body
  · exact KeyState.of_withPubkey keyed fun _ => keyed
  · exact keyed

/-- A run of calls from a keyed client leaves it keyed.

Each state of the run is the one that a call leaves from the state before it. -/
theorem keyed_of_run {states : Nat → KeyState} {k : Nat} (start : (states 0).Keyed)
    (run : ∀ i < k, ∃ text client chain method path body,
      states (i + 1) = (handle text client chain (states i) method path body).2) :
    (states k).Keyed :=
  KeyState.of_run (fun _ keyed => keyed_handle keyed) start run

/-- After a run of calls from a keyed client, an exit that the client signs verifies.

It verifies under the key of its validator, against the signing root of the exit. -/
theorem verify_of_signVoluntaryExit_of_run {preset : Preset} {fork : Fork}
    {config : Config} {state : BeaconState preset fork} {pubkey : BLSPubkey} {epoch : Epoch}
    {signed : SignedVoluntaryExit} {states : Nat → KeyState} {k : Nat}
    (start : (states 0).Keyed)
    (run : ∀ i < k, ∃ text client chain method path body,
      states (i + 1) = (handle text client chain (states i) method path body).2)
    (call : signVoluntaryExit config state (states k) pubkey epoch = .ok signed) :
    ∃ validator domain root, getValidator state signed.message.validatorIndex = .ok validator ∧
      voluntaryExitDomain config state signed.message.epoch = .ok domain ∧
      computeSigningRoot signed.message domain = .ok root ∧
      Signatures.verify validator.pubkey (packBytes root) signed.signature = true :=
  verify_of_signVoluntaryExit (keyed_of_run start run) call

end EthLib.Consensus.KeymanagerApi
