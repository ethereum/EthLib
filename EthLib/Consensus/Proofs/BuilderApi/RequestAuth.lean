module

public import EthLib.Consensus.BuilderApi.RequestAuth

/-!
# Proofs: the checks of a Gloas request to a builder

A request for a bid fails no check exactly when its header, data, slot and signature all hold.

A submission of preferences for a slot that has passed always fails, and leaves the store as it was.

So does a submission from a key that the builder knows is not the proposer of the slot.

A submission for a key and slot whose preferences the store keeps leaves the store as it was.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

/-- Without data agreed out of band, the agreed data is the default data of the builder's URL. -/
theorem agreedData_none (builderUrl : String) :
    agreedData none builderUrl = defaultAuthData builderUrl := rfl

/-- Data agreed out of band is the agreed data, whatever the builder's URL. -/
theorem agreedData_some (data : ByteArray) (builderUrl : String) :
    agreedData (some data) builderUrl = .ok data := rfl

/-- A request for a bid fails no check exactly when every check holds. -/
theorem authFailures_nil_iff {config : Config} {checks : SignatureChecks} {agreed : ByteArray}
    {pathSlot : Slot} {pubkey : BLSPubkey} {versionHeader : Option String}
    {auth : SignedBuilderRequestAuth} :
    authFailures config checks agreed pathSlot pubkey versionHeader auth = .ok [] ↔
      versionHeader = some ConsensusVersion.gloas.name ∧ auth.message.data.data ≠ #[] ∧
        auth.message.data.data = agreed.data ∧ auth.message.slot = pathSlot ∧
        verifyBuilderRequestAuthSignature config checks auth pubkey = .ok true := by
  unfold authFailures signatureFailures headerFailures dataFailures
  rcases h : verifyBuilderRequestAuthSignature config checks auth pubkey with e | b
  · simp [Functor.map, Except.map]
  · cases b <;>
      simp [Functor.map, Except.map, List.append_eq_nil_iff] <;> grind

/-- A request for a bid whose only failed check is the signature fails with that check alone. -/
theorem authFailures_signature_only {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {pathSlot : Slot} {pubkey : BLSPubkey} {versionHeader : Option String}
    {auth : SignedBuilderRequestAuth} (header : versionHeader = some ConsensusVersion.gloas.name)
    (nonempty : auth.message.data.data ≠ #[]) (data : auth.message.data.data = agreed.data)
    (slot : auth.message.slot = pathSlot)
    (signature : verifyBuilderRequestAuthSignature config checks auth pubkey = .ok false) :
    authFailures config checks agreed pathSlot pubkey versionHeader auth = .ok [.badSignature] := by
  have hd : agreed.data ≠ #[] := data ▸ nonempty
  simp [authFailures, signatureFailures, headerFailures, dataFailures, signature, header, hd,
    data, slot, Functor.map, Except.map]

/-- A request whose only failed check is the signature gets 401 and no other status. -/
theorem allowedStatus_badSignature (status : Nat) :
    AllowedStatus [.badSignature] status ↔ status = 401 := by
  simp [AllowedStatus, AuthFailure.status, eq_comm]

/-- A request that submits preferences for a passed slot fails on that slot, when its checks run. -/
theorem preferencesFailures_of_passed {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey}
    {pubkey : BLSPubkey} {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {failures : List AuthFailure} (passed : request.auth.message.slot < currentSlot)
    (checked : preferencesFailures config checks agreed currentSlot proposerOf pubkey
      versionHeader request = .ok failures) :
    .slotPassed ∈ failures := by
  unfold preferencesFailures signatureFailures at checked
  rcases h : verifyBuilderRequestAuthSignature config checks request.auth pubkey with e | b
  · simp [h, Functor.map, Except.map] at checked
  · cases b <;> simp [h, passed, Functor.map, Except.map] at checked <;> simp [← checked]

/-- Preferences fail on the proposer exactly when the builder knows another proposer of their slot.

This holds whenever the checks run. -/
theorem notProposer_mem_iff {config : Config} {checks : SignatureChecks} {agreed : ByteArray}
    {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey} {pubkey : BLSPubkey}
    {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {failures : List AuthFailure}
    (checked : preferencesFailures config checks agreed currentSlot proposerOf pubkey
      versionHeader request = .ok failures) :
    .notProposer ∈ failures ↔
      ∃ key, proposerOf request.auth.message.slot = some key ∧ key ≠ pubkey := by
  unfold preferencesFailures signatureFailures headerFailures dataFailures at checked
  rcases h : verifyBuilderRequestAuthSignature config checks request.auth pubkey with e | b
  · simp [h, Functor.map, Except.map] at checked
  · cases b <;> simp [h, Functor.map, Except.map] at checked <;> subst checked <;>
      cases proposerOf request.auth.message.slot <;> simp <;> split <;> simp

/-- From Gloas, preferences fail on the proposer when the lookahead names another validator.

This holds whenever the checks run, for a builder that reads the lookahead of its state. -/
theorem notProposer_mem_of_lookahead {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {preset : Preset} {fork : Fork}
    {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork} {pubkey key : BLSPubkey}
    {versionHeader : Option String} {request : BuilderPreferencesRequest} {index : ValidatorIndex}
    {failures : List AuthFailure}
    (scheduled : lookaheadSchedule state (Nat.le_trans (by decide) gloas)
      request.auth.message.slot = some index)
    (keyed : validatorPubkey? state index = some key) (other : key ≠ pubkey)
    (checked : preferencesFailures config checks agreed currentSlot
      (lookaheadProposerKey state gloas) pubkey versionHeader request = .ok failures) :
    .notProposer ∈ failures :=
  (notProposer_mem_iff checked).mpr
    ⟨key, by simp [lookaheadProposerKey, scheduled, keyed], other⟩

/-- The checks of a request that submits preferences do not read the preferences.

The signature does not cover the preferences. -/
theorem preferencesFailures_preferences (config : Config) (checks : SignatureChecks)
    (agreed : ByteArray) (currentSlot : Slot) (proposerOf : Slot → Option BLSPubkey)
    (pubkey : BLSPubkey) (versionHeader : Option String) (request : BuilderPreferencesRequest)
    (preferences : BuilderPreferences) :
    preferencesFailures config checks agreed currentSlot proposerOf pubkey versionHeader
        { request with preferences } =
      preferencesFailures config checks agreed currentSlot proposerOf pubkey versionHeader
        request :=
  rfl

/-- A store with preferences kept under a key and a slot changes no entry under any other pair. -/
theorem PreferencesStore.get_keep (store : PreferencesStore) (pubkey : BLSPubkey) (kept : Slot)
    (preferences : BuilderPreferences) (key : BLSPubkey) (slot : Slot) :
    (store.keep pubkey kept preferences).get key slot =
      if key = pubkey ∧ slot = kept then some preferences else store.get key slot := by
  unfold PreferencesStore.keep PreferencesStore.get
  by_cases h : key = pubkey ∧ slot = kept
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp only [h, ite_false]
    have : ((key, slot) == (pubkey, kept)) = false := by
      rw [beq_eq_false_iff_ne]
      intro e; exact h ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
    simp [List.lookup_cons, this]

/-- A submission that fails no check keeps its preferences under the key and its slot.

This needs no preferences kept for that key and slot before. -/
theorem PreferencesStore.submit_of_accepted {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey}
    {pubkey : BLSPubkey} {versionHeader : Option String} {request : BuilderPreferencesRequest}
    (store : PreferencesStore)
    (accepted : preferencesFailures config checks agreed currentSlot proposerOf pubkey
      versionHeader request = .ok [])
    (fresh : store.get pubkey request.auth.message.slot = none) :
    store.submit config checks agreed currentSlot proposerOf pubkey versionHeader request =
      .ok (store.keep pubkey request.auth.message.slot request.preferences) := by
  simp [PreferencesStore.submit, accepted, fresh, bind, Except.bind, pure, Except.pure]

/-- A submission that some check fails leaves the store as it was. -/
private theorem PreferencesStore.submit_of_failed {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey}
    {pubkey : BLSPubkey} {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {store after : PreferencesStore} {failure : AuthFailure}
    (failed : ∀ failures, preferencesFailures config checks agreed currentSlot proposerOf pubkey
      versionHeader request = .ok failures → failure ∈ failures)
    (submitted : store.submit config checks agreed currentSlot proposerOf pubkey versionHeader
      request = .ok after) :
    after = store := by
  unfold PreferencesStore.submit at submitted
  cases checked : preferencesFailures config checks agreed currentSlot proposerOf pubkey
      versionHeader request with
  | error e => simp [checked, bind, Except.bind] at submitted
  | ok failures =>
    have nonempty : failures ≠ [] := by
      rintro rfl
      simpa using failed _ checked
    simp [checked, nonempty, bind, Except.bind, pure, Except.pure] at submitted
    exact submitted.symm

/-- A submission for a slot that has passed leaves the store as it was. -/
theorem PreferencesStore.submit_of_passed {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey}
    {pubkey : BLSPubkey} {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {store after : PreferencesStore} (passed : request.auth.message.slot < currentSlot)
    (submitted : store.submit config checks agreed currentSlot proposerOf pubkey versionHeader
      request = .ok after) :
    after = store :=
  submit_of_failed (fun _ => preferencesFailures_of_passed passed) submitted

/-- A submission whose key is not the proposer the builder knows leaves the store unchanged. -/
theorem PreferencesStore.submit_of_notProposer {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey}
    {pubkey key : BLSPubkey} {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {store after : PreferencesStore} (scheduled : proposerOf request.auth.message.slot = some key)
    (other : key ≠ pubkey)
    (submitted : store.submit config checks agreed currentSlot proposerOf pubkey versionHeader
      request = .ok after) :
    after = store :=
  submit_of_failed (fun _ checked => (notProposer_mem_iff checked).mpr ⟨key, scheduled, other⟩)
    submitted

/-- A submission for a key and slot whose preferences the store keeps leaves the store as it was.

So a replay of a request, with another cap, cannot replace the kept preferences. -/
theorem PreferencesStore.submit_of_kept {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {proposerOf : Slot → Option BLSPubkey}
    {pubkey : BLSPubkey} {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {store after : PreferencesStore} {kept : BuilderPreferences}
    (stored : store.get pubkey request.auth.message.slot = some kept)
    (submitted : store.submit config checks agreed currentSlot proposerOf pubkey versionHeader
      request = .ok after) :
    after = store := by
  unfold PreferencesStore.submit at submitted
  cases checked : preferencesFailures config checks agreed currentSlot proposerOf pubkey
      versionHeader request with
  | error e => simp [checked, bind, Except.bind] at submitted
  | ok failures =>
    simp [checked, stored, bind, Except.bind, pure, Except.pure] at submitted
    exact submitted.symm

/-- A bid honors preferences just kept for its proposer at its slot exactly when within the cap. -/
theorem bidHonorsPreferences_keep {preset : Preset} {fork : Fork} (store : PreferencesStore)
    (pubkey : BLSPubkey) (preferences : BuilderPreferences)
    (bid : ExecutionPayloadBid preset fork) :
    BidHonorsPreferences (store.keep pubkey bid.slot preferences) pubkey bid ↔
      bid.executionPayment ≤ preferences.maxExecutionPayment := by
  simp [BidHonorsPreferences, PreferencesStore.get_keep]

end EthLib.Consensus.BuilderApi
