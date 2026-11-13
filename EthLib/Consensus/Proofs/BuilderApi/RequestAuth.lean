module

public import EthLib.Consensus.BuilderApi.RequestAuth

/-!
# Proofs: the checks of a Gloas request to a builder

Without data agreed out of band, the agreed data is the default data from the builder's URL.

A request for a bid fails no check exactly when its header, data, slot and signature all hold.

A request whose only failed check is the signature gets 401, and no other status.

A submission of preferences for a slot that has passed always fails, and leaves the store as it was.

The checks do not read the preferences, which the signature does not cover.

An accepted submission keeps its preferences for its key and slot, and changes no other entry.
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
    {agreed : ByteArray} {currentSlot : Slot} {pubkey : BLSPubkey}
    {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {failures : List AuthFailure} (passed : request.auth.message.slot < currentSlot)
    (checked : preferencesFailures config checks agreed currentSlot pubkey versionHeader request =
      .ok failures) :
    .slotPassed ∈ failures := by
  unfold preferencesFailures signatureFailures at checked
  rcases h : verifyBuilderRequestAuthSignature config checks request.auth pubkey with e | b
  · simp [h, Functor.map, Except.map] at checked
  · cases b <;> simp [h, passed, Functor.map, Except.map] at checked <;> simp [← checked]

/-- The checks of a request that submits preferences do not read the preferences. -/
theorem preferencesFailures_preferences (config : Config) (checks : SignatureChecks)
    (agreed : ByteArray) (currentSlot : Slot) (pubkey : BLSPubkey) (versionHeader : Option String)
    (request : BuilderPreferencesRequest) (preferences : BuilderPreferences) :
    preferencesFailures config checks agreed currentSlot pubkey versionHeader
        { request with preferences } =
      preferencesFailures config checks agreed currentSlot pubkey versionHeader request :=
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

/-- A submission that fails no check keeps its preferences under the key and its slot. -/
theorem PreferencesStore.submit_of_accepted {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {pubkey : BLSPubkey}
    {versionHeader : Option String} {request : BuilderPreferencesRequest}
    (store : PreferencesStore)
    (accepted : preferencesFailures config checks agreed currentSlot pubkey versionHeader request =
      .ok []) :
    store.submit config checks agreed currentSlot pubkey versionHeader request =
      .ok (store.keep pubkey request.auth.message.slot request.preferences) := by
  simp [PreferencesStore.submit, accepted, bind, Except.bind, pure, Except.pure]

/-- A submission for a slot that has passed leaves the store as it was. -/
theorem PreferencesStore.submit_of_passed {config : Config} {checks : SignatureChecks}
    {agreed : ByteArray} {currentSlot : Slot} {pubkey : BLSPubkey}
    {versionHeader : Option String} {request : BuilderPreferencesRequest}
    {store after : PreferencesStore} (passed : request.auth.message.slot < currentSlot)
    (submitted : store.submit config checks agreed currentSlot pubkey versionHeader request =
      .ok after) :
    after = store := by
  unfold PreferencesStore.submit at submitted
  cases checked : preferencesFailures config checks agreed currentSlot pubkey versionHeader
      request with
  | error e => simp [checked, bind, Except.bind] at submitted
  | ok failures =>
    have nonempty : failures ≠ [] := by
      rintro rfl
      simpa using preferencesFailures_of_passed passed checked
    simp [checked, nonempty, bind, Except.bind, pure, Except.pure] at submitted
    exact submitted.symm

/-- A bid honors preferences just kept for its proposer at its slot exactly when within the cap. -/
theorem bidHonorsPreferences_keep {preset : Preset} {fork : Fork} (store : PreferencesStore)
    (pubkey : BLSPubkey) (preferences : BuilderPreferences)
    (bid : ExecutionPayloadBid preset fork) :
    BidHonorsPreferences (store.keep pubkey bid.slot preferences) pubkey bid ↔
      bid.executionPayment ≤ preferences.maxExecutionPayment := by
  simp [BidHonorsPreferences, PreferencesStore.get_keep]

end EthLib.Consensus.BuilderApi
