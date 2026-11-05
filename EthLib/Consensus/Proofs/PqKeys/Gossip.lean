module

public import EthLib.Consensus.PqKeys.Gossip
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: what an accepted registration satisfies

A registration is accepted exactly when every check of its topic passes.

So an accepted registration names a registrant that is not exiting, with the stored change epoch.

Its leanXMSS key is new and nonzero, its BLS signature is valid, and so is its proof of possession.

A beacon block passes the extra check exactly when it carries at most the preset number.
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open Base Cryptography.Bls Networking.Gossip Networking.Gossip.ValidationResult

variable {config : Config} {preset : PqKeyPreset} {activationEpoch clockEpoch : Epoch}
  {seen : Bool} {signed : SignedPQKeyRegistration}

/-- Before the head state reaches the fork of the registry, every registration is ignored. -/
theorem validatePqKeyRegistration_none (early : activationEpoch ≤ clockEpoch) :
    validatePqKeyRegistration config preset activationEpoch clockEpoch none seen signed =
      .ignore "head state before the fork of the registry" := by
  simp [validatePqKeyRegistration, early, ignoreUnless]

/-- A registration for an index with no validator or builder is rejected. -/
theorem validatePqKeyRegistration_no_registrant {view : RegistrationView}
    (early : activationEpoch ≤ clockEpoch)
    (absent : view.registrant signed.message.index = none) :
    validatePqKeyRegistration config preset activationEpoch clockEpoch (some view) seen signed =
      .reject "no validator or builder at the index" := by
  simp [validatePqKeyRegistration, early, ignoreUnless, absent]

/-- A registration for a registrant with a stored entry is accepted exactly when each check passes.

The stored entry is the BLS key of the registrant, its keys and the epoch of their last change. -/
theorem validatePqKeyRegistration_eq_accept {view : RegistrationView} {pubkey : BLSPubkey}
    {stored : PQKeyMaterial} {changeEpoch : Epoch}
    (registered : view.registrant signed.message.index = some (pubkey, stored, changeEpoch)) :
    validatePqKeyRegistration config preset activationEpoch clockEpoch (some view) seen signed =
        accept ↔
      activationEpoch ≤ clockEpoch ∧
      view.notExiting signed.message.index = true ∧
      view.depositFinalized signed.message.index = true ∧
      (isBuilderIndex signed.message.index = true →
        signed.message.keyMaterial.vrfRoot = Vector.replicate 32 0) ∧
      seen = false ∧
      signed.message.previousChangeEpoch = changeEpoch ∧
      (stored.xmssPublicKey ≠ Vector.replicate 32 0 →
        changeEpoch.toNat + preset.MIN_PQ_KEY_CHANGE_DELAY.toNat ≤ clockEpoch.toNat) ∧
      signed.message.keyMaterial.xmssPublicKey ≠ Vector.replicate 32 0 ∧
      view.keyInUse signed.message.keyMaterial.xmssPublicKey = false ∧
      isValidRegistrationSignature config view.genesisValidatorsRoot pubkey signed = true ∧
      isValidPqPossessionProof config view.genesisValidatorsRoot pubkey
        signed.message.keyMaterial.xmssPublicKey signed.possession = true := by
  simp only [validatePqKeyRegistration, registered, andThen_eq_accept, ignoreUnless_eq_accept,
    rejectUnless_eq_accept, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
    bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨early, exiting, deposit, vrf, fresh, stale, delay, zero, used, bls, possession⟩
    subst stale
    refine ⟨early, exiting, deposit, ?_, fresh, rfl, ?_, zero, used, bls, possession⟩
    · intro builder
      simpa [builder] using vrf
    · intro nonzero
      simpa [nonzero] using delay
  · rintro ⟨early, exiting, deposit, vrf, fresh, stale, delay, zero, used, bls, possession⟩
    subst stale
    refine ⟨early, exiting, deposit, ?_, fresh, rfl, ?_, zero, used, bls, possession⟩
    · cases builder : isBuilderIndex signed.message.index
      · exact .inl rfl
      · exact .inr (vrf builder)
    · by_cases nonzero : stored.xmssPublicKey = Vector.replicate 32 0
      · exact .inl nonzero
      · exact .inr (delay nonzero)

/-- A block passes the extra check exactly when it carries at most the preset number. -/
theorem verifyPqKeyRegistrationsLimit_eq_accept {preset : PqKeyPreset}
    {registrations : PQKeyRegistrations} :
    verifyPqKeyRegistrationsLimit preset registrations = accept ↔
      registrations.data.size ≤ preset.MAX_PQ_KEY_REGISTRATIONS.toNat := by
  simp [verifyPqKeyRegistrationsLimit]

end EthLib.Consensus.PqKeys
