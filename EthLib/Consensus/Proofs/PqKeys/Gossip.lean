module

public import EthLib.Consensus.PqKeys.Gossip
public import EthLib.Networking.Proofs.Gossip.Validation

/-!
# Proofs: what an accepted registration satisfies

A registration is accepted exactly when every check of its topic passes.

So an accepted registration names a registrant that is not exiting, with the stored change epoch.

Its leanXMSS key is new and nonzero, its BLS signature is valid, and so is its proof of possession.

A beacon block passes the extra check exactly when it carries at most the preset number.

Each read of the head state is stated against the registry that it reads.

So the acceptance of a validator or a builder registration needs no hypothesis on the registrant.
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

/-! ## What the checks read from the head state -/

/-- The registrant of an index is the entry at its position in the registry that the index names.

A builder index reads the builders, their keys and their change epochs, with its flag cleared.

Any other index reads the validators, their keys and their change epochs, at the index itself. -/
theorem RegistrationView.registrant_eq_some_iff {view : RegistrationView}
    {index : ValidatorIndex} {pubkey : BLSPubkey} {keys : PQKeyMaterial} {epoch : Epoch} :
    view.registrant index = some (pubkey, keys, epoch) ↔
      isBuilderIndex index = true ∧
          (view.builders[(convertValidatorIndexToBuilderIndex index).toNat]?).map (·.pubkey) =
            some pubkey ∧
          view.builderKeys.data[(convertValidatorIndexToBuilderIndex index).toNat]? = some keys ∧
          view.builderChangeEpochs.data[(convertValidatorIndexToBuilderIndex index).toNat]? =
            some epoch ∨
        isBuilderIndex index = false ∧
          (view.validators[index.toNat]?).map (·.pubkey) = some pubkey ∧
          view.validatorKeys.data[index.toNat]? = some keys ∧
          view.validatorChangeEpochs.data[index.toNat]? = some epoch := by
  unfold RegistrationView.registrant
  cases isBuilderIndex index <;> simp [Option.bind_eq_some_iff] <;> grind

/-- A registrant has not begun to exit exactly when its exit epoch is the far future epoch.

For a builder index it is the withdrawable epoch of the builder, at the index with its flag cleared.

For any other index it is the exit epoch of the validator at the index. -/
theorem RegistrationView.notExiting_eq_true_iff {view : RegistrationView}
    {index : ValidatorIndex} :
    view.notExiting index = true ↔
      isBuilderIndex index = true ∧
          (∃ builder, view.builders[(convertValidatorIndexToBuilderIndex index).toNat]? =
            some builder ∧ builder.withdrawableEpoch = FAR_FUTURE_EPOCH) ∨
        isBuilderIndex index = false ∧
          ∃ validator, view.validators[index.toNat]? = some validator ∧
            validator.exitEpoch = FAR_FUTURE_EPOCH := by
  unfold RegistrationView.notExiting
  cases isBuilderIndex index <;> simp [Option.any_eq_true]

/-- The deposit check passes every index that is not a builder index.

A builder index passes exactly when its builder has a deposit epoch before the finalized epoch. -/
theorem RegistrationView.depositFinalized_eq_true_iff {view : RegistrationView}
    {index : ValidatorIndex} :
    view.depositFinalized index = true ↔
      isBuilderIndex index = false ∨
        ∃ builder, view.builders[(convertValidatorIndexToBuilderIndex index).toNat]? =
          some builder ∧ builder.depositEpoch < view.finalizedEpoch := by
  unfold RegistrationView.depositFinalized
  cases isBuilderIndex index <;> simp [Option.any_eq_true]

/-- A leanXMSS key is in use exactly when the keys of some validator or of some builder hold it. -/
theorem RegistrationView.keyInUse_eq_true_iff {view : RegistrationView} {key : XMSSPublicKey} :
    view.keyInUse key = true ↔
      (∃ keys ∈ view.validatorKeys.data, keys.xmssPublicKey = key) ∨
        ∃ keys ∈ view.builderKeys.data, keys.xmssPublicKey = key := by
  simp only [RegistrationView.keyInUse, Bool.or_eq_true, Array.any_eq_true', beq_iff_eq]

/-- A registration for a validator with a stored entry is accepted exactly when each check passes.

The checks read the validator, its keys and their change epoch, at the index itself.

The validator has no exit epoch yet, and the leanXMSS key is held by no validator and no builder. -/
theorem validatePqKeyRegistration_eq_accept_of_validator {view : RegistrationView}
    {validator : Validator} {stored : PQKeyMaterial} {changeEpoch : Epoch}
    (notBuilder : isBuilderIndex signed.message.index = false)
    (found : view.validators[signed.message.index.toNat]? = some validator)
    (keys : view.validatorKeys.data[signed.message.index.toNat]? = some stored)
    (epochs : view.validatorChangeEpochs.data[signed.message.index.toNat]? = some changeEpoch) :
    validatePqKeyRegistration config preset activationEpoch clockEpoch (some view) seen signed =
        accept ↔
      activationEpoch ≤ clockEpoch ∧
      validator.exitEpoch = FAR_FUTURE_EPOCH ∧
      seen = false ∧
      signed.message.previousChangeEpoch = changeEpoch ∧
      (stored.xmssPublicKey ≠ Vector.replicate 32 0 →
        changeEpoch.toNat + preset.MIN_PQ_KEY_CHANGE_DELAY.toNat ≤ clockEpoch.toNat) ∧
      signed.message.keyMaterial.xmssPublicKey ≠ Vector.replicate 32 0 ∧
      (∀ keys ∈ view.validatorKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey) ∧
      (∀ keys ∈ view.builderKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey) ∧
      isValidRegistrationSignature config view.genesisValidatorsRoot validator.pubkey signed =
        true ∧
      isValidPqPossessionProof config view.genesisValidatorsRoot validator.pubkey
        signed.message.keyMaterial.xmssPublicKey signed.possession = true := by
  have registered : view.registrant signed.message.index =
      some (validator.pubkey, stored, changeEpoch) :=
    RegistrationView.registrant_eq_some_iff.mpr (.inr ⟨notBuilder, by simp [found], keys, epochs⟩)
  rw [validatePqKeyRegistration_eq_accept registered]
  have exiting : view.notExiting signed.message.index = true ↔
      validator.exitEpoch = FAR_FUTURE_EPOCH := by
    simp [RegistrationView.notExiting_eq_true_iff, notBuilder, found]
  have deposit : view.depositFinalized signed.message.index = true :=
    RegistrationView.depositFinalized_eq_true_iff.mpr (.inl notBuilder)
  have used : view.keyInUse signed.message.keyMaterial.xmssPublicKey = false ↔
      (∀ keys ∈ view.validatorKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey) ∧
      ∀ keys ∈ view.builderKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey := by
    rw [← Bool.not_eq_true, RegistrationView.keyInUse_eq_true_iff]
    simp
  rw [exiting, used]
  simp [deposit, notBuilder, and_assoc]

/-- A registration for a builder with a stored entry is accepted exactly when each check passes.

The checks read the builder, its keys and their change epoch, at the index with its flag cleared.

The builder has no withdrawable epoch yet, and it was deposited before the finalized epoch.

Its VRF root is zero, and the leanXMSS key is held by no validator and no builder. -/
theorem validatePqKeyRegistration_eq_accept_of_builder {view : RegistrationView}
    {builder : Builder} {stored : PQKeyMaterial} {changeEpoch : Epoch}
    (isBuilder : isBuilderIndex signed.message.index = true)
    (found : view.builders[(convertValidatorIndexToBuilderIndex signed.message.index).toNat]? =
      some builder)
    (keys : view.builderKeys.data[(convertValidatorIndexToBuilderIndex
      signed.message.index).toNat]? = some stored)
    (epochs : view.builderChangeEpochs.data[(convertValidatorIndexToBuilderIndex
      signed.message.index).toNat]? = some changeEpoch) :
    validatePqKeyRegistration config preset activationEpoch clockEpoch (some view) seen signed =
        accept ↔
      activationEpoch ≤ clockEpoch ∧
      builder.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
      builder.depositEpoch < view.finalizedEpoch ∧
      signed.message.keyMaterial.vrfRoot = Vector.replicate 32 0 ∧
      seen = false ∧
      signed.message.previousChangeEpoch = changeEpoch ∧
      (stored.xmssPublicKey ≠ Vector.replicate 32 0 →
        changeEpoch.toNat + preset.MIN_PQ_KEY_CHANGE_DELAY.toNat ≤ clockEpoch.toNat) ∧
      signed.message.keyMaterial.xmssPublicKey ≠ Vector.replicate 32 0 ∧
      (∀ keys ∈ view.validatorKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey) ∧
      (∀ keys ∈ view.builderKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey) ∧
      isValidRegistrationSignature config view.genesisValidatorsRoot builder.pubkey signed =
        true ∧
      isValidPqPossessionProof config view.genesisValidatorsRoot builder.pubkey
        signed.message.keyMaterial.xmssPublicKey signed.possession = true := by
  have registered : view.registrant signed.message.index =
      some (builder.pubkey, stored, changeEpoch) :=
    RegistrationView.registrant_eq_some_iff.mpr (.inl ⟨isBuilder, by simp [found], keys, epochs⟩)
  rw [validatePqKeyRegistration_eq_accept registered]
  have exiting : view.notExiting signed.message.index = true ↔
      builder.withdrawableEpoch = FAR_FUTURE_EPOCH := by
    simp [RegistrationView.notExiting_eq_true_iff, isBuilder, found]
  have deposit : view.depositFinalized signed.message.index = true ↔
      builder.depositEpoch < view.finalizedEpoch := by
    simp [RegistrationView.depositFinalized_eq_true_iff, isBuilder, found]
  have used : view.keyInUse signed.message.keyMaterial.xmssPublicKey = false ↔
      (∀ keys ∈ view.validatorKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey) ∧
      ∀ keys ∈ view.builderKeys.data,
        keys.xmssPublicKey ≠ signed.message.keyMaterial.xmssPublicKey := by
    rw [← Bool.not_eq_true, RegistrationView.keyInUse_eq_true_iff]
    simp
  rw [exiting, deposit, used]
  simp [isBuilder, and_assoc]

/-- A block passes the extra check exactly when it carries at most the preset number. -/
theorem verifyPqKeyRegistrationsLimit_eq_accept {preset : PqKeyPreset}
    {registrations : PQKeyRegistrations} :
    verifyPqKeyRegistrationsLimit preset registrations = accept ↔
      registrations.data.size ≤ preset.MAX_PQ_KEY_REGISTRATIONS.toNat := by
  simp [verifyPqKeyRegistrationsLimit]

end EthLib.Consensus.PqKeys
