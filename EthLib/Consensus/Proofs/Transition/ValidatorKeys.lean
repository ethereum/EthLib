module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Proofs: the validator keys along a chain

A chain of beacon states runs from the genesis state, one step at a time.

A step never overwrites the public key of a validator.

So the public keys before a step are a prefix of the keys after it.

Keys that are distinct before a step are distinct after it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- A validator keeps its public key at its position when the keys of the registry grow by suffix.

The two states may be at different forks. -/
theorem validators_getElem?_of_validatorKeys_prefix {post : Fork}
    {state : BeaconState preset fork} {after : BeaconState preset post}
    (kept : validatorKeys state <+: validatorKeys after) {i : Nat} {old : Validator}
    (found : state.validators.data[i]? = some old) :
    ∃ current, after.validators.data[i]? = some current ∧ current.pubkey = old.pubkey := by
  obtain ⟨inside, oldEq⟩ := Array.getElem?_eq_some_iff.mp found
  have small : i < (validatorKeys state).length := by simpa [validatorKeys] using inside
  have afterSmall : i < after.validators.data.size := by
    simpa [validatorKeys] using Nat.lt_of_lt_of_le small kept.length_le
  refine ⟨after.validators.data[i], by simp [afterSmall], ?_⟩
  have same := kept.getElem small
  simpa [validatorKeys, oldEq] using same.symm

/-- An indexed attestation valid in one state is valid in another state.

The check reads only the keys of the signers, the fork versions and the genesis validators root.

So it is enough that both registries are prefixes of the keys of a common state.

The signers must be in the other registry.

The two states must agree on the fork versions and the genesis validators root. -/
theorem isValidIndexedAttestation_of_keys {post : Fork} {one other : BeaconState preset fork}
    {common : BeaconState preset post}
    {indexed : IndexedAttestation preset fork}
    (valid : isValidIndexedAttestation config checks one indexed = .ok true)
    (oneKeys : validatorKeys one <+: validatorKeys common)
    (otherKeys : validatorKeys other <+: validatorKeys common)
    -- The two states must agree on the fork versions.
    (forkVersions : other.forkVersions = one.forkVersions)
    -- They must also agree on the genesis validators root.
    (genesisValidatorsRoot : other.genesisValidatorsRoot = one.genesisValidatorsRoot)
    -- The signers must be in the other registry.
    (inside : ∀ index ∈ indexed.attestingIndices.data.toList,
      index.toNat < other.validators.data.size) :
    isValidIndexedAttestation config checks other indexed = .ok true := by
  -- Each signer has one key, read in either state.
  have keys : ∀ index ∈ indexed.attestingIndices.data.toList,
      (Validator.pubkey <$> liftAccessor (getValidator other index)) =
        (Validator.pubkey <$> liftAccessor (getValidator one index)) := by
    intro index member
    obtain ⟨pubkeys, -, -, pubkeysOk, -⟩ := isValidIndexedAttestation_signature valid
    simp only [bind_pure_comp, Array.mapM_eq_mapM_toList] at pubkeysOk
    obtain ⟨ys, mappedOk⟩ : ∃ ys, indexed.attestingIndices.data.toList.mapM
        (fun index => Validator.pubkey <$> liftAccessor (getValidator one index)) = .ok ys := by
      cases mapped : indexed.attestingIndices.data.toList.mapM
          (fun index => Validator.pubkey <$> liftAccessor (getValidator one index)) with
      | error e =>
        rw [mapped] at pubkeysOk
        cases pubkeysOk
      | ok ys => exact ⟨ys, rfl⟩
    obtain ⟨key, read⟩ := mapM_ok_of_mem mappedOk index member
    obtain ⟨v, found⟩ : ∃ v, one.validators.data[index.toNat]? = some v := by
      cases h : one.validators.data[index.toNat]? with
      | none =>
        simp [getValidator, h, liftAccessor, Except.mapError, Functor.map, Except.map] at read
      | some v => exact ⟨v, rfl⟩
    obtain ⟨w, foundOther⟩ : ∃ w, other.validators.data[index.toNat]? = some w :=
      ⟨_, Array.getElem?_eq_getElem (inside index member)⟩
    obtain ⟨c, foundC, keyC⟩ := validators_getElem?_of_validatorKeys_prefix oneKeys found
    obtain ⟨c', foundC', keyC'⟩ := validators_getElem?_of_validatorKeys_prefix otherKeys foundOther
    rw [foundC, Option.some.injEq] at foundC'
    subst foundC'
    simp [getValidator, found, foundOther, liftAccessor, Except.mapError, Functor.map,
      Except.map, ← keyC, keyC']
  have domain : getDomain config other DOMAIN_BEACON_ATTESTER (some indexed.data.target.epoch) =
      getDomain config one DOMAIN_BEACON_ATTESTER (some indexed.data.target.epoch) := by
    simp only [getDomain, Option.getD_some, forkVersions, genesisValidatorsRoot]
  unfold isValidIndexedAttestation at valid ⊢
  simp only [bind_pure_comp, Array.mapM_eq_mapM_toList] at valid ⊢
  -- The two reads of the keys agree on every signer, so the two maps agree.
  rw [mapM_congr keys, domain]
  exact valid

/-- One slot keeps the public keys as a prefix, and keeps distinct keys distinct. -/
theorem keys_advanceSlot {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after) :
    validatorKeys state <+: validatorKeys after ∧
      (PubkeysDistinct state → PubkeysDistinct after) := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have first := frame_processSlot cachedOk
  -- The epoch step is justification, which keeps the registry, then an epoch frame.
  have second : validatorKeys cached <+: validatorKeys epoched ∧
      (PubkeysDistinct cached → PubkeysDistinct epoched) := by
    obtain ⟨_, epochedOk⟩ | ⟨_, rfl⟩ := epochIfLast_cases epochedOk
    · obtain ⟨justified, justifiedOk, frame⟩ := processEpoch_frame epochedOk
      have same : validatorKeys justified = validatorKeys cached := by
        unfold validatorKeys
        rw [(processJustificationAndFinalization_keeps justifiedOk).2.2.2.2.2.1]
      have kept := frame.toFrame.pubkeysPrefix
      have distinct := frame.toFrame.pubkeysDistinct
      rw [same] at kept
      unfold PubkeysDistinct at distinct
      rw [same] at distinct
      exact ⟨kept, distinct⟩
    · exact ⟨List.prefix_refl _, id⟩
  exact ⟨first.pubkeysPrefix.trans second.1, second.2 ∘ first.pubkeysDistinct⟩

/-- One step of a chain keeps the public keys as a prefix, and keeps distinct keys distinct. -/
private theorem keys_chainStep {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    validatorKeys forked.state <+: validatorKeys after.state ∧
      (PubkeysDistinct forked.state → PubkeysDistinct after.state) := by
  -- The prefix and the distinct keys hold at every fork that the specification covers.
  --
  -- They hold for slots, epochs, blocks and upgrades.
  cases step with
  | slot computed =>
    obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
    -- Each upgrade is an upgrade frame, which carries the keys.
    obtain ⟨kept, distinct⟩ := processUpgrades_induction
      (property := fun upgraded =>
        validatorKeys advanced <+: validatorKeys upgraded.state ∧
          (PubkeysDistinct advanced → PubkeysDistinct upgraded.state))
      (fun holds stepOk =>
        have frame := upgradeFrame_upgradeNext stepOk
        ⟨holds.1.trans frame.pubkeysPrefix, frame.pubkeysDistinct ∘ holds.2⟩)
      ⟨List.prefix_refl _, id⟩ upgraded
    obtain ⟨first, firstDistinct⟩ := keys_advanceSlot advancedOk
    exact ⟨first.trans kept, distinct ∘ firstDistinct⟩
  | block engine signed validateResult computed =>
    obtain ⟨-, blockOk, -⟩ := applySignedBlock_ok computed
    -- A deposit to a key that a validator has adds no validator.
    --
    -- A deposit to a key that no validator has adds at most one validator.
    --
    -- That validator goes at the end of the registry, with that key.
    --
    -- A deposit with an invalid signature adds none.
    --
    -- From Heze, a pending deposit to a new key with BLS withdrawal credentials adds none.
    --
    -- Before Electra a block credits a deposit at once.
    --
    -- From Electra a block registers a new key with no balance and queues the deposit.
    --
    -- A pending deposit, applied at an epoch, then raises a balance or adds a validator.
    have frame := frame_processBlock blockOk
    exact ⟨frame.pubkeysPrefix, frame.pubkeysDistinct⟩

/-- Along a run of steps of a chain, the public keys of the first state are a prefix of the last.

Keys that are distinct in the first state are distinct in the last.

So a chain from a later state keeps its keys distinct when they are distinct in that state. -/
theorem validatorKeys_prefix_and_distinct_of_chainSteps {first last : ForkedBeaconState preset}
    (steps : Relation.ReflTransGen (ChainStep config checks) first last) :
    validatorKeys first.state <+: validatorKeys last.state ∧
      (PubkeysDistinct first.state → PubkeysDistinct last.state) := by
  induction steps with
  | refl => exact ⟨List.prefix_refl _, id⟩
  | tail _ step more =>
    obtain ⟨kept, distinct⟩ := keys_chainStep step
    exact ⟨more.1.trans kept, distinct ∘ more.2⟩

/-- Along a chain from genesis, the public keys of the validators stay a prefix and stay distinct.

The keys of the genesis state, built from deposits, are a prefix of the keys of every state.

The keys of every state of the chain are distinct.

The specification defines genesis only before Altair. -/
theorem validatorKeys_prefix_and_distinct_of_genesis_chainSteps
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {genesis : BeaconState preset fork} {last : ForkedBeaconState preset}
    {before : fork < .altair}
    (initialized :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok genesis)
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, genesis⟩ last) :
    validatorKeys genesis <+: validatorKeys last.state ∧ PubkeysDistinct last.state := by
  obtain ⟨genesisTime, bodyRoot, _, root, frame, rfl⟩ :=
    initializeBeaconStateFromEth1_frame initialized
  -- The empty state before the deposits has no validator, so no two share a key.
  have empty : PubkeysDistinct (emptyGenesisState (preset := preset) config before genesisTime
      eth1BlockHash deposits.size.toUInt64 bodyRoot) := by
    simp [PubkeysDistinct, validatorKeys, emptyGenesisState]
  -- The genesis state has distinct keys, since it is built from the empty registry by deposits.
  have distinct := frame.pubkeysDistinct empty
  obtain ⟨kept, carried⟩ := validatorKeys_prefix_and_distinct_of_chainSteps steps
  exact ⟨kept, carried distinct⟩

/-- The key at a registry position, or the default key past the end. -/
def keyAt (state : BeaconState preset fork) (i : Nat) : Cryptography.Bls.BLSPubkey :=
  ((state.validators.data[i]?).map (·.pubkey)).getD default

end EthLib.Consensus
