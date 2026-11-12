module

public import EthLib.Consensus.Proofs.Transition.Chain
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Proofs: the validator keys along a chain

A chain of beacon states runs from the genesis state, one step at a time.

A step never overwrites the public key of a validator.

A deposit to a key that a validator has adds no validator.

A deposit to a key that no validator has adds at most one validator.

That validator goes at the end of the registry, with that key.

A deposit with an invalid signature adds none.

From Heze, a pending deposit to a new key with BLS withdrawal credentials adds none.

Before Electra a block credits a deposit at once.

From Electra a block registers a new key with no balance and queues the deposit.

A pending deposit, applied at an epoch, then raises a balance or adds a validator.

So the public keys before a step are a prefix of the keys after it.

Keys that are distinct before a step are distinct after it.

That holds at every fork the specification covers, for slots, epochs, blocks and upgrades.

The genesis state has distinct keys, since it is built from the empty registry by deposits.

So along a chain from genesis the keys of the validators stay distinct.

The specification defines genesis only before Altair.

A chain from a later state keeps its keys distinct when they are distinct in that state.
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

/-- One slot keeps the public keys as a prefix, and keeps distinct keys distinct. -/
private theorem keys_advanceSlot {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after) :
    validatorKeys state <+: validatorKeys after ∧
      (PubkeysDistinct state → PubkeysDistinct after) := by
  obtain ⟨next, cached, epoched, _, cachedOk, epochedOk, rfl⟩ := advanceSlot_ok computed
  have first := frame_processSlot cachedOk
  -- The epoch step is justification, which keeps the registry, then an epoch frame.
  have second : validatorKeys cached <+: validatorKeys epoched ∧
      (PubkeysDistinct cached → PubkeysDistinct epoched) := by
    unfold epochIfLast at epochedOk
    split at epochedOk
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
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact ⟨List.prefix_refl _, id⟩
  exact ⟨first.pubkeysPrefix.trans second.1, second.2 ∘ first.pubkeysDistinct⟩

/-- One step of a chain keeps the public keys as a prefix, and keeps distinct keys distinct. -/
private theorem keys_chainStep {forked after : ForkedBeaconState preset}
    (step : ChainStep config checks forked after) :
    validatorKeys forked.state <+: validatorKeys after.state ∧
      (PubkeysDistinct forked.state → PubkeysDistinct after.state) := by
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
    have frame := frame_processBlock blockOk
    exact ⟨frame.pubkeysPrefix, frame.pubkeysDistinct⟩

/-- Along a run of steps of a chain, the public keys of the first state are a prefix of the last.

Keys that are distinct in the first state are distinct in the last. -/
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

The keys of every state of the chain are distinct. -/
theorem validatorKeys_prefix_and_distinct_of_genesis_chainSteps
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {genesis : BeaconState preset fork} {last : ForkedBeaconState preset}
    (initialized :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
        .ok genesis)
    (steps : Relation.ReflTransGen (ChainStep config checks) ⟨fork, genesis⟩ last) :
    validatorKeys genesis <+: validatorKeys last.state ∧ PubkeysDistinct last.state := by
  obtain ⟨before, genesisTime, bodyRoot, _, root, frame, rfl⟩ :=
    initializeBeaconStateFromEth1_frame initialized
  -- The empty state before the deposits has no validator, so no two share a key.
  have empty : PubkeysDistinct (emptyGenesisState (preset := preset) config before genesisTime
      eth1BlockHash deposits.size.toUInt64 bodyRoot) := by
    simp [PubkeysDistinct, validatorKeys, emptyGenesisState]
  have distinct := frame.pubkeysDistinct empty
  obtain ⟨kept, carried⟩ := validatorKeys_prefix_and_distinct_of_chainSteps steps
  exact ⟨kept, carried distinct⟩

end EthLib.Consensus
