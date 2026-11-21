module

public import EthLib.Consensus.BuilderApi.Submit
public import EthLib.Consensus.Proofs.BuilderApi

/-!
# Proofs: the answer of a builder to a signed blinded block

Each endpoint answers its success exactly when the block is valid for the builder.

It answers 400 exactly when the block is not.

A block whose proposer signature fails on the state of its slot gets 400.

So the separate check of the signature of a blinded block adds nothing to the transition.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork} {state : BeaconState preset fork}
  {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork}
  {signed : SignedBlindedBeaconBlock preset fork}

/-- A signed blinded block that unblinds keeps its slot. -/
private theorem unblind_slot {range : HasBuilderApi fork} {payload : ExecutionPayload preset fork}
    {full : SignedBeaconBlock preset fork} (made : signed.unblind range payload = .ok full) :
    full.message.slot = signed.message.slot := by
  cases block : signed.message.unblind range payload with
  | error e => simp [SignedBlindedBeaconBlock.unblind, block, bind, Except.bind] at made
  | ok fullBlock =>
    simp only [SignedBlindedBeaconBlock.unblind, block, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at made
    subst made
    cases body : signed.message.body.unblind range payload with
    | error e => simp [BlindedBeaconBlock.unblind, body, bind, Except.bind] at block
    | ok fullBody =>
      simp only [BlindedBeaconBlock.unblind, body, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at block
      subst block
      rfl

/-- An endpoint answers its success exactly when the block is valid for the builder. -/
theorem submitBlindedBlockStatus_eq_success_iff {version : SubmitVersion} :
    submitBlindedBlockStatus config checks engine state range payload signed version =
        version.success ↔
      ValidBlindedBlock config checks engine state range payload signed := by
  unfold submitBlindedBlockStatus ValidBlindedBlock
  cases made : signed.unblind range payload with
  | error e => cases version <;> simp [SubmitVersion.success]
  | ok full =>
    cases run : stateTransition config checks engine state full with
    | error e => cases version <;> simp [SubmitVersion.success, run]
    | ok post => cases version <;> simp [SubmitVersion.success, run]

/-- An endpoint answers 400 exactly when the block is not valid for the builder. -/
theorem submitBlindedBlockStatus_eq_400_iff {version : SubmitVersion} :
    submitBlindedBlockStatus config checks engine state range payload signed version = 400 ↔
      ¬ ValidBlindedBlock config checks engine state range payload signed := by
  unfold submitBlindedBlockStatus ValidBlindedBlock
  cases made : signed.unblind range payload with
  | error e => simp
  | ok full =>
    cases run : stateTransition config checks engine state full with
    | error e => simp [run]
    | ok post => cases version <;> simp [SubmitVersion.success, run]

/-- A block whose proposer signature fails gets 400, at both endpoints.

The signature is checked on the state at the slot of the block, whose proposer the block names.

The logs bloom of the preset is not empty, as in every preset of the source. -/
theorem submitBlindedBlockStatus_of_signature [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    {version : SubmitVersion}
    {pre : BeaconState preset fork}
    (slots : processSlots config checks state signed.message.slot = .ok pre)
    (proposer : getBeaconProposerIndex pre = .ok signed.message.proposerIndex)
    (bad : verifyBlindedBlockSignature config checks pre signed = .ok false) :
    submitBlindedBlockStatus config checks engine state range payload signed version = 400 := by
  unfold submitBlindedBlockStatus
  cases made : signed.unblind range payload with
  | error e => simp
  | ok full =>
    have sig := verifyBlockSignature_unblind (config := config) (checks := checks) made proposer
    have slot := unblind_slot made
    cases run : stateTransition config checks engine state full with
    | error e => simp [run]
    | ok post =>
      exfalso
      have fail : stateTransition config checks engine state full = .error
          (.invalidBlockSignature full.message.proposerIndex full.message.slot) := by
        simp only [stateTransition, applySignedBlock, checkBlockSignature, slot, slots, sig, bad,
          bind, Except.bind, pure, Except.pure, ensure]
        simp
      rw [fail] at run
      cases run

end EthLib.Consensus.BuilderApi
