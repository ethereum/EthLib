module

public import EthLib.Consensus.BuilderApi.GloasBid

/-!
# Proofs: the Gloas checks of a request for a bid and of a fetched bid

A Gloas builder serves a request exactly when its six rules hold.

So it serves only the key of the proposer of the slot, and only while that proposer is active.

A proposer accepts a fetched bid exactly when its eight rules hold and the signature verifies.

The builder's funds are checked only for a bid of positive value.

A bid that names the index of a self-built payload is never accepted.

While the registry of builders is shorter than that index, the check of an active builder fails.
-/

@[expose] public section

namespace EthLib.Consensus.BuilderApi

open Base Cryptography.Bls Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- Simplifies the `Except` plumbing of the checks, using every hypothesis. -/
local macro "gsimp" : tactic =>
  `(tactic| simp [*, Option.isSome_iff_ne_none, liftAccessor, liftSsz, Except.mapError, bind,
    Except.bind, pure, Except.pure])

/-- A Gloas builder serves a request exactly when the six rules hold. -/
theorem isEligibleForBidGloas_ok_true_iff {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {preferences : ValidatorIndex → Option ProposerPreferences}
    {slot : Slot} {parentHash : Hash32} {parentRoot : Root} {pubkey : BLSPubkey} :
    isEligibleForBidGloas state gloas preferences slot parentHash parentRoot pubkey = .ok true ↔
      slot = state.slot ∧
      (∃ index proposer, getBeaconProposerIndex state = .ok index ∧
        getValidator state index = .ok proposer ∧ proposer.pubkey = pubkey ∧
        isActiveValidator proposer (getCurrentEpoch state) = true ∧
        (preferences index).isSome) ∧
      isParentBlockHash state gloas parentHash = true ∧
      SszType.hashTreeRoot state.latestBlockHeader = .ok parentRoot := by
  unfold isEligibleForBidGloas
  by_cases hs : slot = state.slot
  · cases hi : getBeaconProposerIndex state with
    | error e => gsimp
    | ok index =>
      cases hv : getValidator state index with
      | error e => gsimp
      | ok proposer =>
        by_cases hk : proposer.pubkey = pubkey
        · by_cases ha : isActiveValidator proposer (getCurrentEpoch state) = true
          · by_cases hp : preferences index = none
            · gsimp
            · by_cases hh : isParentBlockHash state gloas parentHash = true
              · cases hr : SszType.hashTreeRoot state.latestBlockHeader with
                | error e => gsimp
                | ok root =>
                  by_cases he : root = parentRoot
                  · subst he
                    gsimp
                  · gsimp
                    exact fun same => he same.symm
              · gsimp
          · gsimp
        · gsimp
  · simp [hs, pure, Except.pure]

/-- A request that a Gloas builder serves names the key of the active proposer of the slot. -/
theorem isEligibleForBidGloas_proposer {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {preferences : ValidatorIndex → Option ProposerPreferences}
    {slot : Slot} {parentHash : Hash32} {parentRoot : Root} {pubkey : BLSPubkey}
    (served :
      isEligibleForBidGloas state gloas preferences slot parentHash parentRoot pubkey = .ok true) :
    ∃ index proposer, getBeaconProposerIndex state = .ok index ∧
      getValidator state index = .ok proposer ∧ proposer.pubkey = pubkey ∧
      isActiveValidator proposer (getCurrentEpoch state) = true := by
  obtain ⟨-, ⟨index, proposer, found, read, key, active, -⟩, -⟩ :=
    isEligibleForBidGloas_ok_true_iff.1 served
  exact ⟨index, proposer, found, read, key, active⟩

/-- A proposer accepts a fetched bid exactly when the eight rules hold and the signature verifies.

The builder's funds count only for a bid of positive value. -/
theorem validateBid_ok_true_iff {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {preferences : ProposerPreferences} {parentGasLimit : UInt64}
    {signed : SignedExecutionPayloadBid preset fork} {feeRecipient : ExecutionAddress} :
    validateBid config checks state gloas preferences parentGasLimit signed feeRecipient =
        .ok true ↔
      isActiveBuilder state gloas signed.message.builderIndex = .ok true ∧
      signed.message.slot = state.slot ∧
      signed.message.feeRecipient = feeRecipient ∧
      isParentBlockHash state gloas signed.message.parentBlockHash = true ∧
      SszType.hashTreeRoot state.latestBlockHeader = .ok signed.message.parentBlockRoot ∧
      getRandaoMix state (getCurrentEpoch state) = .ok signed.message.prevRandao ∧
      isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
        preferences.targetGasLimit = .ok true ∧
      (0 < signed.message.value →
        canBuilderCoverBid state gloas signed.message.builderIndex signed.message.value =
          .ok true) ∧
      verifyExecutionPayloadBidSignature config checks state gloas signed = .ok true := by
  unfold validateBid
  simp only [liftAccessor, liftSsz, liftArith, Except.mapError, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw]
  generalize isActiveBuilder state gloas signed.message.builderIndex = active
  generalize SszType.hashTreeRoot state.latestBlockHeader = root
  generalize getRandaoMix state (getCurrentEpoch state) = randao
  generalize isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
    preferences.targetGasLimit = gas
  generalize canBuilderCoverBid state gloas signed.message.builderIndex signed.message.value =
    cover
  generalize verifyExecutionPayloadBidSignature config checks state gloas signed = sig
  by_cases h2 : signed.message.slot = state.slot <;>
  by_cases h3 : signed.message.feeRecipient = feeRecipient <;>
  by_cases h4 : isParentBlockHash state gloas signed.message.parentBlockHash = true <;>
  rcases active with _ | (_ | _) <;> (try simp [*]) <;>
  rcases root with _ | root <;> (try simp [*]) <;>
  by_cases h5 : root = signed.message.parentBlockRoot <;> (try have h5' := Ne.symm h5) <;>
  (try simp [*]) <;>
  rcases randao with _ | randao <;> (try simp [*]) <;>
  by_cases h6 : randao = signed.message.prevRandao <;> (try have h6' := Ne.symm h6) <;>
  (try simp [*]) <;>
  rcases gas with _ | (_ | _) <;> (try simp [*]) <;>
  rcases cover with _ | (_ | _) <;> rcases sig with _ | (_ | _) <;>
  by_cases hv : 0 < signed.message.value <;> simp [*]

/-- A bid of value zero is never refused for the funds of its builder. -/
theorem validateBid_zero_value {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {preferences : ProposerPreferences} {parentGasLimit : UInt64}
    {signed : SignedExecutionPayloadBid preset fork} {feeRecipient : ExecutionAddress}
    (zero : signed.message.value = 0) :
    validateBid config checks state gloas preferences parentGasLimit signed feeRecipient ≠
      .error .cannotCoverBid := by
  have hv : ¬0 < signed.message.value := by simp [zero]
  unfold validateBid
  simp only [liftAccessor, liftSsz, liftArith, Except.mapError, bind, Except.bind, throw,
    throwThe, MonadExceptOf.throw, hv, ite_false]
  generalize isActiveBuilder state gloas signed.message.builderIndex = active
  generalize SszType.hashTreeRoot state.latestBlockHeader = root
  generalize getRandaoMix state (getCurrentEpoch state) = randao
  generalize isGasLimitTargetCompatible parentGasLimit signed.message.gasLimit
    preferences.targetGasLimit = gas
  generalize verifyExecutionPayloadBidSignature config checks state gloas signed = sig
  rcases active with _ | (_ | _) <;> (try simp) <;>
  by_cases h2 : signed.message.slot = state.slot <;> (try simp [h2]) <;>
  by_cases h3 : signed.message.feeRecipient = feeRecipient <;> (try simp [h3]) <;>
  by_cases h4 : isParentBlockHash state gloas signed.message.parentBlockHash = true <;>
  (try simp [h4]) <;>
  rcases root with _ | root <;> (try simp) <;>
  by_cases h5 : signed.message.parentBlockRoot = root <;> (try simp [h5]) <;>
  rcases randao with _ | randao <;> (try simp) <;>
  by_cases h6 : signed.message.prevRandao = randao <;> (try simp [h6]) <;>
  rcases gas with _ | (_ | _) <;> (try simp) <;>
  rcases sig with _ | (_ | _) <;> simp

/-- A bid that names the index of a self-built payload is never accepted.

This holds while the registry of builders is shorter than that index. -/
theorem validateBid_not_selfBuild {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {preferences : ProposerPreferences} {parentGasLimit : UInt64}
    {signed : SignedExecutionPayloadBid preset fork} {feeRecipient : ExecutionAddress}
    (short : (state.builders gloas).data.size < 2 ^ 64 - 1)
    (self : signed.message.builderIndex = BUILDER_INDEX_SELF_BUILD) :
    validateBid config checks state gloas preferences parentGasLimit signed feeRecipient ≠
      .ok true := by
  have hnone : (state.builders gloas).data[signed.message.builderIndex.toNat]? = none := by
    refine Array.getElem?_eq_none ?_
    rw [self]
    have h : (UInt64.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 := by simp
    simp only [BUILDER_INDEX_SELF_BUILD]
    omega
  obtain ⟨e, he⟩ : ∃ e, isActiveBuilder state gloas signed.message.builderIndex = .error e := by
    simp [isActiveBuilder, getBuilder, hnone, bind, Except.bind]
  unfold validateBid
  simp [liftAccessor, Except.mapError, bind, Except.bind, he]

end EthLib.Consensus.BuilderApi
