module

public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Transition.Block

/-!
# Proofs: when a block accepts an attester slashing of one validator

An attester slashing carries two indexed attestations.

Here each names one validator only, by the same index.

Then the state accepts the slashing exactly when it can slash the validator.

That last step can fail for reasons outside the slashing, such as checked arithmetic.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork}

/-- A signature by one key verifies on an attestation data in the domain that a state reads.

The domain is the attester domain at the target epoch of the data. -/
def SignsAttestationAt (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (key : Cryptography.Bls.BLSPubkey) (data : AttestationData)
    (signature : Cryptography.Bls.BLSSignature) : Prop :=
  ∃ domain root,
    getDomain config state DOMAIN_BEACON_ATTESTER (some data.target.epoch) = .ok domain ∧
      computeSigningRoot data domain = .ok root ∧
      checks.fastAggregateVerify #[key] (packBytes root) signature = true

/-- The set of one index is that index alone. -/
private theorem sortedSet_singleton (index : ValidatorIndex) : sortedSet [index] = [index] := by
  simp [sortedSet, keepNew]

/-- An indexed attestation of one validator, signed by its key, is valid.

From Gloas the limit of attesters must be at least one. -/
private theorem isValidIndexedAttestation_single {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {attestation : IndexedAttestation preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (single : attestation.attestingIndices.data.toList = [index])
    (bounded : .glamsterdam ≤ fork → 1 ≤ maxAttesters preset fork)
    (found : getValidator state index = .ok validator)
    (signs : SignsAttestationAt config checks state validator.pubkey attestation.data
      attestation.signature) :
    isValidIndexedAttestation config checks state attestation = .ok true := by
  obtain ⟨domain, root, domained, rooted, verifies⟩ := signs
  have passes : ¬ ([index] = [] ∨ [index] ≠ sortedSet [index] ∨
      (.glamsterdam ≤ fork ∧ maxAttesters preset fork < [index].length)) := by
    rw [sortedSet_singleton]
    rintro (empty | unsorted | ⟨gloas, over⟩)
    · exact List.cons_ne_nil _ _ empty
    · exact unsorted rfl
    · exact Nat.not_lt_of_ge (bounded gloas) over
  simp only [isValidIndexedAttestation, single]
  rw [ite_eq_right passes]
  -- The key of the one index, the domain and the signing root all read as the signature needs.
  simp [Array.mapM_eq_mapM_toList, found, domained, rooted, verifies, liftAccessor, liftSsz,
    Except.mapError, bind, Except.bind, pure, Except.pure, List.mapM_cons, Functor.map,
    Except.map]

/-- An attester slashing of one validator by its two signatures does what slashing it does.

The state accepts the slashing exactly when it can slash the validator, with the same result. -/
theorem processAttesterSlashing_eq_slashValidator_of_single {config : Config}
    {checks : SignatureChecks}
    {state : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    {index : ValidatorIndex} {validator : Validator}
    -- The first attestation names the validator alone, so it carries the signature of that key.
    (first : slashing.attestation1.attestingIndices.data.toList = [index])
    -- The second attestation names the validator alone too.
    (second : slashing.attestation2.attestingIndices.data.toList = [index])
    -- The two data are a double or surround vote.
    (conflict :
      isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true)
    (found : getValidator state index = .ok validator)
    -- The validator is slashable at the epoch of the state.
    --
    -- So it is not slashed, it is activated, and it is not yet withdrawable.
    (slashable : isSlashableValidator validator (getCurrentEpoch state) = true)
    -- The first signature verifies in the attester domain that the state reads at its target epoch.
    (signedFirst : SignsAttestationAt config checks state validator.pubkey
      slashing.attestation1.data slashing.attestation1.signature)
    -- The second signature verifies in the same way, at the target epoch of its own data.
    (signedSecond : SignsAttestationAt config checks state validator.pubkey
      slashing.attestation2.data slashing.attestation2.signature)
    -- From Gloas, the limit of attesters of an indexed attestation is at least one.
    (bounded : .glamsterdam ≤ fork → 1 ≤ maxAttesters preset fork) :
    processAttesterSlashing config checks state slashing =
      liftAccessor (slashValidator config state index) := by
  have valid1 := isValidIndexedAttestation_single first bounded found signedFirst
  have valid2 := isValidIndexedAttestation_single second bounded found signedSecond
  -- The validators in both attestations are the one index.
  have indices : slashingIndices slashing = [index] := by
    simp [slashingIndices, first, second, sortedSet_singleton]
  -- The one step of the slashing is the slashing of the validator, which succeeds or fails.
  cases slashes : slashValidator config state index with
  | error fault =>
    have folded : [index].foldlM (slashIfSlashable config) (state, false) =
        .error (.accessor fault) := by
      simp [slashIfSlashable, found, slashable, slashes, liftAccessor, Except.mapError, bind,
        Except.bind]
    simp [processAttesterSlashing, conflict, valid1, valid2, indices, folded, ensure, bind,
      Except.bind, liftAccessor, Except.mapError]
  | ok slashed =>
    have folded : [index].foldlM (slashIfSlashable config) (state, false) =
        .ok (slashed, true) := by
      simp [slashIfSlashable, found, slashable, slashes, liftAccessor, Except.mapError, bind,
        Except.bind, pure, Except.pure]
    simp [processAttesterSlashing, conflict, valid1, valid2, indices, folded, ensure, bind,
      Except.bind, pure, Except.pure, liftAccessor, Except.mapError]

end EthLib.Consensus
