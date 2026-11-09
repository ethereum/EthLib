module

public import EthLib.Consensus.Proofs.HonestAggregation
public import EthLib.Consensus.Transition.Block
import EthLib.Cryptography.Proofs.Bls.AggregatePerm
import EthLib.Consensus.Proofs.Gossip.Attestation
import Mathlib.Data.List.Sort

/-!
# Proofs: honest attestation aggregates pass their signature check

The indexed attestation sorts its validator indices before reading their keys.

Distinct honest signers give the same keys, with the same multiplicities, in that order.

Their aggregate key must not be zero, and the number of signers must fit the indexed check.

The aggregate topic runs this same indexed attestation check.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz
open Networking.Gossip Networking.Gossip.ValidationResult
open scoped EthLib.Cryptography.Bls.Fr

variable {preset : Preset} {fork : Fork}

/-- Each member on the left of a pointwise relation has a related member on the right. -/
private theorem exists_related_of_mem {α β : Type} {R : α → β → Prop}
    {xs : List α} {ys : List β} (related : List.Forall₂ R xs ys)
    {x : α} (member : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction related with
  | nil => cases member
  | @cons head other xs ys headRelated tailRelated ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨other, List.mem_cons_self, headRelated⟩
    · obtain ⟨y, member, related⟩ := ih member
      exact ⟨y, List.mem_cons_of_mem _ member, related⟩

/-- A signature of attestation data fixes a domain and a signing root for that data. -/
private theorem attestation_signing_root {config : Config} {state : BeaconState preset fork}
    {data : AttestationData} {key : Signatures.SecretKey} {signature : BLSSignature}
    (signed : getAttestationSignature config state data key = .ok signature) :
    ∃ domain root,
      getDomain config state DOMAIN_BEACON_ATTESTER (some data.target.epoch) = .ok domain ∧
      computeSigningRoot data domain = .ok root := by
  unfold getAttestationSignature signAtEpoch at signed
  obtain ⟨domain, domained, signed⟩ := bind_ok_iff.mp signed
  obtain ⟨root, rooted, _⟩ := bind_ok_iff.mp signed
  exact ⟨domain, root, mapError_ok_iff.mp domained, mapError_ok_iff.mp rooted⟩

/-- A duty signature is the BLS signature of its computed signing root. -/
private theorem attestation_sign_eq {config : Config} {state : BeaconState preset fork}
    {data : AttestationData} {key : Signatures.SecretKey} {signature : BLSSignature}
    {domain : Domain} {root : Root}
    (domained :
      getDomain config state DOMAIN_BEACON_ATTESTER (some data.target.epoch) = .ok domain)
    (rooted : computeSigningRoot data domain = .ok root)
    (signed : getAttestationSignature config state data key = .ok signature) :
    Signatures.sign key (Base.packBytes root) = .ok signature := by
  unfold getAttestationSignature signAtEpoch at signed
  obtain ⟨domain', domained', signed⟩ := bind_ok_iff.mp signed
  rw [mapError_ok_iff, domained, Except.ok.injEq] at domained'
  subst domained'
  obtain ⟨root', rooted', signed⟩ := bind_ok_iff.mp signed
  rw [mapError_ok_iff, rooted, Except.ok.injEq] at rooted'
  subst rooted'
  exact mapError_ok_iff.mp signed

/-- Sorted attesters read the same public keys as a permutation of their honest signers. -/
private theorem indexed_attestation_of_aggregate {config : Config}
    {state : BeaconState preset fork} {data : AttestationData}
    {attestation : Attestation preset fork} {indices signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {signatures : List BLSSignature}
    {domain : Domain} {root : Root}
    (computed : getAttestingIndices state attestation = .ok indices)
    (sameData : attestation.data = data) (permuted : indices.Perm signers)
    (nonempty : signers ≠ [])
    (bounded : .glamsterdam ≤ fork → signers.length ≤ maxAttesters preset fork)
    (registered : ∀ index ∈ signers, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (domained :
      getDomain config state DOMAIN_BEACON_ATTESTER (some data.target.epoch) = .ok domain)
    (rooted : computeSigningRoot data domain = .ok root)
    (signed : List.Forall₂ (fun secret signature =>
      Signatures.sign secret (Base.packBytes root) = .ok signature) (signers.map key) signatures)
    (sum : ((signers.map key).map (·.val)).sum ≠ 0)
    (aggregated : Signatures.aggregate (signatures.map Signatures.sigBytes).toArray =
      .ok attestation.signature) :
    ∃ indexed, getIndexedAttestation state attestation = .ok indexed ∧
      isValidIndexedAttestation config .bls state indexed = .ok true := by
  obtain ⟨indexed, indexedOf, sameIndices, indexedData, indexedSignature⟩ :=
    getIndexedAttestation_of_getAttestingIndices computed
  have ordered := getAttestingIndices_sorted computed
  have fixed : indices = sortedSet indices :=
    ordered.eq_of_mem_iff (sortedSet_sorted _) fun _ => mem_sortedSet.symm
  have nonemptyIndices : indices ≠ [] := by
    intro empty
    exact nonempty (empty ▸ permuted.symm).eq_nil
  have keysOf : indices.toArray.mapM (fun index => do
      return Base.packBytes (← liftAccessor (getValidator state index)).pubkey) =
        .ok ((indices.map fun index => Signatures.pkBytes (key index)).toArray) := by
    rw [Array.mapM_eq_mapM_toList]
    have mapped := mapM_eq_ok_map (xs := indices)
      (f := fun index => do
        return Base.packBytes (← liftAccessor (getValidator state index)).pubkey)
      (g := fun index => Signatures.pkBytes (key index)) fun index member => by
        obtain ⟨validator, found, owned⟩ :=
          registered index (permuted.mem_iff.mp member)
        simp only [found, liftAccessor, Except.mapError, bind, Except.bind, pure, Except.pure,
          owned, Signatures.pkBytes, Base.packBytes]
    rw [mapped]
    rfl
  have verifies := Signatures.fastAggregateVerify_aggregate_of_forall₂
    signed (by simpa using nonempty) sum aggregated
  have permutes := Signatures.fastAggregateVerify_pkBytes_perm (permuted.map key)
    (Base.packBytes root) (Signatures.sigBytes attestation.signature)
  have verifiesSorted : Signatures.fastAggregateVerify
      ((indices.map fun index => Signatures.pkBytes (key index)).toArray)
      (Base.packBytes root) (Base.packBytes attestation.signature) = true := by
    simpa only [List.map_map, Function.comp_def, Signatures.sigBytes, Base.packBytes]
      using permutes.trans verifies
  refine ⟨indexed, indexedOf, ?_⟩
  unfold isValidIndexedAttestation
  have readIndices : indexed.attestingIndices.data.toList = indices := by
    rw [sameIndices]
  rw [readIndices]
  have passes : ¬ (indices = [] ∨ indices ≠ sortedSet indices ∨
      (.glamsterdam ≤ fork ∧ maxAttesters preset fork < indices.length)) := by
    intro bad
    rcases bad with empty | unsorted | ⟨gloas, over⟩
    · exact nonemptyIndices empty
    · exact unsorted fixed
    · have lengthBound : indices.length ≤ maxAttesters preset fork := by
        rw [permuted.length_eq]
        exact bounded gloas
      exact Nat.not_lt_of_ge lengthBound over
  rw [ite_eq_right passes, keysOf]
  simpa only [indexedData, sameData, domained, rooted, liftAccessor, liftSsz, Except.mapError,
    bind, Except.bind, pure, Except.pure, SignatureChecks.bls, indexedSignature]
    using congrArg (Except.ok (ε := TransitionError)) verifiesSorted

/-- Before Electra, an aggregate of distinct honest attesters passes the indexed signature check.

The registry must hold each signer's public key, and their keys must not sum to zero.

The attestation's size bound also bounds its distinct signers. -/
theorem isValidIndexedAttestation_constructAggregate {config : Config}
    {state : BeaconState preset fork} {before : fork < .pectra} {data : AttestationData}
    {signers : List ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {attestations : List (Attestation preset fork)} {aggregate : Attestation preset fork}
    (honest : List.Forall₂ (fun index attestation =>
      constructAttestation config state before data index (key index) = .ok attestation)
        signers (attestations.filter (·.data = data)))
    (distinct : signers.Nodup)
    (registered : ∀ index ∈ signers, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : ((signers.map key).map (·.val)).sum ≠ 0)
    (built : constructAggregate state before data attestations = .ok aggregate) :
    ∃ indexed, getIndexedAttestation state aggregate = .ok indexed ∧
      isValidIndexedAttestation config .bls state indexed = .ok true := by
  obtain ⟨_, _, _, _, _, sameData, aggregateSignature⟩ := constructAggregate_spec built
  obtain ⟨indices, computed, members⟩ := mem_getAttestingIndices_constructAggregate built
  have indexMembers : ∀ index, index ∈ indices ↔ index ∈ signers := by
    intro index
    rw [members]
    constructor
    · rintro ⟨attestation, member, same, attesters, attestersOf, attesting⟩
      obtain ⟨signer, signerMember, made⟩ := exists_related_of_mem honest.flip
        (List.mem_filter.mpr ⟨member, by simp [same]⟩)
      rw [getAttestingIndices_constructAttestation made, Except.ok.injEq] at attestersOf
      subst attestersOf
      have same : index = signer := by simpa using attesting
      exact same.symm ▸ signerMember
    · intro member
      obtain ⟨attestation, attestationMember, made⟩ := exists_related_of_mem honest member
      obtain ⟨rawMember, same⟩ := List.mem_filter.mp attestationMember
      exact ⟨attestation, rawMember, by simpa using same,
        [index], getAttestingIndices_constructAttestation made, by simp⟩
  have permuted : indices.Perm signers :=
    (List.perm_ext_iff_of_nodup (getAttestingIndices_sorted computed).nodup distinct).mpr
      indexMembers
  have nonempty : signers ≠ [] := by
    intro empty
    simp [empty] at sum
  obtain ⟨signer, signerMember⟩ := List.exists_mem_of_ne_nil signers nonempty
  obtain ⟨attestation, _, made⟩ := exists_related_of_mem honest signerMember
  obtain ⟨_, _, _, _, _, signedOne⟩ := constructAttestation_spec made
  obtain ⟨domain, root, domained, rooted⟩ := attestation_signing_root signedOne
  have signed : List.Forall₂ (fun secret signature =>
      Signatures.sign secret (Base.packBytes root) = .ok signature)
      (signers.map key) ((attestations.filter (·.data = data)).map (·.signature)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact honest.imp fun _ _ made =>
      attestation_sign_eq domained rooted (constructAttestation_spec made).choose_spec.2.2.2.2
  have bounded : .glamsterdam ≤ fork → signers.length ≤ maxAttesters preset fork := by
    intro gloas
    exact False.elim (Nat.not_le_of_lt before (le_trans (by decide) gloas))
  apply indexed_attestation_of_aggregate computed sameData permuted nonempty bounded registered
    domained rooted signed sum
  simpa only [getAggregateSignature, List.map_map, Function.comp_def, Signatures.sigBytes,
    Base.packBytes] using aggregateSignature

/-- A single attestation holds its signer's index, committee, data and signature. -/
private theorem single_attestation_spec {config : Config} {state : BeaconState preset fork}
    {data : AttestationData} {committeeIndex : CommitteeIndex} {index : ValidatorIndex}
    {key : Signatures.SecretKey} {single : SingleAttestation}
    (made : constructSingleAttestation config state data committeeIndex index key = .ok single) :
    single.attesterIndex = index ∧ single.data = data ∧
      single.committeeIndex = committeeIndex ∧
      getAttestationSignature config state data key = .ok single.signature := by
  unfold constructSingleAttestation at made
  obtain ⟨signature, signed, made⟩ := bind_ok_iff.mp made
  simp only [pure, Except.pure, Except.ok.injEq] at made
  subst made
  exact ⟨rfl, rfl, rfl, signed⟩

/-- From Electra, an aggregate of distinct honest single attesters passes its indexed check.

The registry must hold each signer's public key, and their keys must not sum to zero.

The number of signers must fit the check's bound, including from Gloas. -/
theorem isValidIndexedAttestation_constructAggregateOfSingleAttestations {config : Config}
    {state : BeaconState preset fork} (electra : .pectra ≤ fork) {data : AttestationData}
    {committeeIndex : CommitteeIndex} {signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {singles : List SingleAttestation}
    {aggregate : Attestation preset fork}
    (honest : List.Forall₂ (fun index single =>
      constructSingleAttestation config state data committeeIndex index (key index) = .ok single)
        signers (singles.filter fun single =>
          single.data = data ∧ single.committeeIndex = committeeIndex))
    (distinct : signers.Nodup)
    (registered : ∀ index ∈ signers, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : ((signers.map key).map (·.val)).sum ≠ 0)
    (bounded : .glamsterdam ≤ fork → signers.length ≤ maxAttesters preset fork)
    (built : constructAggregateOfSingleAttestations state data committeeIndex singles =
      .ok aggregate) :
    ∃ indexed, getIndexedAttestation state aggregate = .ok indexed ∧
      isValidIndexedAttestation config .bls state indexed = .ok true := by
  obtain ⟨_, _, _, _, _, sameData, _, aggregateSignature⟩ :=
    constructAggregateOfSingleAttestations_spec built
  obtain ⟨indices, computed, members⟩ :=
    mem_getAttestingIndices_constructAggregateOfSingleAttestations electra built
  have indexMembers : ∀ index, index ∈ indices ↔ index ∈ signers := by
    intro index
    rw [members]
    constructor
    · rintro ⟨single, member, sameData, sameCommittee, attester⟩
      obtain ⟨signer, signerMember, made⟩ := exists_related_of_mem honest.flip
        (List.mem_filter.mpr ⟨member, by simp [sameData, sameCommittee]⟩)
      have same : index = signer := attester.symm.trans (single_attestation_spec made).1
      exact same.symm ▸ signerMember
    · intro member
      obtain ⟨single, singleMember, made⟩ := exists_related_of_mem honest member
      obtain ⟨sameIndex, sameData, sameCommittee, _⟩ := single_attestation_spec made
      exact ⟨single, (List.mem_filter.mp singleMember).1, sameData, sameCommittee, sameIndex⟩
  have permuted : indices.Perm signers :=
    (List.perm_ext_iff_of_nodup (getAttestingIndices_sorted computed).nodup distinct).mpr
      indexMembers
  have nonempty : signers ≠ [] := by
    intro empty
    simp [empty] at sum
  obtain ⟨signer, signerMember⟩ := List.exists_mem_of_ne_nil signers nonempty
  obtain ⟨single, _, made⟩ := exists_related_of_mem honest signerMember
  obtain ⟨_, _, _, signedOne⟩ := single_attestation_spec made
  obtain ⟨domain, root, domained, rooted⟩ := attestation_signing_root signedOne
  have signed : List.Forall₂ (fun secret signature =>
      Signatures.sign secret (Base.packBytes root) = .ok signature)
      (signers.map key) ((singles.filter fun single =>
        single.data = data ∧ single.committeeIndex = committeeIndex).map (·.signature)) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact honest.imp fun _ _ made =>
      attestation_sign_eq domained rooted (single_attestation_spec made).2.2.2
  apply indexed_attestation_of_aggregate computed sameData permuted nonempty bounded registered
    domained rooted signed sum
  simpa only [List.map_map, Function.comp_def, Signatures.sigBytes, Base.packBytes]
    using aggregateSignature

/-- Before Electra, the topic's committee check accepts exactly when its other checks pass.

The aggregate signature check needs no additional hypothesis. -/
theorem validateAggregateInCommittee_constructAggregate_eq_accept {config : Config}
    {state : BeaconState preset fork} {before : fork < .pectra} {data : AttestationData}
    {signers : List ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {attestations : List (Attestation preset fork)}
    {seen : Seen} {store : Store preset fork} {statuses : PayloadStatuses}
    {signed : SignedAggregateAndProof preset fork} {index : CommitteeIndex}
    {currentTimeMs : UInt64} {root : Root} {committee : Array ValidatorIndex}
    {participants : List ValidatorIndex} {aggregator : Validator} {selected byAggregator : Bool}
    {time ancestry : ValidationResult}
    (honest : List.Forall₂ (fun validatorIndex attestation =>
      constructAttestation config state before data validatorIndex (key validatorIndex) =
        .ok attestation) signers (attestations.filter (·.data = data)))
    (distinct : signers.Nodup)
    (registered : ∀ validatorIndex ∈ signers, ∃ validator,
      getValidator state validatorIndex = .ok validator ∧
        validator.pubkey = Signatures.skToPk (key validatorIndex))
    (sum : ((signers.map key).map (·.val)).sum ≠ 0)
    (built : constructAggregate state before data attestations = .ok signed.message.aggregate)
    (rootOf : SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (head : store.headState config = .ok state)
    (clock : voteTimeOutcome config store signed.message.aggregate.data.slot currentTimeMs
      "aggregate slot is from a future slot"
      "aggregate epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state signed.message.aggregate.data.slot index =
      .ok committee)
    (participantsOf : getAttestingIndices state signed.message.aggregate = .ok participants)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (selectedOf : isValidSignatureAtEpoch config .bls state DOMAIN_SELECTION_PROOF
      signed.message.aggregate.data.target.epoch signed.message.aggregate.data.slot
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (signedOf : isValidSignatureAtEpoch config .bls state DOMAIN_AGGREGATE_AND_PROOF
      signed.message.aggregate.data.target.epoch signed.message aggregator.pubkey
      signed.signature = .ok byAggregator)
    (ancestryOf : voteOutcome store statuses signed.message.aggregate.data = .ok ancestry) :
    validateAggregateInCommittee config .bls seen store statuses signed index currentTimeMs =
        .ok accept ↔
      isNonStrictSuperset (seen.aggregateBitsFor (aggregateKey fork root index))
          signed.message.aggregate.aggregationBits.bits.toList = false ∧
        (signed.message.aggregate.data.target.epoch, signed.message.aggregatorIndex) ∉
          seen.aggregatorEpochs ∧
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blocks ∧
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blockStates ∧
        index < getCommitteeCountPerSlot state signed.message.aggregate.data.target.epoch ∧
        time = accept ∧
        signed.message.aggregate.data.target.epoch =
          computeEpochAtSlot preset signed.message.aggregate.data.slot ∧
        signed.message.aggregate.aggregationBits.bits.size = committee.size ∧
        participants ≠ [] ∧ isAggregator committee.size signed.message.selectionProof = true ∧
        signed.message.aggregatorIndex ∈ committee ∧ selected = true ∧ byAggregator = true ∧
        ancestry = accept := by
  obtain ⟨indexed, indexedOf, signature⟩ :=
    isValidIndexedAttestation_constructAggregate honest distinct registered sum built
  simpa using validateAggregateInCommittee_eq_accept rootOf head clock committeeOf
    participantsOf found selectedOf signedOf indexedOf signature ancestryOf

/-- From Electra, the topic's committee check accepts exactly when its other checks pass.

The aggregate signature check needs no additional hypothesis. -/
theorem validateAggregateInCommittee_constructAggregateOfSingleAttestations_eq_accept
    {config : Config} {state : BeaconState preset fork} (electra : .pectra ≤ fork)
    {data : AttestationData} {committeeIndex : CommitteeIndex} {signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {singles : List SingleAttestation}
    {seen : Seen} {store : Store preset fork} {statuses : PayloadStatuses}
    {signed : SignedAggregateAndProof preset fork} {index : CommitteeIndex}
    {currentTimeMs : UInt64} {root : Root} {committee : Array ValidatorIndex}
    {participants : List ValidatorIndex} {aggregator : Validator} {selected byAggregator : Bool}
    {time ancestry : ValidationResult}
    (honest : List.Forall₂ (fun validatorIndex single =>
      constructSingleAttestation config state data committeeIndex validatorIndex
        (key validatorIndex) = .ok single) signers (singles.filter fun single =>
          single.data = data ∧ single.committeeIndex = committeeIndex))
    (distinct : signers.Nodup)
    (registered : ∀ validatorIndex ∈ signers, ∃ validator,
      getValidator state validatorIndex = .ok validator ∧
        validator.pubkey = Signatures.skToPk (key validatorIndex))
    (sum : ((signers.map key).map (·.val)).sum ≠ 0)
    (bounded : .glamsterdam ≤ fork → signers.length ≤ maxAttesters preset fork)
    (built : constructAggregateOfSingleAttestations state data committeeIndex singles =
      .ok signed.message.aggregate)
    (rootOf : SszType.hashTreeRoot signed.message.aggregate.data = .ok root)
    (head : store.headState config = .ok state)
    (clock : voteTimeOutcome config store signed.message.aggregate.data.slot currentTimeMs
      "aggregate slot is from a future slot"
      "aggregate epoch is not current or previous epoch" = .ok time)
    (committeeOf : getBeaconCommittee state signed.message.aggregate.data.slot index =
      .ok committee)
    (participantsOf : getAttestingIndices state signed.message.aggregate = .ok participants)
    (found : state.validators.data[signed.message.aggregatorIndex.toNat]? = some aggregator)
    (selectedOf : isValidSignatureAtEpoch config .bls state DOMAIN_SELECTION_PROOF
      signed.message.aggregate.data.target.epoch signed.message.aggregate.data.slot
      aggregator.pubkey signed.message.selectionProof = .ok selected)
    (signedOf : isValidSignatureAtEpoch config .bls state DOMAIN_AGGREGATE_AND_PROOF
      signed.message.aggregate.data.target.epoch signed.message aggregator.pubkey
      signed.signature = .ok byAggregator)
    (ancestryOf : voteOutcome store statuses signed.message.aggregate.data = .ok ancestry) :
    validateAggregateInCommittee config .bls seen store statuses signed index currentTimeMs =
        .ok accept ↔
      isNonStrictSuperset (seen.aggregateBitsFor (aggregateKey fork root index))
          signed.message.aggregate.aggregationBits.bits.toList = false ∧
        (signed.message.aggregate.data.target.epoch, signed.message.aggregatorIndex) ∉
          seen.aggregatorEpochs ∧
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blocks ∧
        signed.message.aggregate.data.beaconBlockRoot ∈ store.blockStates ∧
        index < getCommitteeCountPerSlot state signed.message.aggregate.data.target.epoch ∧
        time = accept ∧
        signed.message.aggregate.data.target.epoch =
          computeEpochAtSlot preset signed.message.aggregate.data.slot ∧
        signed.message.aggregate.aggregationBits.bits.size = committee.size ∧
        participants ≠ [] ∧ isAggregator committee.size signed.message.selectionProof = true ∧
        signed.message.aggregatorIndex ∈ committee ∧ selected = true ∧ byAggregator = true ∧
        ancestry = accept := by
  obtain ⟨indexed, indexedOf, signature⟩ :=
    isValidIndexedAttestation_constructAggregateOfSingleAttestations electra honest distinct
      registered sum bounded built
  simpa using validateAggregateInCommittee_eq_accept rootOf head clock committeeOf
    participantsOf found selectedOf signedOf indexedOf signature ancestryOf

end EthLib.Consensus
