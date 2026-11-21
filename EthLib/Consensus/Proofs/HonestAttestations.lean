module

public import EthLib.Consensus.Proofs.HonestAggregateSignatures
public import EthLib.Consensus.Proofs.Transition.AttestationAccepted
import EthLib.Base.Proofs.Forall2
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Signing
import EthLib.Consensus.Proofs.Containers.Misc
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Cryptography.Proofs.Bls.Signatures
import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: the honest attestation of a committee is accepted, and flags its honest members

An honest validator of a committee signs the attestation data of its slot with its own key.

An aggregator joins those signatures into one attestation, with a bit for each signer.

Before Electra each validator sends an attestation with one bit, and the aggregate joins them.

From Electra each sends a single attestation that names its committee.

The aggregate then marks that one committee in its committee bits, as [EIP-7549] specifies.

Such an aggregate is built when the committee has an honest member.

From Altair until Gloas, the attestation step of a block in the inclusion window accepts it.

Each honest member of the committee then holds the timely target flag.

That needs the state to hold the target root for the first slot of the target epoch.

The signature check is that of BLS, so the secret keys of the signers must not sum to zero.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {state : BeaconState preset fork}

/-- The members of a committee that are in an honest set, each named once. -/
def honestSigners (honest : Finset ValidatorIndex) (committee : Array ValidatorIndex) :
    List ValidatorIndex :=
  (committee.toList.filter (· ∈ honest)).dedup

/-- The honest attestation of one committee on some data.

Each honest member of the committee signs the data with its key.

Before Electra the committee is that of the index of the data, and the given index is not read.

Each member sends an attestation with its one bit, and the aggregate joins them.

From Electra the committee is the given one, and each member sends a single attestation.

The aggregate joins those, and marks the committee in its committee bits.

It is the aggregate that an honest aggregator builds once it holds the vote of each honest member.

So it assumes that those votes reach the aggregator in time. -/
def honestAttestation (config : Config) (state : BeaconState preset fork)
    (honest : Finset ValidatorIndex) (key : ValidatorIndex → Signatures.SecretKey)
    (data : AttestationData) (committeeIndex : CommitteeIndex) :
    Except ValidatorDutyError (Attestation preset fork) :=
  if electra : .pectra ≤ fork then do
    let committee ← (getBeaconCommittee state data.slot committeeIndex).mapError .accessor
    let singles ← (honestSigners honest committee).mapM fun index =>
      constructSingleAttestation config state data committeeIndex index (key index)
    constructAggregateOfSingleAttestations state data committeeIndex singles
  else do
    have before : fork < .pectra := Nat.lt_of_not_le electra
    let committee ← (getBeaconCommittee state data.slot data.index).mapError .accessor
    let singles ← (honestSigners honest committee).mapM fun index =>
      constructAttestation config state before data index (key index)
    constructAggregate state before data singles

/-- A computation that does not fail has a value. -/
private theorem exists_ok_of_not_error {ε α : Type} {result : Except ε α}
    (never : ¬∃ error, result = .error error) : ∃ value, result = .ok value := by
  cases result with
  | error error => exact absurd ⟨error, rfl⟩ never
  | ok value => exact ⟨value, rfl⟩

/-- The signature of attestation data by any key signs one message, fixed by the data. -/
private theorem getAttestationSignature_eq (config : Config) (state : BeaconState preset fork)
    (data : AttestationData) : ∃ message, ∀ key, getAttestationSignature config state data key =
      (Signatures.sign key message).mapError .bls := by
  obtain ⟨domain, domained⟩ :=
    getDomain_total config state DOMAIN_BEACON_ATTESTER (some data.target.epoch)
  obtain ⟨root, rooted⟩ := computeSigningRoot_total data domain
  refine ⟨packBytes root, fun key => ?_⟩
  -- The domain and the root have values, so the signature is that of their message.
  --
  -- Each costly step is replaced by its value before any step is unfolded.
  rw [getAttestationSignature, signAtEpoch, domained, mapError_ok_bind, rooted, mapError_ok_bind]

/-- The honest signers of a committee are its members in the honest set. -/
theorem mem_honestSigners {honest : Finset ValidatorIndex}
    {committee : Array ValidatorIndex} {index : ValidatorIndex} :
    index ∈ honestSigners honest committee ↔ index ∈ committee ∧ index ∈ honest := by
  simp [honestSigners, List.mem_dedup, List.mem_filter]

/-- Signers whose secret keys do not sum to zero are not none. -/
private theorem honestSigners_ne_nil {honest : Finset ValidatorIndex}
    {committee : Array ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    (sum : (((honestSigners honest committee).map key).map (·.val)).sum ≠ 0) :
    honestSigners honest committee ≠ [] := fun empty => sum (by simp [empty])

/-- A single attestation is built whenever the signature of the data is. -/
private theorem constructSingleAttestation_exists_ok {config : Config} {data : AttestationData}
    {committeeIndex : CommitteeIndex} {index : ValidatorIndex} {key : Signatures.SecretKey}
    {signature : BLSSignature}
    (signed : getAttestationSignature config state data key = .ok signature) :
    ∃ single, constructSingleAttestation config state data committeeIndex index key = .ok single :=
  ⟨{ committeeIndex, attesterIndex := index, data, signature },
    by rw [constructSingleAttestation, signed, ok_bind]; rfl⟩

/-- Before Electra, the attestation of a member of the committee of the data is built.

The committee must fit the bits of an attestation. -/
private theorem constructAttestation_exists_ok {config : Config} {before : fork < .pectra}
    {data : AttestationData} {index : ValidatorIndex} {key : Signatures.SecretKey}
    {committee : Array ValidatorIndex} {signature : BLSSignature}
    (committeeOk : getBeaconCommittee state data.slot data.index = .ok committee)
    (member : index ∈ committee) (fits : committee.size ≤ maxAttesters preset fork)
    (signed : getAttestationSignature config state data key = .ok signature) :
    ∃ attestation, constructAttestation config state before data index key = .ok attestation := by
  have inside : committee.idxOf index < committee.size := Array.idxOf_lt_length_of_mem member
  -- The committee and the signature are replaced by their values before any step is unfolded.
  rw [constructAttestation, committeeOk, mapError_ok_bind, signed]
  simp [inside, fits, ok_bind, pure, Except.pure]

/-- Single attestations of signers on the data and the committee are all kept by their filter. -/
private theorem filter_singles_eq {config : Config} {data : AttestationData}
    {committeeIndex : CommitteeIndex} {signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {singles : List SingleAttestation}
    (made : List.Forall₂ (fun index single =>
      constructSingleAttestation config state data committeeIndex index (key index) = .ok single)
        signers singles) :
    singles.filter (fun single =>
      single.data = data ∧ single.committeeIndex = committeeIndex) = singles := by
  refine List.filter_eq_self.mpr fun single member => ?_
  obtain ⟨index, -, made⟩ := exists_mem_of_forall₂ made.flip member
  obtain ⟨-, sameData, sameIndex, -⟩ := constructSingleAttestation_spec made
  simp [sameData, sameIndex]

/-- Before Electra, attestations of signers on the data are all kept by their filter. -/
private theorem filter_attestations_eq {config : Config} {before : fork < .pectra}
    {data : AttestationData} {signers : List ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {attestations : List (Attestation preset fork)}
    (made : List.Forall₂ (fun index attestation =>
      constructAttestation config state before data index (key index) = .ok attestation)
        signers attestations) :
    attestations.filter (·.data = data) = attestations := by
  refine List.filter_eq_self.mpr fun attestation member => ?_
  obtain ⟨index, -, made⟩ := exists_mem_of_forall₂ made.flip member
  obtain ⟨-, -, -, -, sameData, -⟩ := constructAttestation_spec made
  simp [sameData]

/-- The honest attestation of a committee is built when the committee has an honest member.

Before Electra the data names the committee.

The committee has a value, and before Gloas it fits the bits of an attestation.

From Electra its index is below the largest number of committees of a slot. -/
theorem honestAttestation_exists_ok {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {data : AttestationData}
    {committeeIndex : CommitteeIndex} {committee : Array ValidatorIndex}
    (indexed : ¬.pectra ≤ fork → data.index = committeeIndex)
    (committeeOk : getBeaconCommittee state data.slot committeeIndex = .ok committee)
    (fits : fork < .glamsterdam → committee.size ≤ maxAttesters preset fork)
    (below : .pectra ≤ fork → committeeIndex < preset.MAX_COMMITTEES_PER_SLOT)
    (someSigner : honestSigners honest committee ≠ []) :
    ∃ attestation,
      honestAttestation config state honest key data committeeIndex = .ok attestation := by
  obtain ⟨message, signs⟩ := getAttestationSignature_eq config state data
  have nonempty : (honestSigners honest committee).map key ≠ [] := by
    simpa using someSigner
  -- Each key signs the data, since the message has a signature by any key.
  have signed : ∀ index, ∃ signature,
      getAttestationSignature config state data (key index) = .ok signature := fun index => by
    obtain ⟨signature, made⟩ := Signatures.sign_ok (key index) message
    exact ⟨signature, by rw [signs, made]; rfl⟩
  unfold honestAttestation
  by_cases electra : .pectra ≤ fork
  · rw [dite_eq_left electra]
    obtain ⟨singles, mapped⟩ := mapM_exists_ok (xs := honestSigners honest committee)
      (f := fun index =>
        constructSingleAttestation config state data committeeIndex index (key index))
      fun index _ => constructSingleAttestation_exists_ok (signed index).choose_spec
    have made := forall₂_of_mapM_ok mapped
    have kept := filter_singles_eq made
    have aggregated : ∃ aggregate : Attestation preset fork,
        constructAggregateOfSingleAttestations state data committeeIndex singles =
          .ok aggregate := by
      refine exists_ok_of_not_error fun failed => ?_
      rcases exists_constructAggregateOfSingleAttestations_eq_error_iff.mp failed with
        outside | ⟨error, failedCommittee⟩ | ⟨other, otherOk, fault⟩
      · exact absurd (below electra) (UInt64.not_lt.mpr outside)
      · rw [committeeOk] at failedCommittee
        cases failedCommittee
      rw [committeeOk, Except.ok.injEq] at otherOk
      subst otherOk
      rw [kept] at fault
      rcases fault with ⟨single, member, outside⟩ | ⟨earlier, above⟩ | ⟨error, failedAggregate⟩
      · -- The attester of a single attestation is an honest member of the committee.
        obtain ⟨index, signer, made⟩ := exists_mem_of_forall₂ made.flip member
        obtain ⟨attester, -⟩ := constructSingleAttestation_spec made
        exact outside (attester ▸ (mem_honestSigners.mp signer).1)
      · exact Nat.not_le_of_lt above (fits earlier)
      · -- The signatures are those of one message by the keys, so they aggregate.
        have keysSigned : List.Forall₂
            (fun secret signature => Signatures.sign secret message = .ok signature)
            ((honestSigners honest committee).map key) (singles.map (·.signature)) := by
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact made.imp fun index single made => mapError_ok_iff.mp
            ((signs _).symm.trans (constructSingleAttestation_spec made).2.2.2)
        obtain ⟨signature, aggregated⟩ := Signatures.aggregate_sign_exists_ok keysSigned nonempty
        rw [aggregated] at failedAggregate
        cases failedAggregate
    obtain ⟨aggregate, aggregated⟩ := aggregated
    exact ⟨aggregate, bind_ok_iff.mpr ⟨committee, mapError_ok_iff.mpr committeeOk,
      bind_ok_iff.mpr ⟨singles, mapM_ok_of_forall₂ made, aggregated⟩⟩⟩
  · rw [dite_eq_right electra]
    have before : fork < .pectra := Nat.lt_of_not_le electra
    -- Before Electra the data names the committee, and the committee fits the bits.
    have committeeOk' : getBeaconCommittee state data.slot data.index = .ok committee :=
      indexed electra ▸ committeeOk
    have fitted : committee.size ≤ maxAttesters preset fork :=
      fits (Nat.lt_trans before (by decide))
    obtain ⟨attestations, mapped⟩ := mapM_exists_ok (xs := honestSigners honest committee)
      (f := fun index => constructAttestation config state before data index (key index))
      fun index signer => constructAttestation_exists_ok committeeOk'
        (mem_honestSigners.mp signer).1 fitted (signed index).choose_spec
    have made := forall₂_of_mapM_ok mapped
    have kept := filter_attestations_eq made
    have aggregated : ∃ aggregate,
        constructAggregate state before data attestations = .ok aggregate := by
      refine exists_ok_of_not_error fun failed => ?_
      rcases exists_constructAggregate_eq_error_iff.mp failed with
        ⟨error, failedCommittee⟩ | ⟨other, otherOk, fault⟩
      · rw [committeeOk'] at failedCommittee
        cases failedCommittee
      rw [committeeOk', Except.ok.injEq] at otherOk
      subst otherOk
      rw [kept] at fault
      rcases fault with ⟨attestation, member, sized⟩ | ⟨error, failedAggregate⟩
      · -- Each attestation has one bit for each member of the committee.
        obtain ⟨index, -, made⟩ := exists_mem_of_forall₂ made.flip member
        obtain ⟨other, otherOk, -, bits, -⟩ := constructAttestation_spec made
        rw [committeeOk', Except.ok.injEq] at otherOk
        subst otherOk
        exact sized (by simp [bits])
      · -- The signatures are those of one message by the keys, so they aggregate.
        have keysSigned : List.Forall₂
            (fun secret signature => Signatures.sign secret message = .ok signature)
            ((honestSigners honest committee).map key) (attestations.map (·.signature)) := by
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact made.imp fun index attestation made => mapError_ok_iff.mp
            ((signs _).symm.trans (constructAttestation_spec made).choose_spec.2.2.2.2)
        obtain ⟨signature, aggregated⟩ := Signatures.aggregate_sign_exists_ok keysSigned nonempty
        rw [getAggregateSignature, aggregated] at failedAggregate
        cases failedAggregate
    obtain ⟨aggregate, aggregated⟩ := aggregated
    exact ⟨aggregate, bind_ok_iff.mpr ⟨committee, mapError_ok_iff.mpr committeeOk',
      bind_ok_iff.mpr ⟨attestations, mapM_ok_of_forall₂ made, aggregated⟩⟩⟩

/-- From Electra, the honest attestation of a committee, from what it is built of.

Its committee bits name the committee alone, and it holds the given data.

It has one bit for each member of the committee, set when that member is honest.

Its signature is the aggregate of the signatures of the honest signers on the data, in order. -/
theorem honestAttestation_spec (electra : .pectra ≤ fork) {honest : Finset ValidatorIndex}
    {key : ValidatorIndex → Signatures.SecretKey} {data : AttestationData}
    {committeeIndex : CommitteeIndex} {attestation : Attestation preset fork}
    (built : honestAttestation config state honest key data committeeIndex = .ok attestation) :
    ∃ committee, getBeaconCommittee state data.slot committeeIndex = .ok committee ∧
      getCommitteeIndices (attestation.committeeBits electra) = [committeeIndex] ∧
      attestation.data = data ∧
      attestation.aggregationBits.bits =
        Array.ofFn (fun seat : Fin committee.size => decide (committee[seat] ∈ honest)) ∧
      ∃ signatures, List.Forall₂ (fun index signature =>
          getAttestationSignature config state data (key index) = .ok signature)
        (honestSigners honest committee) signatures ∧
        Signatures.aggregate signatures.toArray = .ok attestation.signature := by
  unfold honestAttestation at built
  rw [dite_eq_left electra] at built
  obtain ⟨committee, committeeOk, built⟩ := bind_ok_iff.mp built
  rw [mapError_ok_iff] at committeeOk
  obtain ⟨singles, singlesOk, built⟩ := bind_ok_iff.mp built
  have made := forall₂_of_mapM_ok singlesOk
  have kept := filter_singles_eq made
  obtain ⟨-, other, otherOk, -, bits, sameData, -, aggregated⟩ :=
    constructAggregateOfSingleAttestations_spec built
  rw [committeeOk, Except.ok.injEq] at otherOk
  subst otherOk
  refine ⟨committee, committeeOk,
    getCommitteeIndices_constructAggregateOfSingleAttestations electra built, sameData, ?_,
    singles.map (·.signature), ?_, by rw [kept] at aggregated; exact aggregated⟩
  · -- The attesters of the single attestations are exactly the honest signers.
    rw [bits, kept]
    congr 1
    funext seat
    refine Bool.eq_iff_iff.mpr ?_
    rw [List.any_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨single, member, attester⟩
      obtain ⟨index, signer, singleMade⟩ := exists_mem_of_forall₂ made.flip member
      have same := (constructSingleAttestation_spec singleMade).1
      rw [decide_eq_true_iff, same] at attester
      exact attester ▸ (mem_honestSigners.mp signer).2
    · intro honestMember
      obtain ⟨single, member, singleMade⟩ := exists_mem_of_forall₂ made
        (mem_honestSigners.mpr ⟨Array.getElem_mem seat.isLt, honestMember⟩)
      exact ⟨single, member,
        decide_eq_true_iff.mpr (constructSingleAttestation_spec singleMade).1⟩
  · rw [List.forall₂_map_right_iff]
    exact made.imp fun _ _ singleMade => (constructSingleAttestation_spec singleMade).2.2.2

/-- From Altair to Fulu, the honest attestation of a committee is accepted.

Each honest member of the committee then holds the timely target flag.

That needs the state to hold the target root for the first slot of the target epoch.

The data and the state meet the checks of the attestation step, and the state is within a budget.

The committee index is below the count of committees of a slot in the target epoch.

The registry holds the key of each honest member, and their secret keys must not sum to zero.

The signature check is that of BLS. -/
theorem processAttestation_honestAttestation {budget scoreBound : Nat}
    (altair : .altair ≤ fork) (beforeGloas : fork < .glamsterdam)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {data : AttestationData} {committeeIndex : CommitteeIndex} {committee : Array ValidatorIndex}
    {attestation : Attestation preset fork} (parentSlot : Slot)
    (roots : preset.RootsReachPreviousEpoch)
    (slotRoom : state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat < 2 ^ 64)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT ≠ 0)
    (scaled : preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat < 2 ^ 64)
    (holds : WithinBudget budget scoreBound state)
    (participation : ParticipationMatches state)
    (room : budget + state.validators.data.size * (64 * preset.baseRewardCeiling) < 2 ^ 64)
    (recent : data.target.epoch = getPreviousEpoch state ∨
      data.target.epoch = getCurrentEpoch state)
    (slotEpoch : data.target.epoch = computeEpochAtSlot preset data.slot)
    (past : data.slot.toNat < state.slot.toNat)
    (early : data.slot.toNat + preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat ≤ state.slot.toNat)
    (deadline : fork < .dencun → state.slot.toNat ≤ data.slot.toNat + preset.SLOTS_PER_EPOCH.toNat)
    (indexed : data.index = if .pectra ≤ fork then 0 else committeeIndex)
    (below : committeeIndex < getCommitteeCountPerSlot state data.target.epoch)
    (committeeOk : getBeaconCommittee state data.slot committeeIndex = .ok committee)
    (source : data.source = if data.target.epoch = getCurrentEpoch state then
        state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint)
    (registered : ∀ index ∈ honestSigners honest committee, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : (((honestSigners honest committee).map key).map (·.val)).sum ≠ 0)
    (proposer : ∃ index, getBeaconProposerIndex state = .ok index ∧
      index.toNat < state.validators.data.size)
    (built : honestAttestation config state honest key data committeeIndex = .ok attestation) :
    ∃ after, processAttestation config .bls state parentSlot attestation = .ok after ∧
      (getBlockRoot state data.target.epoch = .ok data.target.root →
        ∀ index ∈ committee, index ∈ honest → TargetFlagAt (recentParticipation after altair
          (data.target.epoch == getCurrentEpoch state)) index.toNat) := by
  have signer := List.exists_mem_of_ne_nil _ (honestSigners_ne_nil sum)
  have described := fun electra => honestAttestation_spec (config := config) electra built
  unfold honestAttestation at built
  by_cases electra : .pectra ≤ fork
  · -- The bits of the committee are set exactly at its honest members.
    obtain ⟨other, otherOk, -, -, bits, -⟩ := described electra
    rw [committeeOk, Except.ok.injEq] at otherOk
    subst otherOk
    rw [dite_eq_left electra] at built
    obtain ⟨other, otherOk, built⟩ := bind_ok_iff.mp built
    rw [mapError_ok_iff, committeeOk, Except.ok.injEq] at otherOk
    subst otherOk
    obtain ⟨singles, singlesOk, built⟩ := bind_ok_iff.mp built
    have made := forall₂_of_mapM_ok singlesOk
    have kept := filter_singles_eq made
    obtain ⟨-, other, otherOk, -, -, sameData, -, -⟩ :=
      constructAggregateOfSingleAttestations_spec built
    rw [committeeOk, Except.ok.injEq] at otherOk
    subst otherOk
    obtain ⟨indices, computed, members⟩ :=
      mem_getAttestingIndices_constructAggregateOfSingleAttestations electra built
    -- The aggregate passes its signature check, since the filter keeps every single attestation.
    have valid := isValidIndexedAttestation_constructAggregateOfSingleAttestations electra
      (by rw [kept]; exact made) (List.nodup_dedup _) registered sum
      (fun gloas => absurd beforeGloas (Nat.not_lt_of_le gloas)) built
    -- The bits of the committee mark an honest signer, so the committee has an attester.
    obtain ⟨attesters, attestersOk⟩ := committeeAttesters_ok
      (bits := attestation.aggregationBits.bits) (committee := committee) (by simp [bits])
    have someAttester : attesters ≠ [] := by
      obtain ⟨index, member⟩ := signer
      obtain ⟨inCommittee, honestMember⟩ := mem_honestSigners.mp member
      obtain ⟨seat, inside, seated⟩ := Array.mem_iff_getElem.mp inCommittee
      refine List.ne_nil_of_mem
        ((mem_committeeAttesters_iff attestersOk).mpr ⟨seat, inside, seated, ?_⟩)
      simp [bits, inside, seated, honestMember]
    have committees : checkAttestationCommittees state attestation = .ok () := by
      unfold checkAttestationCommittees
      rw [dite_eq_left electra,
        getCommitteeIndices_constructAggregateOfSingleAttestations electra built,
        attestationCommitteesSize_cons, sameData]
      have indexZero : data.index = 0 := by simpa [electra] using indexed
      have notGloas : ¬.glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
      have sized : attestation.aggregationBits.bits.size = committee.size := by simp [bits]
      -- The count and the committee are replaced by their values before any step is unfolded.
      rw [getCommitteeCountPerSlotChecked_of_within holds.within, committeeOk]
      simp only [liftAccessor, mapError_ok_bind, ensure, below, indexZero, ↓reduceIte, ok_bind,
        attestersOk, attestationCommitteesSize_nil, sized, notGloas, ne_eq, someAttester,
        not_false_eq_true, Nat.zero_add]
    subst sameData
    obtain ⟨after, processed, flags⟩ := processAttestation_exists_ok altair beforeGloas parentSlot
      roots slotRoom increment scaled holds participation room recent slotEpoch past early deadline
      committees source valid proposer
    refine ⟨after, processed, fun rooted index member honestMember =>
      flags indices computed rooted index ?_⟩
    -- An honest member of the committee signs a single attestation, so it attests.
    obtain ⟨single, singleMember, singleMade⟩ :=
      exists_mem_of_forall₂ made (mem_honestSigners.mpr ⟨member, honestMember⟩)
    obtain ⟨attester, singleData, singleIndex, -⟩ := constructSingleAttestation_spec singleMade
    exact (members index).mpr ⟨single, singleMember, singleData, singleIndex, attester⟩
  · rw [dite_eq_right electra] at built
    have before : fork < .pectra := Nat.lt_of_not_le electra
    -- Before Electra the data names the committee.
    have indexEq : data.index = committeeIndex := by simpa [electra] using indexed
    obtain ⟨other, otherOk, built⟩ := bind_ok_iff.mp built
    rw [mapError_ok_iff, indexEq, committeeOk, Except.ok.injEq] at otherOk
    subst otherOk
    obtain ⟨attestations, attestationsOk, built⟩ := bind_ok_iff.mp built
    have made := forall₂_of_mapM_ok attestationsOk
    have kept := filter_attestations_eq made
    obtain ⟨other, otherOk, -, -, bits, sameData, -⟩ := constructAggregate_spec built
    rw [indexEq, committeeOk, Except.ok.injEq] at otherOk
    subst otherOk
    obtain ⟨indices, computed, members⟩ := mem_getAttestingIndices_constructAggregate built
    -- The aggregate passes its signature check, since the filter keeps every attestation.
    have valid := isValidIndexedAttestation_constructAggregate (by rw [kept]; exact made)
      (List.nodup_dedup _) registered sum built
    -- The count of committees has a value, the index is below it, and the bits fit.
    have committees : checkAttestationCommittees state attestation = .ok () := by
      unfold checkAttestationCommittees
      have sized : attestation.aggregationBits.bits.size = committee.size := by simp [bits]
      rw [dite_eq_right electra, sameData]
      -- The count and the committee are replaced by their values before any step is unfolded.
      rw [getCommitteeCountPerSlotChecked_of_within holds.within, indexEq, committeeOk]
      simp only [liftAccessor, mapError_ok_bind, ensure, below, ↓reduceIte, ok_bind, sized]
    subst sameData
    obtain ⟨after, processed, flags⟩ := processAttestation_exists_ok altair beforeGloas parentSlot
      roots slotRoom increment scaled holds participation room recent slotEpoch past early deadline
      committees source valid proposer
    refine ⟨after, processed, fun rooted index member honestMember =>
      flags indices computed rooted index ?_⟩
    -- An honest member of the committee signs an attestation, whose only attester it is.
    obtain ⟨single, singleMember, singleMade⟩ :=
      exists_mem_of_forall₂ made (mem_honestSigners.mpr ⟨member, honestMember⟩)
    exact (members index).mpr ⟨single, singleMember,
      (constructAttestation_spec singleMade).choose_spec.2.2.2.1, [index],
      getAttestingIndices_constructAttestation singleMade, List.mem_singleton_self _⟩

end EthLib.Consensus
