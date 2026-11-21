module

public import EthLib.Consensus.Proofs.HonestAttestations
public import EthLib.Consensus.Proofs.HonestProposer
import EthLib.Base.Proofs.Forall2
import EthLib.Consensus.Proofs.Accessors
import EthLib.Consensus.Proofs.Signing
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Cryptography.Proofs.Bls.SignaturesCorrect

/-!
# Proofs: from Electra, the honest aggregate of a slot is accepted, and flags its honest members

From Electra an attestation in a block may cover several committees of one slot, as [EIP-7549] says.

Its committee bits name the committees, and its bits run over each of them in turn.

The honest aggregate of a slot covers each committee of the slot that has an honest member.

It joins the honest attestation of each such committee, as an honest proposer joins aggregates.

From Electra until Gloas, the attestation step of a block in the inclusion window accepts it.

Its signature check needs the secret keys of all honest members of the slot not to sum to zero.

Each honest member of each committee of the slot then holds the timely target flag.

[EIP-7549]: https://eips.ethereum.org/EIPS/eip-7549#consensus-layer
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {state : BeaconState preset fork}

/-- The committees of a slot that have an honest member, by their index, in increasing order. -/
def honestCommittees (state : BeaconState preset fork) (honest : Finset ValidatorIndex)
    (slot : Slot) : Except AccessorError (List CommitteeIndex) := do
  let count := (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat
  let committees ← (List.range count).mapM fun position =>
    getBeaconCommittee state slot position.toUInt64
  return (((List.range count).zip committees).filter fun pair =>
    !(honestSigners honest pair.2).isEmpty).map (·.1.toUInt64)

/-- From Electra: the honest aggregate of a slot, one attestation over its committees.

It covers each committee of the slot of the data that has an honest member.

It is built from the honest attestation of each of them, joined as an honest proposer joins them.

It assumes that every honest member of the slot votes for the same data.

It also assumes that the aggregate of each committee reaches the proposer in time. -/
def honestSlotAggregate (electra : .pectra ≤ fork) (config : Config)
    (state : BeaconState preset fork) (honest : Finset ValidatorIndex)
    (key : ValidatorIndex → Signatures.SecretKey) (data : AttestationData) :
    Except ProposerError (Attestation preset fork) := do
  let committees ← (honestCommittees state honest data.slot).mapError .accessor
  let aggregates ← (committees.mapM (honestAttestation config state honest key data)).mapError .duty
  computeOnChainAggregate electra aggregates

/-! ## Bits that follow the honest members of committees -/

/-- Bits that hold one bit per member of a committee, set when it is honest, give its attesters.

The attesters are then the honest signers of the committee. -/
private theorem committeeAttesters_honest {honest : Finset ValidatorIndex}
    {committee : Array ValidatorIndex} {bits : Array Bool} {before after : List Bool}
    (split : bits.toList = before ++ ((List.ofFn fun seat : Fin committee.size =>
      decide (committee[seat] ∈ honest)) ++ after)) :
    ∃ attesters, committeeAttesters bits before.length committee = .ok attesters ∧
      ∀ index, index ∈ attesters ↔ index ∈ honestSigners honest committee := by
  have sized : before.length + committee.size ≤ bits.size := by
    have lengths := congrArg List.length split
    simp only [Array.length_toList, List.length_append, List.length_ofFn] at lengths
    omega
  have read : ∀ seat (inside : seat < committee.size),
      bits.getD (before.length + seat) false = decide (committee[seat] ∈ honest) := by
    intro seat inside
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, split,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using inside)]
    simp [inside]
  obtain ⟨attesters, computed⟩ :
      ∃ attesters, committeeAttesters bits before.length committee = .ok attesters := by
    unfold committeeAttesters
    rw [ite_eq_right (by omega)]
    exact ⟨_, rfl⟩
  refine ⟨attesters, computed, fun index => ?_⟩
  rw [mem_committeeAttesters_iff computed, mem_honestSigners]
  constructor
  · rintro ⟨seat, inside, rfl, set⟩
    rw [read seat inside, decide_eq_true_iff] at set
    exact ⟨Array.getElem_mem inside, set⟩
  · rintro ⟨member, honestMember⟩
    obtain ⟨seat, inside, rfl⟩ := Array.mem_iff_getElem.mp member
    exact ⟨seat, inside, rfl, by rw [read seat inside, decide_eq_true_iff]; exact honestMember⟩

/-- A position below a count of committees is the same index as a 64-bit number. -/
private theorem toUInt64_lt_of_lt {position : Nat} {count : UInt64}
    (below : position < count.toNat) :
    position.toUInt64 < count := by
  rw [UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq,
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans below (UInt64.toNat_lt _))]
  exact below

/-- From Electra, committees of a slot with honest members, and bits for those members, pass.

Each committee is read at its position, below the count of the slot, and has an honest member.

The bits from the offset are those of the committees in turn, one per member, set when honest.

The total size is then the size of the bits. -/
private theorem attestationCommitteesSize_honest (within : state.RegistryWithinLimit)
    {honest : Finset ValidatorIndex} {data : AttestationData}
    (slotEpoch : data.target.epoch = computeEpochAtSlot preset data.slot) {bits : Array Bool}
    (selected : List (Nat × Array ValidatorIndex))
    (good : ∀ pair ∈ selected,
      pair.1 < (getCommitteeCountPerSlot state (computeEpochAtSlot preset data.slot)).toNat ∧
        getBeaconCommittee state data.slot pair.1.toUInt64 = .ok pair.2 ∧
        honestSigners honest pair.2 ≠ [])
    {before : List Bool}
    (split : bits.toList = before ++ selected.flatMap fun pair =>
      List.ofFn fun seat : Fin pair.2.size => decide (pair.2[seat] ∈ honest)) :
    attestationCommitteesSize state data bits (selected.map (·.1.toUInt64)) before.length =
      .ok bits.size := by
  induction selected generalizing before with
  | nil =>
    have lengths := congrArg List.length split
    simp only [Array.length_toList, List.flatMap_nil, List.append_nil] at lengths
    rw [List.map_nil, attestationCommitteesSize_nil, lengths]
  | cons pair rest ih =>
    obtain ⟨below, committeeOk, someHonest⟩ := good pair List.mem_cons_self
    rw [List.flatMap_cons, ← List.append_assoc] at split
    obtain ⟨attesters, attestersOk, members⟩ :=
      committeeAttesters_honest (List.append_assoc _ _ _ ▸ split)
    have someAttester : attesters ≠ [] := by
      obtain ⟨index, member⟩ := List.exists_mem_of_ne_nil _ someHonest
      exact List.ne_nil_of_mem ((members index).mpr member)
    have rest' := ih (fun other member => good other (List.mem_cons_of_mem _ member)) split
    rw [List.length_append, List.length_ofFn] at rest'
    rw [List.map_cons, attestationCommitteesSize_cons,
      getCommitteeCountPerSlotChecked_of_within within, slotEpoch, committeeOk]
    simp only [liftAccessor, mapError_ok_bind, ensure, toUInt64_lt_of_lt below, ↓reduceIte,
      ok_bind, attestersOk, ne_eq, someAttester, not_false_eq_true, rest']

/-- From Electra, bits for the honest members of committees of a slot show those members.

Each committee is read at its position, and the shuffle of the epoch of the slot has a value.

The bits from the offset are those of the committees in turn, one per member, set when honest. -/
private theorem committeesAttestersOf_honest {honest : Finset ValidatorIndex} {slot : Slot}
    {active : Array ValidatorIndex} {shuffled : Array UInt64}
    (shuffleOk : attesterShuffle state (computeEpochAtSlot preset slot) = .ok (active, shuffled))
    {bits : Array Bool} (selected : List (Nat × Array ValidatorIndex))
    (good : ∀ pair ∈ selected, getBeaconCommittee state slot pair.1.toUInt64 = .ok pair.2)
    {before : List Bool}
    (split : bits.toList = before ++ selected.flatMap fun pair =>
      List.ofFn fun seat : Fin pair.2.size => decide (pair.2[seat] ∈ honest)) :
    ∃ attesters, committeesAttestersOf preset slot bits
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)) active shuffled
        (selected.map (·.1.toUInt64)) before.length = .ok attesters ∧
      ∀ index, index ∈ attesters ↔ ∃ pair ∈ selected, index ∈ honestSigners honest pair.2 := by
  induction selected generalizing before with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons pair rest ih =>
    rw [List.flatMap_cons, ← List.append_assoc] at split
    obtain ⟨here, hereOk, members⟩ :=
      committeeAttesters_honest (List.append_assoc _ _ _ ▸ split)
    obtain ⟨there, thereOk, others⟩ :=
      ih (fun other member => good other (List.mem_cons_of_mem _ member)) split
    rw [List.length_append, List.length_ofFn] at thereOk
    refine ⟨here ++ there, ?_, fun index => ?_⟩
    · rw [List.map_cons, committeesAttestersOf_cons_of_attesterShuffle shuffleOk,
        good pair List.mem_cons_self]
      simp only [bind, Except.bind, hereOk, thereOk, pure, Except.pure]
    · rw [List.mem_append, members, others]
      simp only [List.mem_cons, exists_eq_or_imp]

/-! ## The committee bits of the aggregate -/

/-- Positions below `2^64` keep their order as 64-bit numbers. -/
private theorem toUInt64_lt_toUInt64 {a b : Nat} (lt : a < b) (small : b < 2 ^ 64) :
    a.toUInt64 < b.toUInt64 := by
  rw [UInt64.lt_iff_toNat_lt, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small,
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans lt small)]
  exact lt

/-- The indices of the set bits from a start increase strictly, and are at least the start. -/
private theorem filterMap_zipIdx_increasing (bits : List Bool) (start : Nat)
    (small : start + bits.length ≤ 2 ^ 64) :
    ((bits.zipIdx start).filterMap fun (bit, index) =>
        if bit then some index.toUInt64 else none).Pairwise (· < ·) ∧
      ∀ index ∈ (bits.zipIdx start).filterMap (fun (bit, index) =>
        if bit then some index.toUInt64 else none), start ≤ index.toNat := by
  induction bits generalizing start with
  | nil => simp
  | cons bit rest ih =>
    obtain ⟨increasing, above⟩ := ih (start + 1) (by simp at small; omega)
    have startNat : start.toUInt64.toNat = start := by
      have lt : start < 2 ^ 64 := by simp at small; omega
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' lt]
    rw [List.zipIdx_cons, List.filterMap_cons]
    cases bit with
    | false =>
      refine ⟨increasing, fun index member => ?_⟩
      have := above index member
      omega
    | true =>
      refine ⟨List.pairwise_cons.mpr ⟨fun index member => ?_, increasing⟩, fun index member => ?_⟩
      · rw [UInt64.lt_iff_toNat_lt, startNat]
        have := above index member
        omega
      · rcases List.mem_cons.mp member with rfl | member
        · rw [startNat]
        · have := above index member
          omega

/-- From Electra, committee bits that mark strictly increasing positions name those positions. -/
private theorem getCommitteeIndices_ofFn_contains {count : UInt64} {positions : List Nat}
    (increasing : positions.Pairwise (· < ·))
    (inside : ∀ position ∈ positions, position < count.toNat) :
    getCommitteeIndices (⟨Vector.ofFn fun index : Fin count.toNat =>
      (positions.map Nat.toUInt64).contains index.val.toUInt64⟩ :
        Serialization.Ssz.Bitvector count.toNat) =
        positions.map Nat.toUInt64 := by
  have small := count.toNat_lt
  unfold getCommitteeIndices
  refine List.Pairwise.eq_of_mem_iff
    (filterMap_zipIdx_increasing _ 0 (by simpa using small.le)).1 ?_ fun index => ?_
  · refine List.pairwise_map.mpr (increasing.imp_of_mem fun first second lt => ?_)
    exact toUInt64_lt_toUInt64 lt (Nat.lt_trans (inside _ second) small)
  · simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
      List.mem_zipIdx_iff_getElem?, Prod.exists, Vector.toList_ofFn, List.getElem?_ofFn,
      List.mem_map]
    constructor
    · rintro ⟨bit, position, found, set, rfl⟩
      subst set
      split at found
      · simpa [List.contains_iff_mem] using found.symm
      · cases found
    · rintro ⟨position, member, rfl⟩
      exact ⟨true, position, by simp [inside position member]; exact ⟨position, member, rfl⟩,
        rfl, rfl⟩

/-! ## The on-chain aggregate of aggregates sorted by committee -/

/-- From Electra, aggregates that each name one committee are keyed by that committee. -/
private theorem mapM_committeeOfAggregate {electra : .pectra ≤ fork} {keys : List CommitteeIndex}
    {aggregates : List (Attestation preset fork)}
    (named : List.Forall₂ (fun key aggregate =>
      getCommitteeIndices (aggregate.committeeBits electra) = [key]) keys aggregates) :
    aggregates.mapM (committeeOfAggregate electra) = .ok (keys.zip aggregates) := by
  induction named with
  | nil => rfl
  | cons head _ ih =>
    rw [List.mapM_cons, committeeOfAggregate, head, List.head?_cons]
    simp only [ih, List.zip_cons_cons]
    rfl

/-- Keys in order give pairs in the order of their keys. -/
private theorem pairwise_zip_keys {keys : List CommitteeIndex}
    {aggregates : List (Attestation preset fork)} (ordered : keys.Pairwise (· ≤ ·)) :
    (keys.zip aggregates).Pairwise fun a b => decide (a.1 ≤ b.1) = true := by
  induction keys generalizing aggregates with
  | nil => simp
  | cons key rest ih =>
    cases aggregates with
    | nil => simp
    | cons aggregate others =>
      rw [List.zip_cons_cons, List.pairwise_cons]
      refine ⟨fun pair member => ?_, ih (List.pairwise_cons.mp ordered).2⟩
      exact decide_eq_true ((List.pairwise_cons.mp ordered).1 _ (List.of_mem_zip member).1)

/-- Keys zipped with as many aggregates, then mapped on the aggregates, map the aggregates. -/
private theorem map_zip_snd {β : Type} {keys : List CommitteeIndex}
    {aggregates : List (Attestation preset fork)} (lengths : keys.length = aggregates.length)
    (f : Attestation preset fork → β) :
    (keys.zip aggregates).map (fun pair => f pair.2) = aggregates.map f := by
  simpa [List.map_map, Function.comp_def] using
    congrArg (List.map f) (List.map_snd_zip (l₁ := keys) (l₂ := aggregates) lengths.ge)

/-- From Electra, the on-chain aggregate of aggregates whose committees are in order.

Each aggregate names one committee, and the committees are in order.

The bits are those of the aggregates in turn, and the signature is the aggregate of theirs.

The data is that of one of them, and the committee bits mark their committees. -/
private theorem computeOnChainAggregate_of_ordered {electra : .pectra ≤ fork}
    {keys : List CommitteeIndex} {aggregates : List (Attestation preset fork)}
    {attestation : Attestation preset fork}
    (named : List.Forall₂ (fun key aggregate =>
      getCommitteeIndices (aggregate.committeeBits electra) = [key]) keys aggregates)
    (ordered : keys.Pairwise (· ≤ ·))
    (joined : computeOnChainAggregate electra aggregates = .ok attestation) :
    attestation.aggregationBits.bits =
        (aggregates.map (·.aggregationBits.bits)).foldl (· ++ ·) #[] ∧
      Signatures.aggregate (aggregates.map (·.signature)).toArray = .ok attestation.signature ∧
      (∃ first ∈ aggregates, attestation.data = first.data) ∧
      attestation.committeeBits electra =
        ⟨Vector.ofFn fun index : Fin preset.MAX_COMMITTEES_PER_SLOT.toNat =>
          keys.contains index.val.toUInt64⟩ := by
  have lengths := named.length_eq
  unfold computeOnChainAggregate at joined
  rw [mapM_committeeOfAggregate named, ok_bind,
    List.mergeSort_of_pairwise (pairwise_zip_keys ordered)] at joined
  simp only [List.map_fst_zip lengths.le] at joined
  rw [map_zip_snd lengths (·.aggregationBits.bits), map_zip_snd lengths (·.signature)] at joined
  split at joined
  · rename_i first headed
    split at joined
    · obtain ⟨signature, signed, joined⟩ := bind_ok_iff.mp joined
      simp only [pure, Except.pure, Except.ok.injEq] at joined
      subst joined
      exact ⟨rfl, mapError_ok_iff.mp signed,
        ⟨first.2, (List.of_mem_zip (List.mem_of_head? headed)).2, rfl⟩, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at joined
  · simp [throw, throwThe, MonadExceptOf.throw] at joined

/-- From Electra, aggregates whose committees are in order join on chain.

There is at least one, and before Gloas their bits together fit those of an attestation.

Their signatures must aggregate. -/
private theorem computeOnChainAggregate_exists_ok {electra : .pectra ≤ fork}
    {keys : List CommitteeIndex} {aggregates : List (Attestation preset fork)}
    (named : List.Forall₂ (fun key aggregate =>
      getCommitteeIndices (aggregate.committeeBits electra) = [key]) keys aggregates)
    (ordered : keys.Pairwise (· ≤ ·)) (nonempty : aggregates ≠ [])
    (fits : fork < .glamsterdam →
      ((aggregates.map (·.aggregationBits.bits)).foldl (· ++ ·) #[]).size ≤
        maxAttesters preset fork)
    (signed : ∃ signature,
      Signatures.aggregate (aggregates.map (·.signature)).toArray = .ok signature) :
    ∃ attestation, computeOnChainAggregate electra aggregates = .ok attestation := by
  have lengths := named.length_eq
  obtain ⟨signature, signedOk⟩ := signed
  obtain ⟨first, headed⟩ : ∃ first, (keys.zip aggregates).head? = some first := by
    cases keys with
    | nil => exact absurd (List.length_eq_zero_iff.mp lengths.symm) nonempty
    | cons key rest =>
      cases aggregates with
      | nil => exact absurd rfl nonempty
      | cons aggregate others => exact ⟨_, rfl⟩
  unfold computeOnChainAggregate
  rw [mapM_committeeOfAggregate named, ok_bind,
    List.mergeSort_of_pairwise (pairwise_zip_keys ordered)]
  simp only [List.map_fst_zip lengths.le]
  rw [map_zip_snd lengths (·.aggregationBits.bits), map_zip_snd lengths (·.signature), headed]
  dsimp only
  rw [dite_eq_left fits, signedOk]
  exact ⟨_, rfl⟩

/-! ## The committees of a slot with an honest member -/

/-- Dropping the entries that give no element does not change a flat map. -/
private theorem flatMap_filter_nonempty {α β : Type} (f : α → List β) (l : List α) :
    (l.filter fun x => !(f x).isEmpty).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.filter_cons, List.flatMap_cons]
    cases empty : (f x).isEmpty
    · simp [ih]
    · simp [List.isEmpty_iff.mp empty, ih]

/-- The committees of a slot with an honest member, each with its position.

Each is read at its position, below the count, and has an honest member.

Their positions increase strictly, and their honest signers are those of all the committees.

They are some of the committees, in order. -/
private theorem selected_spec {honest : Finset ValidatorIndex} {slot : Slot} {count : Nat}
    {committees : List (Array ValidatorIndex)} (lengths : committees.length = count)
    (each : ∀ (position : Nat) (below : position < committees.length),
      getBeaconCommittee state slot position.toUInt64 = .ok committees[position]) :
    (∀ pair ∈ ((List.range count).zip committees).filter
        (fun pair => !(honestSigners honest pair.2).isEmpty),
      pair.1 < count ∧ getBeaconCommittee state slot pair.1.toUInt64 = .ok pair.2 ∧
        honestSigners honest pair.2 ≠ []) ∧
    ((((List.range count).zip committees).filter
        (fun pair => !(honestSigners honest pair.2).isEmpty)).map (·.1)).Pairwise (· < ·) ∧
    (((List.range count).zip committees).filter
        (fun pair => !(honestSigners honest pair.2).isEmpty)).flatMap
      (fun pair => honestSigners honest pair.2) = committees.flatMap (honestSigners honest) ∧
    ((((List.range count).zip committees).filter
        (fun pair => !(honestSigners honest pair.2).isEmpty)).map (·.2)).Sublist committees := by
  have firsts : ((List.range count).zip committees).map (·.1) = List.range count :=
    List.map_fst_zip (by simp [lengths])
  have seconds : ((List.range count).zip committees).map (·.2) = committees :=
    List.map_snd_zip (by simp [lengths])
  refine ⟨fun pair member => ?_, ?_, ?_, ?_⟩
  · obtain ⟨zipped, kept⟩ := List.mem_filter.mp member
    obtain ⟨i, inside, rfl⟩ := List.getElem_of_mem zipped
    simp only [List.length_zip, List.length_range, lengths, Nat.min_self] at inside
    simp only [List.getElem_zip, List.getElem_range]
    refine ⟨inside, each i (by omega), ?_⟩
    simpa [List.getElem_zip] using kept
  · have sub := (List.filter_sublist (p := fun pair : Nat × Array ValidatorIndex =>
      !(honestSigners honest pair.2).isEmpty) (l := (List.range count).zip committees)).map
        (·.1)
    rw [firsts] at sub
    exact List.pairwise_lt_range.sublist sub
  · rw [flatMap_filter_nonempty (fun pair : Nat × Array ValidatorIndex =>
      honestSigners honest pair.2), List.flatMap, List.flatMap]
    conv_rhs => rw [← seconds, List.map_map]
    rfl
  · have sub := (List.filter_sublist (p := fun pair : Nat × Array ValidatorIndex =>
      !(honestSigners honest pair.2).isEmpty) (l := (List.range count).zip committees)).map
        (·.2)
    rwa [seconds] at sub

/-- Joining arrays from an accumulator gives the accumulator, then each array in turn. -/
private theorem foldl_append_toList {α β : Type} (f : α → Array β) (l : List α) (acc : Array β) :
    ((l.map f).foldl (· ++ ·) acc).toList = acc.toList ++ l.flatMap fun x => (f x).toList := by
  induction l generalizing acc with
  | nil => simp
  | cons x rest ih => simp [ih]

/-- The honest signers of committees are some of their members, in order. -/
private theorem flatMap_honestSigners_sublist (honest : Finset ValidatorIndex)
    (committees : List (Array ValidatorIndex)) :
    (committees.flatMap (honestSigners honest)).Sublist (committees.flatMap Array.toList) := by
  induction committees with
  | nil => exact List.Sublist.slnil
  | cons committee rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons]
    exact ((List.dedup_sublist _).trans List.filter_sublist).append ih

/-- From Electra, the committees that committee bits name are below their number. -/
private theorem lt_of_mem_getCommitteeIndices {count : Nat}
    {bits : Serialization.Ssz.Bitvector count} {index : CommitteeIndex}
    (member : index ∈ getCommitteeIndices bits) : index.toNat < count := by
  unfold getCommitteeIndices at member
  simp only [List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    List.mem_zipIdx_iff_getElem?, Prod.exists] at member
  obtain ⟨bit, position, found, -, rfl⟩ := member
  have inside := (List.getElem?_eq_some_iff.mp found).1
  simp only [Vector.length_toList] at inside
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) inside

/-! ## The honest attestations of the committees -/

/-- From Electra, the honest attestations of committees read at their positions.

Each names its committee alone and holds the data.

Its bits are one per member of its committee, set when that member is honest.

Its signature aggregates the signatures of the honest signers of its committee. -/
private theorem honestAttestations_spec (electra : .pectra ≤ fork)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {data : AttestationData} {domain : Domain} {root : Root}
    (domained :
      getDomain config state DOMAIN_BEACON_ATTESTER (some data.target.epoch) = .ok domain)
    (rooted : computeSigningRoot data domain = .ok root)
    {selected : List (Nat × Array ValidatorIndex)}
    {aggregates : List (Attestation preset fork)}
    (good : ∀ pair ∈ selected, getBeaconCommittee state data.slot pair.1.toUInt64 = .ok pair.2)
    (made : List.Forall₂ (fun pair aggregate =>
      honestAttestation config state honest key data pair.1.toUInt64 = .ok aggregate)
        selected aggregates) :
    List.Forall₂ (fun key aggregate =>
        getCommitteeIndices (aggregate.committeeBits electra) = [key])
      (selected.map (·.1.toUInt64)) aggregates ∧
    (∀ aggregate ∈ aggregates, aggregate.data = data) ∧
    aggregates.map (·.aggregationBits.bits) = selected.map (fun pair =>
      Array.ofFn fun seat : Fin pair.2.size => decide (pair.2[seat] ∈ honest)) ∧
    List.Forall₂ (fun keys joint => ∃ signatures,
        List.Forall₂ (fun secret signature =>
          Signatures.sign secret (Base.packBytes root) = .ok signature) keys signatures ∧
        Signatures.aggregate signatures.toArray = .ok joint)
      (selected.map fun pair => (honestSigners honest pair.2).map key)
      (aggregates.map (·.signature)) := by
  -- Each honest attestation is described by its committee, which is the one read at its position.
  have described : List.Forall₂ (fun pair aggregate =>
      getCommitteeIndices (aggregate.committeeBits electra) = [pair.1.toUInt64] ∧
      aggregate.data = data ∧
      aggregate.aggregationBits.bits =
        Array.ofFn (fun seat : Fin pair.2.size => decide (pair.2[seat] ∈ honest)) ∧
      ∃ signatures, List.Forall₂ (fun secret signature =>
          Signatures.sign secret (Base.packBytes root) = .ok signature)
        ((honestSigners honest pair.2).map key) signatures ∧
        Signatures.aggregate signatures.toArray = .ok aggregate.signature)
      selected aggregates := by
    refine ((List.forall₂_and_left _ _).mpr ⟨good, made⟩).imp fun pair aggregate facts => ?_
    obtain ⟨committeeOk, built⟩ := facts
    obtain ⟨committee, otherOk, named, sameData, bits, signatures, signed, aggregated⟩ :=
      honestAttestation_spec electra built
    rw [committeeOk, Except.ok.injEq] at otherOk
    subst otherOk
    refine ⟨named, sameData, bits, signatures, ?_, aggregated⟩
    rw [List.forall₂_map_left_iff]
    exact signed.imp fun _ _ one => sign_of_getAttestationSignature domained rooted one
  refine ⟨List.forall₂_map_left_iff.mpr (described.imp fun _ _ facts => facts.1),
    fun aggregate member => ?_, ?_, ?_⟩
  · obtain ⟨pair, -, facts⟩ := exists_mem_of_forall₂ described.flip member
    exact facts.2.1
  · have same : List.Forall₂ (· = ·) (aggregates.map (·.aggregationBits.bits))
        (selected.map (fun pair =>
          Array.ofFn fun seat : Fin pair.2.size => decide (pair.2[seat] ∈ honest))) := by
      rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
      exact described.flip.imp fun _ _ facts => facts.2.2.1
    rwa [List.forall₂_eq_eq_eq] at same
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact described.imp fun _ _ facts => facts.2.2.2

/-- The committees of a slot with an honest member, by index, from the committees of the slot. -/
private theorem honestCommittees_eq {honest : Finset ValidatorIndex} {slot : Slot}
    {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).mapM
      (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees) :
    honestCommittees state honest slot = .ok ((((List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).zip
      committees).filter fun pair => !(honestSigners honest pair.2).isEmpty).map
        (·.1.toUInt64)) := by
  unfold honestCommittees
  dsimp only
  rw [committeesOk]
  rfl

/-- The committees of a slot are each read at their position. -/
private theorem committees_each {slot : Slot} {count : Nat}
    {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range count).mapM
      (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees) :
    committees.length = count ∧ ∀ (position : Nat) (below : position < committees.length),
      getBeaconCommittee state slot position.toUInt64 = .ok committees[position] := by
  obtain ⟨lengths, each⟩ := mapM_eq_ok_iff.mp committeesOk
  rw [List.length_range] at lengths
  refine ⟨lengths, fun position below => ?_⟩
  have read := each position (by rw [List.length_range]; omega)
  rwa [List.getElem_range] at read

/-- The committees of a slot with an honest member, each with its position, as they are selected.

Each is read at its position, below the count, and has an honest member.

Their positions increase strictly, also as 64-bit indices.

Their honest signers are those of all the committees, and they are some of the committees. -/
private theorem selected_exists {honest : Finset ValidatorIndex} {slot : Slot}
    {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat).mapM
      (fun position => getBeaconCommittee state slot position.toUInt64) = .ok committees) :
    ∃ selected : List (Nat × Array ValidatorIndex),
      honestCommittees state honest slot = .ok (selected.map (·.1.toUInt64)) ∧
      (∀ pair ∈ selected,
        pair.1 < (getCommitteeCountPerSlot state (computeEpochAtSlot preset slot)).toNat ∧
        getBeaconCommittee state slot pair.1.toUInt64 = .ok pair.2 ∧
        honestSigners honest pair.2 ≠ []) ∧
      (selected.map (·.1)).Pairwise (· < ·) ∧
      (selected.map (·.1.toUInt64)).Pairwise (· ≤ ·) ∧
      selected.flatMap (fun pair => honestSigners honest pair.2) =
        committees.flatMap (honestSigners honest) ∧
      (selected.map (·.2)).Sublist committees := by
  obtain ⟨lengths, each⟩ := committees_each committeesOk
  obtain ⟨good, increasing, flat, sub⟩ := selected_spec (honest := honest) lengths each
  refine ⟨_, honestCommittees_eq committeesOk, good, increasing, ?_, flat, sub⟩
  -- The positions are below a 64-bit count, so their indices keep their order.
  refine List.pairwise_map.mpr ((List.pairwise_map.mp increasing).imp_of_mem
    fun first second lt => ?_)
  exact UInt64.le_of_lt (toUInt64_lt_toUInt64 lt
    (Nat.lt_trans (good _ second).1 (UInt64.toNat_lt _)))

/-- From Electra, the honest aggregate of a slot is built when its committees have values.

The largest number of committees of a slot is positive.

Some committee of the slot has an honest member.

Before Gloas, the committees of the slot together fit the bits of an attestation. -/
theorem honestSlotAggregate_exists_ok (electra : .pectra ≤ fork)
    (positive : 0 < preset.MAX_COMMITTEES_PER_SLOT)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {data : AttestationData} {committees : List (Array ValidatorIndex)}
    (committeesOk : (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset data.slot)).toNat).mapM
      (fun position => getBeaconCommittee state data.slot position.toUInt64) = .ok committees)
    (fits : fork < .glamsterdam → (committees.map Array.size).sum ≤ maxAttesters preset fork)
    (someHonest : ∃ committee ∈ committees, honestSigners honest committee ≠ []) :
    ∃ attestation,
      honestSlotAggregate electra config state honest key data = .ok attestation := by
  -- The count of committees of a slot is at most the largest number, which is positive.
  have countBelow : (getCommitteeCountPerSlot state (computeEpochAtSlot preset data.slot)).toNat ≤
      preset.MAX_COMMITTEES_PER_SLOT.toNat := by
    have bounded := getCommitteeCountPerSlot_le state (computeEpochAtSlot preset data.slot)
    simp only [max, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at bounded positive ⊢
    split at bounded <;> simp_all
  obtain ⟨selected, covered, good, -, ordered, flat, sub⟩ :=
    selected_exists (honest := honest) committeesOk
  -- A selected committee is one of the slot, so it fits the bits of an attestation.
  have within : ∀ pair ∈ selected, pair.2 ∈ committees := fun pair member =>
    sub.subset (List.mem_map_of_mem member)
  have sized : ∀ pair ∈ selected, pair.2.size ≤ (committees.map Array.size).sum :=
    fun pair member => List.le_sum_of_mem (List.mem_map_of_mem (within pair member))
  -- Each selected committee has an honest attestation.
  obtain ⟨aggregates, aggregatesOk⟩ := mapM_exists_ok
    (f := honestAttestation config state honest key data) (xs := selected.map (·.1.toUInt64))
    fun committeeIndex member => by
      obtain ⟨pair, kept, rfl⟩ := List.mem_map.mp member
      obtain ⟨below, committeeOk, someSigner⟩ := good pair kept
      exact honestAttestation_exists_ok (fun before => absurd electra before) committeeOk
        (fun gloas => (sized pair kept).trans (fits gloas))
        (fun _ => toUInt64_lt_of_lt (Nat.lt_of_lt_of_le below countBelow))
        someSigner
  have made := List.forall₂_map_left_iff.mp (forall₂_of_mapM_ok aggregatesOk)
  obtain ⟨domain, domained⟩ :=
    getDomain_total config state DOMAIN_BEACON_ATTESTER (some data.target.epoch)
  obtain ⟨root, rooted⟩ := computeSigningRoot_total data domain
  obtain ⟨named, -, bitsEq, joined⟩ := honestAttestations_spec electra domained rooted
    (fun pair member => (good pair member).2.1) made
  -- Some committee has an honest member, so some committee is selected.
  have someSelected : selected ≠ [] := by
    obtain ⟨committee, member, someSigner⟩ := someHonest
    obtain ⟨signer, signerMember⟩ := List.exists_mem_of_ne_nil _ someSigner
    intro empty
    have joinedMember : signer ∈ committees.flatMap (honestSigners honest) :=
      List.mem_flatMap.mpr ⟨committee, member, signerMember⟩
    rw [← flat, empty] at joinedMember
    simp at joinedMember
  have nonempty : aggregates ≠ [] := by
    intro empty
    subst empty
    exact someSelected (List.forall₂_nil_right_iff.mp made)
  -- The bits of the aggregates are those of the selected committees, which fit.
  have bitsFit : fork < .glamsterdam →
      ((aggregates.map (·.aggregationBits.bits)).foldl (· ++ ·) #[]).size ≤
        maxAttesters preset fork := by
    intro gloas
    have total : ((selected.map (·.2)).map Array.size).sum ≤ (committees.map Array.size).sum :=
      (sub.map Array.size).sum_le_sum fun _ _ => Nat.zero_le _
    rw [← Array.length_toList, bitsEq, foldl_append_toList]
    simp only [List.nil_append, List.length_flatMap, Array.toList_ofFn,
      List.length_ofFn]
    simpa [List.map_map, Function.comp_def] using total.trans (fits gloas)
  obtain ⟨signature, aggregated⟩ := Signatures.aggregate_of_groups_exists_ok joined
    (by simpa using someSelected)
  obtain ⟨attestation, joinedOk⟩ :=
    computeOnChainAggregate_exists_ok named ordered nonempty bitsFit ⟨signature, aggregated⟩
  refine ⟨attestation, ?_⟩
  unfold honestSlotAggregate
  rw [covered, mapError_ok_bind, aggregatesOk, mapError_ok_bind]
  exact joinedOk

/-- From Electra until Gloas, the honest aggregate of a slot is accepted.

Each honest member of each committee of the slot then holds the timely target flag.

That needs the state to hold the target root for the first slot of the target epoch.

The data and the state meet the checks of the attestation step, and the state is within a budget.

The active validators of the epoch times its committees must fit in 64 bits.

Then the committees of the slot do not overlap.

The registry holds the key of each honest validator.

The secret keys of the honest members of the committees of the slot must not sum to zero.

The signature check is that of BLS. -/
theorem processAttestation_honestSlotAggregate {budget scoreBound : Nat}
    (electra : .pectra ≤ fork) (beforeGloas : fork < .glamsterdam)
    {honest : Finset ValidatorIndex} {key : ValidatorIndex → Signatures.SecretKey}
    {data : AttestationData} {committees : List (Array ValidatorIndex)}
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
    (indexed : data.index = 0)
    (committeesOk : (List.range
        (getCommitteeCountPerSlot state (computeEpochAtSlot preset data.slot)).toNat).mapM
      (fun position => getBeaconCommittee state data.slot position.toUInt64) = .ok committees)
    (shuffleRoom : (getActiveValidatorIndices state (computeEpochAtSlot preset data.slot)).length *
      ((getCommitteeCountPerSlot state (computeEpochAtSlot preset data.slot)).toNat *
        preset.SLOTS_PER_EPOCH.toNat) < 2 ^ 64)
    (source : data.source = if data.target.epoch = getCurrentEpoch state then
        state.currentJustifiedCheckpoint
      else state.previousJustifiedCheckpoint)
    (registered : ∀ index ∈ honest, ∃ validator,
      getValidator state index = .ok validator ∧ validator.pubkey = Signatures.skToPk (key index))
    (sum : (((committees.flatMap (honestSigners honest)).map key).map (·.val)).sum ≠ 0)
    (proposer : ∃ index, getBeaconProposerIndex state = .ok index ∧
      index.toNat < state.validators.data.size)
    (built : honestSlotAggregate electra config state honest key data = .ok attestation) :
    ∃ after, processAttestation config .bls state parentSlot attestation = .ok after ∧
      (getBlockRoot state data.target.epoch = .ok data.target.root →
        ∀ committee ∈ committees, ∀ index ∈ committee, index ∈ honest →
          TargetFlagAt (recentParticipation after (Nat.le_trans (by decide) electra)
            (data.target.epoch == getCurrentEpoch state)) index.toNat) := by
  have notGloas : ¬.glamsterdam ≤ fork := Nat.not_le_of_lt beforeGloas
  -- The committees of the slot with an honest member, each with its position.
  obtain ⟨selected, covered, good, increasing, ordered, flat, -⟩ :=
    selected_exists (honest := honest) committeesOk
  -- The aggregate joins the honest attestations of those committees.
  unfold honestSlotAggregate at built
  obtain ⟨keys, keysOk, built⟩ := bind_ok_iff.mp built
  rw [mapError_ok_iff, covered, Except.ok.injEq] at keysOk
  subst keysOk
  obtain ⟨aggregates, aggregatesOk, built⟩ := bind_ok_iff.mp built
  have made := List.forall₂_map_left_iff.mp (forall₂_of_mapM_ok (mapError_ok_iff.mp aggregatesOk))
  obtain ⟨domain, domained⟩ :=
    getDomain_total config state DOMAIN_BEACON_ATTESTER (some data.target.epoch)
  obtain ⟨root, rooted⟩ := computeSigningRoot_total data domain
  obtain ⟨named, datas, bitsEq, joined⟩ := honestAttestations_spec electra domained rooted
    (fun pair member => (good pair member).2.1) made
  obtain ⟨bitsOf, signatureOf, ⟨first, firstMember, dataOf⟩, committeeBitsOf⟩ :=
    computeOnChainAggregate_of_ordered named ordered built
  have sameData : attestation.data = data := dataOf.trans (datas first firstMember)
  -- The bits are those of the committees in turn, one per member, set when it is honest.
  have split : attestation.aggregationBits.bits.toList = [] ++ selected.flatMap fun pair =>
      List.ofFn fun seat : Fin pair.2.size => decide (pair.2[seat] ∈ honest) := by
    rw [bitsOf, bitsEq, foldl_append_toList]
    simp
  -- The committee bits name the committees, each below the largest number of committees.
  have inside : ∀ position ∈ selected.map (·.1),
      position < preset.MAX_COMMITTEES_PER_SLOT.toNat := by
    intro position member
    obtain ⟨pair, kept, rfl⟩ := List.mem_map.mp member
    obtain ⟨aggregate, -, one⟩ := exists_mem_of_forall₂ named
      (List.mem_map_of_mem (f := fun pair : Nat × Array ValidatorIndex => pair.1.toUInt64) kept)
    have below := lt_of_mem_getCommitteeIndices (one ▸ List.mem_singleton_self _)
    rwa [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt'
      (Nat.lt_trans (good pair kept).1 (UInt64.toNat_lt _))] at below
  have indices : getCommitteeIndices (attestation.committeeBits electra) =
      selected.map (·.1.toUInt64) := by
    rw [committeeBitsOf]
    have same : selected.map (·.1.toUInt64) = (selected.map (·.1)).map Nat.toUInt64 := by
      rw [List.map_map]
      rfl
    rw [same]
    exact getCommitteeIndices_ofFn_contains increasing inside
  -- Each committee has an honest attester, and the bits run over the committees exactly.
  have committeesChecked : checkAttestationCommittees state attestation = .ok () := by
    have size := attestationCommitteesSize_honest holds.within (sameData ▸ slotEpoch) selected
      (sameData ▸ good) split
    unfold checkAttestationCommittees
    rw [dite_eq_left electra, ite_eq_right notGloas, indices]
    simp only [ensure, sameData, indexed, ↓reduceIte, ok_bind]
    rw [sameData, List.length_nil] at size
    rw [size, ok_bind, ite_eq_left rfl]
  -- The signers are the honest members of the committees, and there is one at least.
  have signersNonempty : committees.flatMap (honestSigners honest) ≠ [] := by
    intro empty
    exact sum (by rw [empty]; rfl)
  obtain ⟨signer, signerMember⟩ := List.exists_mem_of_ne_nil _ signersNonempty
  obtain ⟨pair, kept, -⟩ := List.mem_flatMap.mp (flat ▸ signerMember)
  obtain ⟨active, shuffled, shuffleOk⟩ :=
    attesterShuffle_ok_of_getBeaconCommittee (good pair kept).2.1
  -- The attesters are the honest members of the committees.
  obtain ⟨attesters, attestersOk, members⟩ := committeesAttestersOf_honest shuffleOk selected
    (fun pair member => (good pair member).2.1) split
  have computed : getAttestingIndices state attestation = .ok (sortedSet attesters) := by
    rw [getAttestingIndices_of_attesterShuffle (sameData ▸ shuffleOk)]
    unfold attestingIndicesOf
    rw [dite_eq_left electra, indices, sameData]
    simp only [List.length_nil] at attestersOk
    simp only [attestersOk, bind, Except.bind, pure, Except.pure]
  have membersAll : ∀ index, index ∈ sortedSet attesters ↔
      index ∈ committees.flatMap (honestSigners honest) := by
    intro index
    rw [mem_sortedSet, members, ← flat, List.mem_flatMap]
  -- The committees of the slot do not overlap, so the signers are distinct.
  have distinct : (committees.flatMap (honestSigners honest)).Nodup :=
    (getBeaconCommittees_nodup holds.within shuffleRoom committeesOk).sublist
      (flatMap_honestSigners_sublist honest committees)
  have permuted : (sortedSet attesters).Perm (committees.flatMap (honestSigners honest)) :=
    (List.perm_ext_iff_of_nodup ((getAttestingIndices_sorted computed).imp
      fun {first second} lt (same : first = second) => UInt64.lt_irrefl _ (same ▸ lt))
      distinct).mpr membersAll
  -- The aggregate signature verifies under the keys of all signers.
  have flatKeys : (selected.map fun pair => (honestSigners honest pair.2).map key).flatten =
      (committees.flatMap (honestSigners honest)).map key := by
    rw [← flat, List.map_flatMap, List.flatMap]
  have verifies := Signatures.fastAggregateVerify_aggregate_of_groups joined
    (by rw [flatKeys]; simpa using signersNonempty) (by rwa [flatKeys]) signatureOf
  rw [flatKeys] at verifies
  have valid := isValidIndexedAttestation_of_fastAggregateVerify computed sameData permuted
    signersNonempty (fun gloas => absurd gloas notGloas)
    (fun index member => registered index
      (mem_honestSigners.mp (List.mem_flatMap.mp member).choose_spec.2).2)
    domained rooted (by simpa only [List.map_map] using verifies)
  -- From Electra the deadline of the inclusion window is gone.
  have deadline : fork < .dencun →
      state.slot.toNat ≤ data.slot.toNat + preset.SLOTS_PER_EPOCH.toNat := fun dencun =>
    absurd (Nat.le_trans (by decide : Base.Fork.dencun ≤ .pectra) electra)
      (Nat.not_le_of_lt dencun)
  subst sameData
  obtain ⟨after, processed, flags⟩ := processAttestation_exists_ok
    (Nat.le_trans (by decide) electra) beforeGloas parentSlot roots slotRoom increment scaled
    holds participation room recent slotEpoch past early deadline committeesChecked source valid
    proposer
  refine ⟨after, processed, fun rooted committee member index seated honestMember =>
    flags _ computed rooted index ((membersAll index).mpr ?_)⟩
  exact List.mem_flatMap.mpr ⟨committee, member, mem_honestSigners.mpr ⟨seated, honestMember⟩⟩

end EthLib.Consensus
