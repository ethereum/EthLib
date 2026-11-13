module

public import EthLib.Base.Proofs.List
public import EthLib.Consensus.BeaconApi.Registries

/-!
# Proofs: the registry answers of the Beacon API

An entry is in the validators answer exactly when four conditions hold.

The request names its index.

Its record and its balance are those of the state.

Its status is the status at the current epoch, and it passes the filter.

An empty request names every validator.

Otherwise an identifier names an index by its value, or by the public key of its validator.

Each index appears at most once, so the entries of an answer fix it up to order.

The balances and identities answers follow the same rule, without a filter.

The builders answer follows the same rule, with a filter on the status of a builder.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base Cryptography.Bls

variable {preset : Preset} {fork : Fork}

/-- A word of 64 bits that comes from a natural number is at most that number. -/
private theorem toNat_ofNat_le (n : Nat) : (UInt64.ofNat n).toNat ≤ n := by
  simp [Nat.mod_le]

/-- An index names itself when it is below the size of the registry, and nothing otherwise. -/
theorem resolveValidatorId_index {state : BeaconState preset fork} {i index : ValidatorIndex} :
    resolveValidatorId state (.index i) = some index ↔
      i = index ∧ index.toNat < state.validators.data.size := by
  simp only [resolveValidatorId]
  split
  · constructor
    · intro h
      cases h
      exact ⟨rfl, by assumption⟩
    · rintro ⟨rfl, _⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    intro h; subst h; omega

/-- A public key names the first position of the registry whose validator holds it. -/
theorem resolveValidatorId_pubkey {state : BeaconState preset fork} {pubkey : BLSPubkey}
    {index : ValidatorIndex} :
    resolveValidatorId state (.pubkey pubkey) = some index ↔
      ∃ position validator, state.validators.data[position]? = some validator ∧
        validator.pubkey = pubkey ∧
        (∀ j < position, ∀ other, state.validators.data[j]? = some other →
          other.pubkey ≠ pubkey) ∧
        index = UInt64.ofNat position := by
  simp only [resolveValidatorId, Option.map_eq_some_iff, Array.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨n, ⟨hn, hp, hbefore⟩, rfl⟩
    refine ⟨n, _, Array.getElem?_eq_getElem hn, by simpa using hp, ?_, rfl⟩
    intro j hj other hother
    have hjn : j < state.validators.data.size := by omega
    rw [Array.getElem?_eq_getElem hjn] at hother
    cases hother
    simpa using hbefore j hj
  · rintro ⟨n, validator, hv, hp, hbefore, rfl⟩
    have hn := (Array.getElem?_eq_some_iff.mp hv).1
    refine ⟨n, ⟨hn, ?_, ?_⟩, rfl⟩
    · have := (Array.getElem?_eq_some_iff.mp hv).2
      simpa [this] using hp
    · intro j hj
      have := hbefore j hj _ (Array.getElem?_eq_getElem (by omega))
      simpa using this

/-- An empty request selects every index below the size, and any other request each named index. -/
private theorem mem_selectIndices {size : Nat} {resolve : ValidatorId → Option UInt64}
    {ids : List ValidatorId} {index : UInt64} :
    index ∈ selectIndices size resolve ids ↔
      (ids = [] ∧ index.toNat < size) ∨ ∃ id ∈ ids, resolve id = some index := by
  unfold selectIndices
  by_cases hids : ids = []
  · subst hids
    simp only [List.isEmpty_nil, ite_true, List.mem_map, List.mem_range, List.not_mem_nil,
      or_false, true_and, exists_false, false_and]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have := toNat_ofNat_le n
      omega
    · intro h
      have := index.toNat_lt_size
      exact ⟨index.toNat, by omega, by simp⟩
  · have : ids.isEmpty = false := by simpa using hids
    simp [this, hids, List.mem_mergeSort, List.mem_eraseDups, List.mem_filterMap]

/-- A selection holds each index at most once. -/
private theorem selectIndices_nodup (size : Nat) (resolve : ValidatorId → Option UInt64)
    (ids : List ValidatorId) : (selectIndices size resolve ids).Nodup := by
  unfold selectIndices
  split
  · rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.nodup_range
    intro a b ha hb hne h
    have ha := List.mem_range.mp ha
    have hb := List.mem_range.mp hb
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' (by omega), UInt64.toNat_ofNat_of_lt' (by omega)] at this
    omega
  · exact (List.mergeSort_perm _ _).nodup_iff.mpr (nodup_eraseDups _)

/-- The selection of one identifier is the index that it names, or nothing. -/
private theorem selectIndices_single (size : Nat) (resolve : ValidatorId → Option UInt64)
    (id : ValidatorId) : selectIndices size resolve [id] = (resolve id).toList := by
  unfold selectIndices
  cases h : resolve id <;> simp [h, List.eraseDups_cons, List.eraseDups_nil]

/-- An empty request selects every index of the registry.

Otherwise it selects each index that one of its identifiers names. -/
theorem mem_selectValidators {state : BeaconState preset fork} {ids : List ValidatorId}
    {index : ValidatorIndex} :
    index ∈ selectValidators state ids ↔
      (ids = [] ∧ index.toNat < state.validators.data.size) ∨
        ∃ id ∈ ids, resolveValidatorId state id = some index :=
  mem_selectIndices

/-- A request selects each index at most once. -/
theorem selectValidators_nodup (state : BeaconState preset fork) (ids : List ValidatorId) :
    (selectValidators state ids).Nodup :=
  selectIndices_nodup _ _ _

/-- The validators answer holds each requested index that has a balance.

Its status at the current epoch must pass the filter.

Its entry has the record and the balance of the state. -/
theorem stateValidators_mem {state : BeaconState preset fork} {ids : List ValidatorId}
    {filter : StatusFilter} {entry : ValidatorResponse} :
    entry ∈ stateValidators state ids filter ↔
      ((ids = [] ∧ entry.index.toNat < state.validators.data.size) ∨
          ∃ id ∈ ids, resolveValidatorId state id = some entry.index) ∧
        state.validators.data[entry.index.toNat]? = some entry.validator ∧
        state.balances.data[entry.index.toNat]? = some entry.balance ∧
        entry.status = validatorStatus entry.validator entry.balance (getCurrentEpoch state) ∧
        filter.passes entry.status = true := by
  unfold stateValidators
  simp only [List.mem_filterMap, mem_selectValidators]
  constructor
  · rintro ⟨a, ha, h⟩
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨validator, hv, balance, hb, h⟩ := h
    split at h
    · cases h
      exact ⟨ha, hv, hb, rfl, by assumption⟩
    · cases h
  · rintro ⟨ha, hv, hb, hs, hp⟩
    refine ⟨entry.index, ha, ?_⟩
    simp only [bind, Option.bind_eq_some_iff, hv, hb]
    cases entry
    simp_all

/-- The balance of each entry of the validators answer is the balance of its index. -/
theorem stateValidators_balance {state : BeaconState preset fork} {ids : List ValidatorId}
    {filter : StatusFilter} {entry : ValidatorResponse}
    (mem : entry ∈ stateValidators state ids filter) :
    state.balances.data[entry.index.toNat]? = some entry.balance :=
  (stateValidators_mem.mp mem).2.2.1

/-- The validators answer has each index at most once. -/
theorem stateValidators_nodup (state : BeaconState preset fork) (ids : List ValidatorId)
    (filter : StatusFilter) :
    ((stateValidators state ids filter).map (·.index)).Nodup := by
  have sub : ((stateValidators state ids filter).map (·.index)).Sublist
      (selectValidators state ids) := by
    unfold stateValidators
    generalize selectValidators state ids = l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filterMap_cons]
      split
      · exact ih.cons _
      · rename_i entry h
        simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨validator, _, balance, _, h⟩ := h
        split at h
        · cases h
          simpa using ih.cons_cons a
        · cases h
  exact sub.nodup (selectValidators_nodup state ids)

/-- The selection of one identifier is the index that it names, or nothing. -/
private theorem selectValidators_single (state : BeaconState preset fork) (id : ValidatorId) :
    selectValidators state [id] = (resolveValidatorId state id).toList :=
  selectIndices_single _ _ _

/-- The endpoint for one validator answers the entry of the index that the identifier names.

The entry has the record and the balance of the state, and the status at the current epoch. -/
theorem stateValidator_ok {state : BeaconState preset fork} {id : ValidatorId}
    {entry : ValidatorResponse} :
    stateValidator state id = .ok entry ↔
      resolveValidatorId state id = some entry.index ∧
        state.validators.data[entry.index.toNat]? = some entry.validator ∧
        state.balances.data[entry.index.toNat]? = some entry.balance ∧
        entry.status = validatorStatus entry.validator entry.balance (getCurrentEpoch state) := by
  unfold stateValidator
  unfold stateValidators
  rw [selectValidators_single]
  cases h : resolveValidatorId state id with
  | none => simp
  | some i =>
    simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil]
    cases hv : state.validators.data[i.toNat]? with
    | none => simp; intro hi; subst hi; simp_all
    | some validator =>
      cases hb : state.balances.data[i.toNat]? with
      | none => simp; intro hi; subst hi; simp_all
      | some balance =>
        simp only [bind, Option.bind_some, StatusFilter.passes, List.isEmpty_nil, Bool.true_or,
          ite_true, Except.ok.injEq, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨rfl, hv, hb, rfl⟩
        · rintro ⟨hi, hv', hb', hs⟩
          cases entry
          simp_all

/-- The balances answer holds each requested index that has a balance, with that balance. -/
theorem stateBalances_mem {state : BeaconState preset fork} {ids : List ValidatorId}
    {entry : ValidatorBalanceResponse} :
    entry ∈ stateBalances state ids ↔
      ((ids = [] ∧ entry.index.toNat < state.validators.data.size) ∨
          ∃ id ∈ ids, resolveValidatorId state id = some entry.index) ∧
        state.balances.data[entry.index.toNat]? = some entry.balance := by
  unfold stateBalances
  simp only [List.mem_filterMap, mem_selectValidators, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, balance, hb, rfl⟩
    exact ⟨ha, hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨entry.index, ha, entry.balance, hb, rfl⟩

/-- The identities answer holds each requested index.

Its entry has the public key and the activation epoch of its validator. -/
theorem stateIdentities_mem {state : BeaconState preset fork} {ids : List ValidatorId}
    {entry : ValidatorIdentityResponse} :
    entry ∈ stateIdentities state ids ↔
      ((ids = [] ∧ entry.index.toNat < state.validators.data.size) ∨
          ∃ id ∈ ids, resolveValidatorId state id = some entry.index) ∧
        ∃ validator, state.validators.data[entry.index.toNat]? = some validator ∧
          entry.pubkey = validator.pubkey ∧ entry.activationEpoch = validator.activationEpoch := by
  unfold stateIdentities
  simp only [List.mem_filterMap, mem_selectValidators, Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, validator, hv, rfl⟩
    exact ⟨ha, validator, hv, rfl, rfl⟩
  · rintro ⟨ha, validator, hv, hp, he⟩
    exact ⟨entry.index, ha, validator, hv, by cases entry; simp_all⟩

/-- The endpoint for one validator fails only with code 404. -/
theorem stateValidator_error_code {state : BeaconState preset fork} {id : ValidatorId}
    {error : ErrorMessage} (h : stateValidator state id = .error error) : error.code = 404 := by
  unfold stateValidator at h
  split at h
  · cases h
  · cases h
    rfl

/-- The balances answer has each index at most once. -/
theorem stateBalances_nodup (state : BeaconState preset fork) (ids : List ValidatorId) :
    ((stateBalances state ids).map (·.index)).Nodup := by
  have sub : ((stateBalances state ids).map (·.index)).Sublist (selectValidators state ids) := by
    unfold stateBalances
    generalize selectValidators state ids = l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filterMap_cons]
      split
      · exact ih.cons _
      · rename_i entry h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨balance, _, rfl⟩ := h
        simpa using ih.cons_cons a
  exact sub.nodup (selectValidators_nodup state ids)

/-- The identities answer has each index at most once. -/
theorem stateIdentities_nodup (state : BeaconState preset fork) (ids : List ValidatorId) :
    ((stateIdentities state ids).map (·.index)).Nodup := by
  have sub : ((stateIdentities state ids).map (·.index)).Sublist (selectValidators state ids) := by
    unfold stateIdentities
    generalize selectValidators state ids = l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filterMap_cons]
      split
      · exact ih.cons _
      · rename_i entry h
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨balance, _, rfl⟩ := h
        simpa using ih.cons_cons a
  exact sub.nodup (selectValidators_nodup state ids)

/-- The reader of a filter takes the name of each status. -/
theorem StatusName.parse_status_name (status : ValidatorStatus) :
    StatusName.parse status.name = .ok (.status status) := by
  cases status <;> rfl

/-- The reader of a filter takes the name of each group. -/
theorem StatusName.parse_group_name (group : CoarseStatus) :
    StatusName.parse group.name = .ok (.group group) := by
  cases group <;> rfl

/-- More than 64 identifiers in a query string give the error with code 414. -/
theorem readValidatorIds_too_many {texts : List String} (long : texts.length > MAX_QUERY_IDS) :
    readValidatorIds true texts =
      .error { code := 414, message := "Too many validator IDs in request" } := by
  simp [readValidatorIds, long]

/-- An answer of the validators endpoint holds the same entries as the reference list. -/
theorem IsValidatorsAnswer.mem_iff {state : BeaconState preset fork} {ids : List ValidatorId}
    {filter : StatusFilter} {answer : List ValidatorResponse}
    (h : IsValidatorsAnswer state ids filter answer) {entry : ValidatorResponse} :
    entry ∈ answer ↔ entry ∈ stateValidators state ids filter :=
  List.Perm.mem_iff h

/-- An answer of the balances endpoint holds the same entries as the reference list. -/
theorem IsBalancesAnswer.mem_iff {state : BeaconState preset fork} {ids : List ValidatorId}
    {answer : List ValidatorBalanceResponse} (h : IsBalancesAnswer state ids answer)
    {entry : ValidatorBalanceResponse} : entry ∈ answer ↔ entry ∈ stateBalances state ids :=
  List.Perm.mem_iff h

/-- An answer of the identities endpoint holds the same entries as the reference list. -/
theorem IsIdentitiesAnswer.mem_iff {state : BeaconState preset fork} {ids : List ValidatorId}
    {answer : List ValidatorIdentityResponse} (h : IsIdentitiesAnswer state ids answer)
    {entry : ValidatorIdentityResponse} : entry ∈ answer ↔ entry ∈ stateIdentities state ids :=
  List.Perm.mem_iff h

/-! ## Builders -/

/-- The builders answer holds each requested builder whose status passes the filter.

Its entry has the record of the state, and the status that the state gives it. -/
theorem stateBuilders_mem {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {ids : List ValidatorId} {filter : List BuilderStatus} {entry : BuilderResponse} :
    entry ∈ stateBuilders state gloas ids filter ↔
      ((ids = [] ∧ entry.index.toNat < (state.builders gloas).data.size) ∨
          ∃ id ∈ ids, resolveBuilderId state gloas id = some entry.index) ∧
        (state.builders gloas).data[entry.index.toNat]? = some entry.builder ∧
        builderStatus state gloas entry.index = .ok entry.status ∧
        builderStatusPasses filter entry.status = true := by
  unfold stateBuilders
  simp only [List.mem_filterMap, mem_selectIndices]
  constructor
  · rintro ⟨a, ha, h⟩
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨builder, hv, status, hs, h⟩ := h
    split at h
    · cases h
      refine ⟨ha, hv, ?_, by assumption⟩
      revert hs
      cases builderStatus state gloas a <;> simp [Except.toOption]
    · cases h
  · rintro ⟨ha, hv, hs, hp⟩
    refine ⟨entry.index, ha, ?_⟩
    simp only [bind, Option.bind_eq_some_iff, hv, hs, Except.toOption]
    cases entry
    simp_all

/-- The builders answer has each index at most once. -/
theorem stateBuilders_nodup (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (ids : List ValidatorId) (filter : List BuilderStatus) :
    ((stateBuilders state gloas ids filter).map (·.index)).Nodup := by
  have sub : ((stateBuilders state gloas ids filter).map (·.index)).Sublist
      (selectIndices (state.builders gloas).data.size (resolveBuilderId state gloas) ids) := by
    unfold stateBuilders
    generalize selectIndices (state.builders gloas).data.size (resolveBuilderId state gloas) ids
      = l
    induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.filterMap_cons]
      split
      · exact ih.cons _
      · rename_i entry h
        simp only [bind, Option.bind_eq_some_iff] at h
        obtain ⟨builder, _, status, _, h⟩ := h
        split at h
        · cases h
          simpa using ih.cons_cons a
        · cases h
  exact sub.nodup (selectIndices_nodup _ _ _)

/-- An index names a builder when it is below the size of the registry, and nothing otherwise. -/
theorem resolveBuilderId_index {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {i index : BuilderIndex} :
    resolveBuilderId state gloas (.index i) = some index ↔
      i = index ∧ index.toNat < (state.builders gloas).data.size := by
  simp only [resolveBuilderId]
  split
  · constructor
    · intro h
      cases h
      exact ⟨rfl, by assumption⟩
    · rintro ⟨rfl, _⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    intro h; subst h; omega

/-- A public key names the first position of the registry whose builder holds it. -/
theorem resolveBuilderId_pubkey {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {pubkey : BLSPubkey} {index : BuilderIndex} :
    resolveBuilderId state gloas (.pubkey pubkey) = some index ↔
      ∃ position builder, (state.builders gloas).data[position]? = some builder ∧
        builder.pubkey = pubkey ∧
        (∀ j < position, ∀ other, (state.builders gloas).data[j]? = some other →
          other.pubkey ≠ pubkey) ∧
        index = UInt64.ofNat position := by
  simp only [resolveBuilderId, Option.map_eq_some_iff, Array.findIdx?_eq_some_iff_getElem]
  constructor
  · rintro ⟨n, ⟨hn, hp, hbefore⟩, rfl⟩
    refine ⟨n, _, Array.getElem?_eq_getElem hn, by simpa using hp, ?_, rfl⟩
    intro j hj other hother
    have hjn : j < (state.builders gloas).data.size := by omega
    rw [Array.getElem?_eq_getElem hjn] at hother
    cases hother
    simpa using hbefore j hj
  · rintro ⟨n, builder, hv, hp, hbefore, rfl⟩
    have hn := (Array.getElem?_eq_some_iff.mp hv).1
    refine ⟨n, ⟨hn, ?_, ?_⟩, rfl⟩
    · have := (Array.getElem?_eq_some_iff.mp hv).2
      simpa [this] using hp
    · intro j hj
      have := hbefore j hj _ (Array.getElem?_eq_getElem (by omega))
      simpa using this

/-- The reader of a filter takes the name of each builder status. -/
theorem BuilderStatus.parse_name (status : BuilderStatus) :
    BuilderStatus.parse status.name = .ok status := by
  cases status <;> rfl

/-- A state before Gloas gives the error with code 400 to the builders endpoint. -/
theorem buildersResponse_before_gloas {state : BeaconState preset fork}
    (before : ¬.glamsterdam ≤ fork) (ids : List ValidatorId) (filter : List BuilderStatus) :
    buildersResponse state ids filter = .error (beforeFork "builders" .glamsterdam) := by
  simp [buildersResponse, before]

/-- An answer of the builders endpoint holds the same entries as the reference list. -/
theorem IsBuildersAnswer.mem_iff {state : BeaconState preset fork} {gloas : .glamsterdam ≤ fork}
    {ids : List ValidatorId} {filter : List BuilderStatus} {answer : List BuilderResponse}
    (h : IsBuildersAnswer state gloas ids filter answer) {entry : BuilderResponse} :
    entry ∈ answer ↔ entry ∈ stateBuilders state gloas ids filter :=
  List.Perm.mem_iff h

end EthLib.Consensus.BeaconApi
