module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Common

/-!
# The final assembly

The headline follows from producers that this module and earlier ones prove.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section

open Cryptography.Bls

/-! ## Final assembly

The headline follows from four producers, each proved below.

They are the selected payments, their release, and the common ledgers after and before Electra.

Every other input on the path is proved above. -/

/-- What the release reads of the selected consolidation payments, after Electra. -/
def SelectedInputs {g x y : ForkedBeaconState preset} : Prop :=
  ∀ (_shared : Run config checks g x) (tail : Run config checks x y) high,
  Supported _shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
  ∀ events, tail.balanceEvents high = .ok events →
  ∀ electra : .pectra ≤ x.fork,
  ∃ calls : List (IndexedDepartureCall preset config),
  ∃ final consumed paidTags : List TaggedEntry,
  ∃ selected : List SelectedCharge, ∃ payments : List (Payment preset),
    FreshPaymentCoverage (config := config) events
      (initialTags (x.state.pendingConsolidations electra).data.toList)
      final consumed paidTags payments calls ∧
    FreshTags (config := config) (consumed ++ final) calls ∧
    paidTags.Sublist consumed ∧ SelectedPayments selected payments paidTags ∧
    ActualPaymentCoverage events payments (x.state.pendingConsolidations electra).data.toList

/-- After Electra the selected payments feed the release.

The allocation and issued tokens of the release feed the common ledger. -/
private theorem commonLedger_electra
    (hSelected : ∀ g x y : ForkedBeaconState preset,
      SelectedInputs (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hRelease : ∀ g x y : ForkedBeaconState preset,
      SelectedReleaseProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hLedgerElectra : ∀ {g x y : ForkedBeaconState preset}
      (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat),
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
      ∀ {ledger : RoundLedger tail high} {owned : Ownership}
        {tokens : BLSPubkey → Finset TokenOrigin},
      NewCohortAllocation tail high ledger owned tokens →
      gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high →
      ∀ cutoff, exitedBefore x cutoff ∩ recentKeys y.state = ∅ → cutoff ≤ high + 1 →
        stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
            drift (config := config) x high)
    {g x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork) :
    CommonLedger (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail high supported twoSlots cutoff apart within
  obtain ⟨genesis, _, _, _, early, _, _⟩ := id supported
  obtain ⟨events, replayed, -⟩ := shared.balanceEvents_bounded tail genesis early high
  obtain ⟨calls, final, consumed, paidTags, selected, payments, fresh, tags, _, chosen, actual⟩ :=
    hSelected g x y shared tail high supported twoSlots events replayed electra
  obtain ⟨ledger, -⟩ := (LedgerCuts.ofStops tail fun i => Classical.choice
    (Stop.exists tail i)).roundLedger_closed_electra shared supported electra twoSlots
  obtain ⟨_, _, after, tokens, _, _, _, terminal, ⟨allocation⟩, _, _, issued, _⟩ :=
    hRelease g x y shared tail high supported twoSlots events replayed electra selected payments
      paidTags actual chosen final consumed calls fresh tags ledger
  exact hLedgerElectra shared tail high supported twoSlots allocation
    ((gainWithoutPreviousOnly_le_issued terminal).trans issued) cutoff apart within

/-- The common ledger at every fork. -/
private theorem commonLedger_proved
    (hSelected : ∀ g x y : ForkedBeaconState preset,
      SelectedInputs (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hRelease : ∀ g x y : ForkedBeaconState preset,
      SelectedReleaseProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hLedgerElectra : ∀ {g x y : ForkedBeaconState preset}
      (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat),
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
      ∀ {ledger : RoundLedger tail high} {owned : Ownership}
        {tokens : BLSPubkey → Finset TokenOrigin},
      NewCohortAllocation tail high ledger owned tokens →
      gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high →
      ∀ cutoff, exitedBefore x cutoff ∩ recentKeys y.state = ∅ → cutoff ≤ high + 1 →
        stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
            drift (config := config) x high)
    (hLedgerPre : ∀ {g x y : ForkedBeaconState preset}
      (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat),
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → x.fork < .pectra →
      ∀ cutoff, exitedBefore x cutoff ∩ recentKeys y.state = ∅ → cutoff ≤ high + 1 →
        stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
            drift (config := config) x high)
    (g x y : ForkedBeaconState preset) :
    CommonLedger (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  by_cases electra : .pectra ≤ x.fork
  · exact commonLedger_electra hSelected hRelease hLedgerElectra electra
  · intro shared tail high supported twoSlots cutoff apart within
    exact hLedgerPre shared tail high supported twoSlots (Nat.lt_of_not_le electra) cutoff apart
      within

/-- At cutoff zero the common keys are empty, so the common ledger is the state bound. -/
private theorem stateProducer_of_ledger {g x y : ForkedBeaconState preset}
    (ledger : CommonLedger (config := config) (checks := checks) (g := g) (x := x) (y := y)) :
    StateProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) := by
  intro shared tail high supported twoSlots
  have empty : exitedBefore x 0 = ∅ := by simp [exitedBefore]
  have read := ledger shared tail high supported twoSlots 0
    (by rw [empty]; exact Finset.empty_inter _) (Nat.zero_le _)
  simpa [empty, commonSlashed, Models.stake] using read

/-- The headline from the derived envelope and the common ledger, without `ProducerGraph`. -/
private theorem composition_of_ledger
    (ledger : ∀ g x y : ForkedBeaconState preset,
      CommonLedger (config := config) (checks := checks) (g := g) (x := x) (y := y)) :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) := by
  have derived : ∀ g x y : ForkedBeaconState preset,
      DerivedProducer (config := config) (checks := checks) (g := g) (x := x) (y := y) :=
    fun g x _ => derivedProducer_of_state (stateProducer_of_ledger (ledger g x _))
  refine composition_conditional_of_call_ledger derived reducedIdentity ?_ cachedAbsence_proved
    reducedTransfer_proved
  intro g x a b shared left right parameters genesis caps aligned twoSlots earlyA earlyB high
    guard low starts one two lowerOne upperOne lowerTwo upperTwo c absentOne absentTwo
  have selected (call : EitherCall (shared.append left) (shared.append right))
      (lower : low ≤ call.targetEpoch) (upper : call.targetEpoch ≤ high) (cutoff : Nat)
      (cutoffLe : cutoff ≤ high + 1)
      (absent : exitedBefore x cutoff ∩ recentKeys call.state.state = ∅) :
      stateDrift x call.state + 2 * commonSlashed x call.state (exitedBefore x cutoff) ≤
        drift (config := config) x high := by
    cases call with
    | inl call =>
      exact selected_call_commonLedger (ledger g x) shared left parameters genesis
        caps aligned twoSlots earlyA high low guard starts call lower upper cutoff cutoffLe absent
    | inr call =>
      exact selected_call_commonLedger (ledger g x) shared right parameters genesis
        caps aligned twoSlots earlyB high low guard starts call lower upper cutoff cutoffLe absent
  exact ⟨selected one lowerOne upperOne _ ((Nat.min_le_left _ _).trans (by omega)) absentOne,
    selected two lowerTwo upperTwo _ ((Nat.min_le_right _ _).trans (by omega)) absentTwo⟩

/-- The staged headline: both theorems from the four producers still to prove. -/
private theorem headline_staged
    (hSelected : ∀ g x y : ForkedBeaconState preset,
      SelectedInputs (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hRelease : ∀ g x y : ForkedBeaconState preset,
      SelectedReleaseProducer (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hLedgerElectra : ∀ {g x y : ForkedBeaconState preset}
      (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat),
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat →
      ∀ {ledger : RoundLedger tail high} {owned : Ownership}
        {tokens : BLSPubkey → Finset TokenOrigin},
      NewCohortAllocation tail high ledger owned tokens →
      gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high →
      ∀ cutoff, exitedBefore x cutoff ∩ recentKeys y.state = ∅ → cutoff ≤ high + 1 →
        stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
            drift (config := config) x high)
    (hLedgerPre : ∀ {g x y : ForkedBeaconState preset}
      (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat),
      Supported shared tail high → 2 ≤ preset.SLOTS_PER_EPOCH.toNat → x.fork < .pectra →
      ∀ cutoff, exitedBefore x cutoff ∩ recentKeys y.state = ∅ → cutoff ≤ high + 1 →
        stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
          drift (config := config) x high) :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) :=
  composition_of_ledger (commonLedger_proved hSelected hRelease hLedgerElectra hLedgerPre)

end

/-- Before Electra, every ledger cut extends to a rounding ledger.

The penalties come from the pre-Electra penalty producer, and no event pays a pending partial. -/
private theorem LedgerCuts.roundLedger_pre {g x y : ForkedBeaconState preset} {high : Nat}
    {tail : Run config checks x y} (ledger : LedgerCuts tail) (shared : Run config checks g x)
    (supported : Supported shared tail high) (before : x.fork < .pectra)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) :
    ∃ result : RoundLedger tail high, result.toLedgerCuts = ledger := by
  have regime := regime_of_supported shared tail supported
  have yBefore := regime.resolve_left (Nat.not_le_of_gt before)
  obtain ⟨events, replayed⟩ := tail.balanceEvents_ok supported.2.2.2.2.1 high
  have numeric := penaltyProducer_pre before shared tail high supported twoSlots events replayed
  have horizon : ix x y + 1 ≤ driftHorizon x high + 1 := by
    have endpoint := supported.2.2.2.2.2.1
    unfold ix driftHorizon
    omega
  have partials := pre_partial_zero shared tail high supported yBefore replayed
  exact ledger.roundLedger_regime shared supported regime twoSlots replayed
    (numeric.trans (penalties_monotone x high horizon)) (by rw [partials]; exact Nat.zero_le _)

/-- Before Electra, the loss of the new cohort plus its boundary stake fits a sum of five terms.

The first three are the queue budget, the partial budget and the start slack.

The last two are the penalties and the rounding allowance.

The boundary gains of the cohort are added on the right. -/
private theorem NewCohortCuts.loss_boundary_pre {g x y : ForkedBeaconState preset} {high : Nat}
    (shared : Run config checks g x) (tail : Run config checks x y)
    (supported : Supported shared tail high) (ledger : RoundLedger tail high)
    (cohort : NewCohortCuts tail high ledger.toLedgerCuts)
    (unique : PubkeysDistinct y.state) (before : x.fork < .pectra)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (boundarySupported : cohort.boundary ⊆ cohort.supported) :
    (∑ i ∈ cohort.cohort,
      (effectiveAt x i - if i ∈ cohort.supported then effectiveAt y i else 0)) +
      (∑ i ∈ cohort.boundary, effectiveAt y i) ≤
    departureBudgetAt (config := config) x high + duePartialWithdrawals x (driftHorizon x high) +
        startSlack x +
      windowPenalties (config := config) x high (driftHorizon x high + 1) +
          roundingBudget (config := config) x high +
      (∑ i ∈ cohort.boundary, (effectiveAt y i - effectiveAt x i)) := by
  have regime := regime_of_supported shared tail supported
  have yBefore := regime.resolve_left (Nat.not_le_of_gt before)
  have early := supported.2.2.2.2.1
  have endpoint := supported.2.2.2.2.2.1
  have prefixes (i : Nat) : ∃ part,
      (ledger.headRun i).balanceEvents high = .ok part ∧ part <+: events := by
    have replay := replayed
    rw [← ledger.split i] at replay
    exact (ledger.headRun i).balanceEvents_prefix (ledger.suffix i) high events replay
  choose parts reads included using prefixes
  have indices : ∀ i ∈ cohort.cohort, i < x.state.validators.data.size := by
    intro i member
    rw [cohort.exactUniverse, Finset.mem_filter] at member
    exact Finset.mem_range.mp member.1
  have partials := stopped_partial_occurrences shared supported.1 tail early endpoint replayed
    cohort.cohort parts indices (fun i _ => included i)
  have joint := pre_stopped_joint_budget shared tail high supported yBefore replayed
    ledger.stops (cohort.boundary ∪ cohort.departed) cohort.charge (fun i member => by
      obtain ⟨c, chosen, amount⟩ := cohort.actualCharge i member
      obtain ⟨_, v, w, initial, final, active, _, _, inactive⟩ :=
        cohort.charged_cohort unique early member
      exact ⟨c, chosen, amount, ((ledger.stops i).inactive_charge_cutoff chosen
        ⟨v, initial, active⟩ (by simpa only [final, Option.any_some] using inactive)).trans
          endpoint⟩) _ partials
  have debits := cohort.debit_budget_of_penaltyProducer (penaltyProducer_pre before) shared tail
    supported ledger twoSlots replayed parts reads
  have boundarySubset : cohort.boundary ⊆ cohort.cohort := by
    rw [cohort.exactBoundary]
    exact Finset.filter_subset _ _
  have departedSubset : cohort.departed ⊆ cohort.cohort := by
    rw [cohort.exactDeparted]
    exact Finset.sdiff_subset
  have departedIff : ∀ i ∈ cohort.cohort, i ∈ cohort.departed ↔ i ∉ cohort.supported := by
    intro i member
    rw [cohort.exactDeparted, Finset.mem_sdiff]
    exact and_iff_right member
  have arithmetic := new_reference_loss_boundary_le cohort.cohort cohort.supported
    cohort.boundary cohort.departed (effectiveAt x) (effectiveAt y) cohort.charge
    (fun i => (effectiveAt x i - actualBalanceAt x i) +
      ((parts i).map (floorPenaltyDebit i)).sum +
      ((parts i).map (floorPartialDebit (UInt64.ofNat i))).sum +
      (if i ∈ ledger.falling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0))
    boundarySupported boundarySubset departedSubset departedIff
    (fun i member => cohort.stopped_debit_regime shared supported unique regime twoSlots member
      (reads i))
    (fun i member retained notBoundary => cohort.retained_debit_regime shared supported unique
      regime member retained notBoundary (reads i))
  omega

section

open Cryptography.Bls

/-- The endpoint reserve cut, with the epoch of `y` as demand epoch, gives the endpoint demand.

Each recent key that is not previous-only names one supported validator at `y`.

Its gain over the reference weight is paid by its held endpoint tokens. -/
theorem endpointDemand_of_reserveCut {g x y : ForkedBeaconState preset} {high : Nat}
    {suffix : List PendingConsolidation} {o : Ownership}
    (reached : Run config checks g y) (genesis : Genesis (config := config) (checks := checks) g)
    (early : y.fork < .glamsterdam)
    (cut : ReserveCut x high y (getCurrentEpoch y.state) suffix o) :
    EndpointDemand x y o := by
  have unique := reached.pubkeysDistinct genesis
  obtain ⟨_, _, _, _, _, _, _, _, _, supportedPaid⟩ := cut
  intro k member
  obtain ⟨recent, fresh⟩ := Finset.mem_sdiff.mp member
  obtain ⟨either, unslashed⟩ := Finset.mem_filter.mp recent
  obtain ⟨i, v, found, key, activity⟩ : ∃ (i : Nat) (v : Validator),
      y.state.validators.data[i]? = some v ∧ v.pubkey = k ∧
        (isActiveValidator v (getCurrentEpoch y.state) = true ∨
          isActiveValidator v (getCurrentEpoch y.state - 1) = true) := by
    rcases Finset.mem_union.mp either with now | before
    · obtain ⟨i, v, found, key, active⟩ := (mem_keysAt_epoch early _ k).mp now
      exact ⟨i, v, found, key, Or.inl active⟩
    · obtain ⟨i, v, found, key, active⟩ := (mem_keysAt_epoch early _ k).mp before
      exact ⟨i, v, found, key, active_current_or_before_of_active_previous _ v active⟩
  have listed : v ∈ y.state.validators.data.toList := by
    simpa using Array.mem_of_getElem? found
  have clean : v.slashed = false := by
    cases flag : v.slashed
    · rfl
    · exact absurd ⟨v, listed, key, flag⟩ unslashed
  have support : SupportedAt (getCurrentEpoch y.state) v := ⟨clean, by
    rcases activity with now | before
    · exact Or.inl now
    · exact Or.inr before⟩
  have paid := supportedPaid i v found support (key ▸ fresh)
  refine ⟨i, by simp [found, key], ?_⟩
  have weight := effectiveWeight_of_member unique listed
  rw [key] at weight
  rw [weight, ← key]
  have read : effectiveAt y i = v.effectiveBalance.toNat := by simp [effectiveAt, found]
  omega

/-- Take each recent key that is not previous-only.

The endpoint demand chooses as many endpoint tokens held at its own index as its gain.

Tokens held at different indices are different, so the choices are disjoint.

Together they are at most the endpoint tokens. -/
theorem terminalAllocation_of_demand {x y : ForkedBeaconState preset} {o : Ownership}
    (valid : OwnershipValid o) (demand : EndpointDemand x y o) :
    ∃ tokens : BLSPubkey → Finset TokenOrigin, TerminalAllocation x y o tokens := by
  let keys := recentKeys y.state \ previousOnly x
  let gain (k : BLSPubkey) := effectiveWeight y.state k -
    Models.supported (unslashedKeys x.state) (effectiveWeight x.state) k
  have pick (k : BLSPubkey) (member : k ∈ keys) : ∃ i t,
      y.state.validators.data[i]?.any (fun v => v.pubkey == k) ∧
        t ⊆ held o i ∩ o.endpoint ∧ t.card = gain k := by
    obtain ⟨i, named, enough⟩ := demand k member
    obtain ⟨t, inside, card⟩ := Finset.exists_subset_card_eq enough
    exact ⟨i, t, named, inside, card⟩
  let index (k : BLSPubkey) : Nat := if h : k ∈ keys then (pick k h).choose else 0
  let tokens (k : BLSPubkey) : Finset TokenOrigin :=
    if h : k ∈ keys then (pick k h).choose_spec.choose else ∅
  have spec (k : BLSPubkey) (member : k ∈ keys) :
      y.state.validators.data[index k]?.any (fun v => v.pubkey == k) ∧
        tokens k ⊆ held o (index k) ∩ o.endpoint ∧ (tokens k).card = gain k := by
    simp only [index, tokens, member, ↓reduceDIte]
    exact (pick k member).choose_spec.choose_spec
  -- Keys at the same index are the same key, and tokens held at one index have that owner.
  have disjoint (k : BLSPubkey) (kIn : k ∈ keys) (l : BLSPubkey) (lIn : l ∈ keys)
      (different : k ≠ l) : Disjoint (tokens k) (tokens l) := by
    obtain ⟨kNamed, kInside, _⟩ := spec k kIn
    obtain ⟨lNamed, lInside, _⟩ := spec l lIn
    have apart : index k ≠ index l := by
      intro same
      rw [same] at kNamed
      cases found : y.state.validators.data[index l]? with
      | none => simp [found] at kNamed
      | some v =>
        simp only [found, Option.any_some, beq_iff_eq] at kNamed lNamed
        exact different (kNamed.symm.trans lNamed)
    rw [Finset.disjoint_left]
    intro token inK inL
    have ownerK := (Finset.mem_filter.mp (Finset.mem_inter.mp (kInside inK)).1).2
    have ownerL := (Finset.mem_filter.mp (Finset.mem_inter.mp (lInside inL)).1).2
    exact apart (Option.some.inj (ownerK.symm.trans ownerL))
  refine ⟨tokens, ⟨fun k member => ?_, disjoint, ?_⟩⟩
  · obtain ⟨named, inside, card⟩ := spec k member
    exact ⟨fun _ token => (Finset.mem_inter.mp (inside token)).2, index k, named,
      fun _ token => (Finset.mem_inter.mp (inside token)).1, card⟩
  · rw [Finset.sum_inter_add_sum_sdiff]
    have union := Finset.card_biUnion (s := keys) (t := tokens)
      (fun k kIn l lIn different => disjoint k kIn l lIn different)
    rw [← union]
    refine (Finset.card_le_card ?_).trans (Finset.card_le_card valid.2.1)
    intro token member
    obtain ⟨k, kIn, inside⟩ := Finset.mem_biUnion.mp member
    exact (Finset.mem_inter.mp ((spec k kIn).2.1 inside)).2

/-- A new boundary index of the cohort takes its tokens from the terminal allocation.

Its key is active and unslashed at `x`, so it is a reference key and not previous-only.

Its gain is its effective balance at `y` less the one at `x`. -/
private theorem NewCohortCuts.selected_of_terminal {g x y : ForkedBeaconState preset} {high : Nat}
    {tail : Run config checks x y} {ledger : LedgerCuts tail} {o : Ownership}
    {tokens : BLSPubkey → Finset TokenOrigin}
    (cohort : NewCohortCuts tail high ledger) (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (early : y.fork < .glamsterdam)
    (terminal : TerminalAllocation x y o tokens) :
    ∀ i ∈ cohort.boundary, ∃ v, y.state.validators.data[i]? = some v ∧
      tokens v.pubkey ⊆ held o i ∩ o.endpoint ∧
      (tokens v.pubkey).card = effectiveAt y i - effectiveAt x i := by
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have uniqueX := shared.pubkeysDistinct genesis
  have uniqueY := (shared.append tail).pubkeysDistinct genesis
  intro i member
  rw [cohort.exactBoundary] at member
  obtain ⟨inCohort, boundary⟩ := Finset.mem_filter.mp member
  rw [cohort.exactUniverse] at inCohort
  obtain ⟨_, atX, _⟩ := Finset.mem_filter.mp inCohort
  cases xFound : x.state.validators.data[i]? with
  | none => simp [xFound] at atX
  | some w =>
  cases yFound : y.state.validators.data[i]? with
  | none => simp [yFound] at boundary
  | some v =>
  simp only [xFound, yFound, Option.any_some, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_true_eq] at atX boundary
  obtain ⟨⟨active, clean⟩, _⟩ := atX
  obtain ⟨later, laterFound, sameKey⟩ := validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1 xFound
  obtain rfl : later = v := Option.some.inj (laterFound.symm.trans yFound)
  have wListed : w ∈ x.state.validators.data.toList := by
    simpa using Array.mem_of_getElem? xFound
  have activeKey : later.pubkey ∈ activeKeys x.state :=
    (mem_keysAt_epoch xEarly _ _).mpr ⟨i, w, xFound, sameKey.symm, active⟩
  have reference : later.pubkey ∈ unslashedKeys x.state :=
    Finset.mem_filter.mpr ⟨activeKey, sameKey ▸ not_slashedAt uniqueX wListed clean⟩
  have keyIn : later.pubkey ∈ recentKeys y.state \ previousOnly x :=
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp boundary).1,
      fun only => (Finset.mem_sdiff.mp only).2 activeKey⟩
  obtain ⟨_, j, named, inside, card⟩ := terminal.1 _ keyIn
  have same : j = i := by
    cases jFound : y.state.validators.data[j]? with
    | none => simp [jFound] at named
    | some u =>
      simp only [jFound, Option.any_some, beq_iff_eq] at named
      exact uniqueY.index_eq jFound yFound named
  rw [same] at inside
  refine ⟨later, rfl, Finset.subset_inter inside (terminal.1 _ keyIn).1, ?_⟩
  rw [card]
  have weightY := effectiveWeight_of_member uniqueY (by simpa using Array.mem_of_getElem? yFound)
  have weightX := effectiveWeight_of_member uniqueX wListed
  have supportedX : Models.supported (unslashedKeys x.state) (effectiveWeight x.state)
      later.pubkey = effectiveWeight x.state later.pubkey := by
    simp [Models.supported, reference]
  rw [supportedX, weightY, sameKey, weightX]
  simp [effectiveAt, xFound, yFound]

/-- From Electra, the new cohort allocation for any terminal allocation.

Every producer premise here is proved. -/
theorem newCohortAllocation_electra {g x y : ForkedBeaconState preset}
    {o : Ownership} {tokens : BLSPubkey → Finset TokenOrigin}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (events : List (BalanceEvent preset))
    (replayed : tail.balanceEvents high = .ok events) (ledger : RoundLedger tail high)
    (terminal : TerminalAllocation x y o tokens) :
    Nonempty (NewCohortAllocation tail high ledger o tokens) := by
  have support := supported
  obtain ⟨genesis, parameters, caps, aligned, early, endpoint, guard⟩ := supported
  have uniqueY := (shared.append tail).pubkeysDistinct genesis
  have startEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  obtain ⟨cohort⟩ := NewCohortCuts.exists tail ledger.toLedgerCuts high uniqueY early twoSlots
    endpoint
  have unit := ceiling_unit_of_guard shared genesis aligned startEarly electra guard
  obtain ⟨_, _, allocation, _⟩ := cohort.allocation_electra_of_ceiling penaltyProducer_proved
    shared tail support ledger uniqueY electra twoSlots unit
    (fun head headEarly within found read => otherCredit_le_allowance_electra shared genesis
      head caps aligned electra headEarly twoSlots high within guard read)
    (fun head headEarly before total read => floor_all_runs_electra shared genesis parameters
      caps aligned guard electra twoSlots head headEarly (by omega) total read)
    replayed o tokens (cohort.selected_of_terminal shared genesis early terminal)
  exact ⟨allocation⟩

/-- Releases of initial tags have baseline zero.

So all allocations release what the fresh ones do. -/
private theorem fresh_baseline_eq {tagged : List (TaggedEntry × Payment preset)}
    {allocations : List OwnedRelease}
    (paired : List.Forall₂ (fun pair allocation => match pair.1.tag with
      | .initial _ => allocation.baseline = 0
      | .fresh _ => allocation.baseline ≤ pair.1.amount + allocation.sourceRound)
      tagged allocations) :
    (allocations.map (·.baseline)).sum =
      ((((tagged.zip allocations).filter fun pair =>
        pair.1.1.tag.isFresh).map Prod.snd).map
          (·.baseline)).sum := by
  induction paired with
  | nil => rfl
  | @cons pair allocation tagged allocations head _ ih =>
    cases tagEq : pair.1.tag with
    | initial n =>
      rw [tagEq] at head
      simp only [List.zip_cons_cons, List.filter_cons, tagEq, List.map_cons, List.sum_cons, head,
        ih]
      simp
    | fresh n =>
      simp only [List.zip_cons_cons, List.filter_cons, tagEq, List.map_cons, List.sum_cons, ih]
      simp

/-- One event's credit bound is within its deposit, reward, sync and other credits. -/
private theorem ownedCreditBound_le (e : BalanceEvent preset) :
    ownedCreditBound e ≤ funding_deposit_credit e +
      (if e.source = .rewards then e.creditLimit else 0) +
      (if e.source = .sync then e.creditLimit else 0) + otherCredit e := by
  unfold ownedCreditBound
  by_cases deposit : e.source = .deposits
  · simp only [deposit, ↓reduceIte]
    omega
  · by_cases reward : e.source = .rewards
    · simp [reward]
      omega
    · by_cases sync : e.source = .sync
      · simp [sync]
        omega
      · simp only [deposit, reward, sync, or_self, ↓reduceIte]
        omega

/-- The four ownership-count conjuncts of `CumulativeFunding`.

They are for the fresh allocations of the replay from `x` to `y`. -/
theorem ownership_counts {x y : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {events : List (BalanceEvent preset)}
    {queue final : List TaggedEntry} {allPayments : List (TaggedEntry × Payment preset)}
    {allAllocations : List OwnedRelease} {calls : List (IndexedDepartureCall preset config)}
    {before after : Ownership}
    (initial : OwnedInitial x high before)
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0 events queue final
      allPayments allAllocations calls before after) :
    let fresh := (allPayments.zip allAllocations).filter fun pair =>
      pair.1.1.tag.isFresh
    let initialT := after.issued.filter (·.isInitial)
    let credits := after.issued.filter (·.isCredit)
    let releases := after.issued.filter (·.isReleased)
    initialT = before.issued ∧
      credits.card ≤ (events.map funding_deposit_credit).sum +
        sourceCredits .rewards events + sourceCredits .sync events + (events.map otherCredit).sum ∧
      releases.card = ((fresh.map Prod.snd).map (·.baseline)).sum ∧
      after.issued.card = initialT.card + credits.card + releases.card := by
  intro fresh initialT credits releases
  obtain ⟨_, initialEq, creditLe, releasedEq⟩ := history.counters_original.1 initial.counters
  -- Every token at `x` is an initial token.
  have origins := initial.2.2.2.1
  have allInitial : before.issued.filter
      ((·.isInitial)) = before.issued :=
    Finset.filter_true_of_mem fun t member => by
      obtain ⟨pot, index, unit, rfl, _⟩ := origins t member
      rfl
  have noCredit : before.issued.filter
      ((·.isCredit)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun t member => by
      obtain ⟨pot, index, unit, rfl, _⟩ := origins t member
      simp
  have noRelease : before.issued.filter
      ((·.isReleased)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun t member => by
      obtain ⟨pot, index, unit, rfl, _⟩ := origins t member
      simp
  rw [allInitial] at initialEq
  rw [noCredit, Finset.card_empty, Nat.zero_add] at creditLe
  rw [noRelease, Finset.card_empty, Nat.zero_add] at releasedEq
  refine ⟨initialEq, ?_, releasedEq.trans (fresh_baseline_eq history.paired_baselines), ?_⟩
  · refine creditLe.trans ((List.sum_le_sum fun e _ => ownedCreditBound_le e).trans ?_)
    simp only [sourceCredits, List.sum_map_add]
    exact Nat.le_refl _
  · -- Each token is of exactly one kind.
    rw [Finset.card_eq_sum_ones, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    cases t <;> simp

/-- The scheduled allocation of a tail, read off its two ends.

The scheduled keys are the unslashed keys active at `x` with an exit assigned within the horizon.

Each keeps its key along the tail, and a recent key at `y` is unslashed there.

Their effective balances at `x` are part of the scheduled departures `scheduledExitStake`. -/
theorem ScheduledAllocation.ofReads {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : Nat) : Nonempty (ScheduledAllocation x y high) := by
  have kept := (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1
  let scheduled := (Finset.range x.state.validators.data.size).filter fun i =>
    (x.state.validators.data[i]?).any (fun v =>
      isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
        decide (v.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.exitEpoch.toNat ≤ horizonEnd x high))
  -- Each scheduled index has its validator at `x` and, with the same key, at `y`.
  have reads : ∀ i ∈ scheduled, ∃ initial v, x.state.validators.data[i]? = some initial ∧
      y.state.validators.data[i]? = some v ∧ initial.pubkey = v.pubkey ∧
      (v.pubkey ∈ recentKeys y.state → v.slashed = false) := by
    intro i member
    obtain ⟨range, _⟩ := Finset.mem_filter.mp member
    obtain ⟨initial, found⟩ : ∃ initial, x.state.validators.data[i]? = some initial :=
      ⟨_, Array.getElem?_eq_getElem (Finset.mem_range.mp range)⟩
    obtain ⟨v, located, key⟩ := validators_getElem?_of_validatorKeys_prefix kept found
    refine ⟨initial, v, found, located, key.symm, fun recent => ?_⟩
    have unslashed := (Finset.mem_filter.mp recent).2
    cases flag : v.slashed
    · rfl
    · exact absurd ⟨v, by simpa using Array.mem_of_getElem? located, rfl, flag⟩ unslashed
  refine ⟨⟨scheduled, rfl,
    fun i => ((y.state.validators.data[i]?).map fun v => if v.slashed then 0 else
      effectiveAt x i - (if v.pubkey ∈ recentKeys y.state then effectiveAt y i else 0)).getD 0,
    fun i => ((y.state.validators.data[i]?).map fun v =>
      if v.pubkey ∈ recentKeys y.state \ activeKeys y.state then
        min (effectiveAt y i - effectiveAt x i) (effectiveAt x i) else 0).getD 0,
    fun i => ((x.state.validators.data[i]?).bind fun initial =>
      (y.state.validators.data[i]?).map fun v =>
        if v.slashed ∧ initial.pubkey ∉ recentKeys y.state then effectiveAt x i else 0).getD 0,
    fun i _ v found => by simp [found],
    fun i _ v found => by simp [found],
    fun i _ v initial initialAt found => by simp [initialAt, found],
    reads, ?_⟩⟩
  -- `scheduledExitStake` counts the scheduled indices with their effective balances.
  unfold scheduledExitStake
  rw [list_map_sum_range x.state.validators.data.toList _, Array.length_toList]
  refine (Finset.sum_le_sum fun i member => ?_).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _) fun _ _ _ => Nat.zero_le _)
  obtain ⟨_, within⟩ := Finset.mem_filter.mp member
  cases found : x.state.validators.data[i]? with
  | none => simp [effectiveAt, found]
  | some v =>
    simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_true_eq] at within
    obtain ⟨⟨active, _⟩, _, before⟩ := within
    simp [Array.getElem?_toList, found, active, effectiveAt, before]

/-- The positions of the unslashed validators active at the current epoch. -/
private def unslashedIndices {fork : Fork} (s : BeaconState preset fork) : Finset Nat :=
  (Finset.range s.validators.data.size).filter fun i =>
    (s.validators.data[i]?).any (fun v => isActiveValidator v (getCurrentEpoch s) && !v.slashed)

/-- With distinct keys, a sum over the unslashed keys is a sum over their positions. -/
private theorem unslashed_sum_indices {fork : Fork} {s : BeaconState preset fork}
    (unique : PubkeysDistinct s) (early : fork < .glamsterdam) (F : BLSPubkey → Nat) :
    ∑ k ∈ unslashedKeys s, F k = ∑ i ∈ unslashedIndices s, F (keyAt s i) := by
  have distinct : (s.validators.data.toList.map (·.pubkey)).Nodup := unique
  have image : unslashedKeys s = (unslashedIndices s).image (keyAt s) := by
    ext k
    simp only [unslashedKeys, Finset.mem_filter, Finset.mem_image, unslashedIndices,
      Finset.mem_range, activeKeys]
    constructor
    · rintro ⟨active, clean⟩
      obtain ⟨i, v, found, key, isActive⟩ := (mem_keysAt_epoch early _ k).mp active
      have unslashed : v.slashed = false := by
        cases flag : v.slashed
        · rfl
        · exact absurd ⟨v, by simpa using Array.mem_of_getElem? found, key, flag⟩ clean
      refine ⟨i, ⟨(Array.getElem?_eq_some_iff.mp found).1, ?_⟩, ?_⟩
      · simp [found, isActive, unslashed]
      · simp [keyAt, found, key]
    · rintro ⟨i, ⟨_, within⟩, rfl⟩
      cases found : s.validators.data[i]? with
      | none => simp [found] at within
      | some v =>
        simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at within
        have key : keyAt s i = v.pubkey := by simp [keyAt, found]
        rw [key]
        refine ⟨(mem_keysAt_epoch early _ _).mpr ⟨i, v, found, rfl, within.1⟩, ?_⟩
        exact not_slashedAt unique (by simpa using Array.mem_of_getElem? found) within.2
  have injective : Set.InjOn (keyAt s) (unslashedIndices s) := by
    intro i member j other same
    obtain ⟨range, _⟩ := Finset.mem_filter.mp member
    obtain ⟨rangeJ, _⟩ := Finset.mem_filter.mp other
    have foundI := Array.getElem?_eq_getElem (Finset.mem_range.mp range)
    have foundJ := Array.getElem?_eq_getElem (Finset.mem_range.mp rangeJ)
    simp only [keyAt, foundI, foundJ, Option.map_some, Option.getD_some] at same
    have nodup := List.Nodup.getElem_inj_iff distinct
      (i := i) (j := j) (hi := by simpa using Finset.mem_range.mp range)
      (hj := by simpa using Finset.mem_range.mp rangeJ)
    exact nodup.mp (by simpa using same)
  rw [image, Finset.sum_image injective]

/-- What a position of an unslashed key at `x` reads at `x` and at `y`.

Keys stay at their positions along the tail.

With distinct keys, a key's weight and slashed flag are those of its position. -/
private theorem unslashedIndex_reads {x y : ForkedBeaconState preset}
    (kept : validatorKeys x.state <+: validatorKeys y.state)
    (uniqueX : PubkeysDistinct x.state) (uniqueY : PubkeysDistinct y.state)
    {i : Nat} (member : i ∈ unslashedIndices x.state) :
    ∃ v w, x.state.validators.data[i]? = some v ∧ y.state.validators.data[i]? = some w ∧
      keyAt x.state i = v.pubkey ∧ w.pubkey = v.pubkey ∧
      isActiveValidator v (getCurrentEpoch x.state) = true ∧ v.slashed = false ∧
      effectiveWeight x.state (keyAt x.state i) = effectiveAt x i ∧
      effectiveWeight y.state (keyAt x.state i) = effectiveAt y i ∧
      (SlashedAt y.state (keyAt x.state i) ↔ w.slashed = true) := by
  have distinctY : (y.state.validators.data.toList.map (·.pubkey)).Nodup := uniqueY
  obtain ⟨range, within⟩ := Finset.mem_filter.mp member
  obtain ⟨v, found⟩ : ∃ v, x.state.validators.data[i]? = some v :=
    ⟨_, Array.getElem?_eq_getElem (Finset.mem_range.mp range)⟩
  obtain ⟨w, located, key⟩ := validators_getElem?_of_validatorKeys_prefix kept found
  have keyed : keyAt x.state i = v.pubkey := by simp [keyAt, found]
  simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at within
  have wListed : w ∈ y.state.validators.data.toList := by
    simpa using Array.mem_of_getElem? located
  refine ⟨v, w, found, located, keyed, key, within.1, within.2, ?_, ?_, ?_⟩
  · rw [keyed, effectiveWeight_of_member uniqueX (by simpa using Array.mem_of_getElem? found)]
    simp [effectiveAt, found]
  · rw [keyed, ← key, effectiveWeight_of_member uniqueY wListed]
    simp [effectiveAt, located]
  · rw [keyed]
    constructor
    · rintro ⟨u, listed, uKey, flag⟩
      have same : u = w := List.inj_on_of_nodup_map distinctY listed wListed (uKey.trans key.symm)
      exact same ▸ flag
    · intro flag
      exact ⟨w, wListed, key, flag⟩

/-- Take a key that is recent but not active at `y`.

It is the key of a validator whose exit is the current epoch of `y`.

It was active at the previous epoch and is not at the current one. -/
private theorem boundary_exit {fork : Fork} {y : BeaconState preset fork}
    (uniqueY : PubkeysDistinct y) (early : fork < .glamsterdam)
    {i : Nat} {w : Validator} (located : y.validators.data[i]? = some w)
    (boundary : w.pubkey ∈ recentKeys y \ activeKeys y) :
    w.exitEpoch = getCurrentEpoch y := by
  have distinctY : (y.validators.data.toList.map (·.pubkey)).Nodup := uniqueY
  have wListed : w ∈ y.validators.data.toList := by simpa using Array.mem_of_getElem? located
  obtain ⟨recent, notActive⟩ := Finset.mem_sdiff.mp boundary
  have notNow : isActiveValidator w (getCurrentEpoch y) = false := by
    cases now : isActiveValidator w (getCurrentEpoch y)
    · rfl
    · exact absurd ((mem_keysAt_epoch early _ _).mpr ⟨i, w, located, rfl, now⟩) notActive
  have before : isActiveValidator w (getPreviousEpoch y) = true := by
    have inUnion := (Finset.mem_filter.mp recent).1
    rcases Finset.mem_union.mp inUnion with active | previous
    · exact absurd active notActive
    · obtain ⟨j, u, uFound, uKey, uActive⟩ := (mem_keysAt_epoch early _ _).mp previous
      have uListed : u ∈ y.validators.data.toList := by
        simpa using Array.mem_of_getElem? uFound
      obtain rfl := List.inj_on_of_nodup_map distinctY uListed wListed uKey
      exact uActive
  have previousNat := getPreviousEpoch_toNat y
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, Nat.not_le,
    Nat.not_lt] at notNow before
  apply UInt64.toNat_inj.mp
  omega

/-- This is the core of the a priori ledger.

The state drift and twice the common reserve of the scheduled keys fit the drift.

The reference loss splits into the scheduled keys' losses and the new cohort's.

The reference gain splits into the previous-only keys and the gain outside them.

The boundary splits into four parts.

The first two are the scheduled keys exiting at `y` and the new cohort's boundary.

The last two are the previous-only keys and the new nonreference keys.

Each part is paid by its own term of the drift.

The terms are the scheduled reserve `scheduledExitStake` and the new cohort's budgets.

They also include the old boundary `previousOnlyStake + 2 adjacentExitStake`.

They include the scheduled growth `exitCohortGrowth` as well.

The last two are the gain budget and the nonreference maximum. -/
private theorem stateDrift_scheduledReserve_le {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {high : Nat} {ledger : LedgerCuts tail}
    (uniqueX : PubkeysDistinct x.state) (uniqueY : PubkeysDistinct y.state)
    (early : y.fork < .glamsterdam) (guard : aprioriGuardAt config x high)
    (cuts : NewCohortCuts tail high ledger)
    (lossBoundary : (∑ i ∈ cuts.cohort,
        (effectiveAt x i - if i ∈ cuts.supported then effectiveAt y i else 0)) +
      (∑ i ∈ cuts.boundary, effectiveAt y i) ≤
      departureBudgetAt (config := config) x high + duePartialWithdrawals x (driftHorizon x high) +
          startSlack x +
        windowPenalties (config := config) x high (driftHorizon x high + 1) +
            roundingBudget (config := config) x high +
        (∑ i ∈ cuts.boundary, (effectiveAt y i - effectiveAt x i)))
    (sched : ScheduledAllocation x y high)
    (funded : gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high)
    (rhat : (∑ i ∈ Finset.range x.state.validators.data.size,
        if (x.state.validators.data[i]?).any (fun v =>
            isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
            decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
        then effectiveAt y i - 2 * effectiveAt x i else 0) ≤ exitCohortGrowth x high)
    (old : 3 * Models.stake (effectiveWeight y.state) (recentKeys y.state ∩ previousOnly x) +
      2 * (∑ i ∈ Finset.range x.state.validators.data.size,
        if (x.state.validators.data[i]?).any (fun v =>
            isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
            decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
        then effectiveAt x i else 0) ≤ previousOnlyStake x + 2 *
          adjacentExitStake x (driftHorizon x high)) :
    stateDrift x y + 2 * ∑ i ∈ sched.scheduled, sched.commonReserve i ≤
      drift (config := config) x high := by
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have kept := (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1
  have life := tail.registryLifecycle
  let U := unslashedKeys x.state
  let I := unslashedIndices x.state
  let Y := (getCurrentEpoch y.state).toNat
  -- Positions with an exit assigned within the horizon are the scheduled ones.
  let p : Nat → Prop := fun i => (x.state.validators.data[i]?).any (fun v =>
    decide (v.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.exitEpoch.toNat ≤ horizonEnd x high))
  have scheduledSplit : I.filter p = sched.scheduled := by
    ext i
    simp only [Finset.mem_filter, I, unslashedIndices, p, sched.exactScheduled]
    cases x.state.validators.data[i]? <;> simp [and_assoc]
  -- The other unslashed positions form the new cohort, with its slashed keys at `y` removed.
  have cohortSub : cuts.cohort ⊆ I.filter (¬ p ·) := by
    intro i member
    rw [cuts.exactUniverse, Finset.mem_filter] at member
    obtain ⟨range, first, _⟩ := member
    simp only [Finset.mem_filter, I, unslashedIndices, p]
    cases found : x.state.validators.data[i]? with
    | none => simp [found] at first
    | some v =>
      simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_true_eq] at first ⊢
      refine ⟨⟨range, first.1.1, first.1.2⟩, ?_⟩
      rcases first.2 with far | late
      · simp [far]
      · intro ⟨_, before⟩
        omega
  have cohortIff : ∀ i ∈ I.filter (¬ p ·), i ∈ cuts.cohort ↔
      (y.state.validators.data[i]?).any (fun w => !w.slashed) := by
    intro i member
    obtain ⟨inI, notP⟩ := Finset.mem_filter.mp member
    obtain ⟨range, within⟩ := Finset.mem_filter.mp inI
    rw [cuts.exactUniverse, Finset.mem_filter]
    simp only [range, true_and]
    constructor
    · exact fun h => h.2
    · intro clean
      refine ⟨?_, clean⟩
      cases found : x.state.validators.data[i]? with
      | none => simp [found] at within
      | some v =>
        simp only [found, Option.any_some, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_true_eq, p] at within notP ⊢
        refine ⟨within, ?_⟩
        by_cases far : v.exitEpoch = FAR_FUTURE_EPOCH
        · exact Or.inl far
        · exact Or.inr (by by_contra small; exact notP ⟨far, by omega⟩)
  -- The reference loss.
  have loss : referenceLoss x y = (∑ i ∈ sched.scheduled, sched.loss i) +
      ∑ i ∈ cuts.cohort, (effectiveAt x i - if i ∈ cuts.supported then effectiveAt y i else 0) := by
    unfold referenceLoss
    rw [Finset.sum_filter, unslashed_sum_indices uniqueX xEarly,
      ← Finset.sum_filter_add_sum_filter_not I p, scheduledSplit]
    congr 1
    · refine Finset.sum_congr rfl fun i member => ?_
      have inI : i ∈ I := by
        rw [← scheduledSplit] at member
        exact (Finset.mem_filter.mp member).1
      obtain ⟨v, w, _, located, keyed, key, _, _, wx, wy, slashed⟩ :=
        unslashedIndex_reads kept uniqueX uniqueY inI
      have same : keyAt x.state i = w.pubkey := keyed.trans key.symm
      rw [sched.exactLoss i member w located]
      by_cases flag : w.slashed = true
      · simp [slashed.mpr flag, flag]
      · have notSlashed : ¬ SlashedAt y.state (keyAt x.state i) := fun h => flag (slashed.mp h)
        rw [ite_eq_left_of_eq_true _ _ (eq_true notSlashed),
          ite_eq_right_of_eq_false _ _ (eq_false flag)]
        unfold Models.supported
        rw [wx, wy, same]
    · rw [← Finset.sum_subset cohortSub ?_]
      · refine Finset.sum_congr rfl fun i member => ?_
        have inI := (Finset.mem_filter.mp (cohortSub member)).1
        obtain ⟨v, w, _, located, keyed, key, _, _, wx, wy, slashed⟩ :=
          unslashedIndex_reads kept uniqueX uniqueY inI
        have clean : w.slashed = false := by
          have := (cohortIff i (cohortSub member)).mp member
          simpa [located] using this
        have notSlashed : ¬ SlashedAt y.state (keyAt x.state i) := fun h => by
          simp [slashed.mp h] at clean
        have supportedIff : i ∈ cuts.supported ↔ keyAt x.state i ∈ recentKeys y.state := by
          rw [cuts.exactSupported, Finset.mem_filter, keyed, ← key]
          simp [member, located]
        rw [ite_eq_left_of_eq_true _ _ (eq_true notSlashed)]
        unfold Models.supported
        rw [wx]
        by_cases recent : keyAt x.state i ∈ recentKeys y.state
        · rw [ite_eq_left_of_eq_true _ _ (eq_true recent),
            ite_eq_left_of_eq_true _ _ (eq_true (supportedIff.mpr recent)), wy]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false recent),
            ite_eq_right_of_eq_false _ _ (eq_false (mt supportedIff.mp recent))]
      -- A position outside the new cohort is slashed at `y`.
      · intro i member outside
        obtain ⟨inI, _⟩ := Finset.mem_filter.mp member
        obtain ⟨v, w, _, located, _, _, _, _, _, _, slashed⟩ :=
          unslashedIndex_reads kept uniqueX uniqueY inI
        have flag : w.slashed = true := by
          by_contra clean
          exact outside ((cohortIff i member).mpr (by simp [located, clean]))
        exact ite_eq_right_of_eq_false _ _ (eq_false (not_not.mpr (slashed.mpr flag)))
  -- The reference gain: the previous-only keys, and the gain outside them.
  have gain : referenceGain x y ≤
      Models.stake (effectiveWeight y.state) (recentKeys y.state ∩ previousOnly x) +
        gainWithoutPreviousOnly x y := by
    unfold referenceGain gainWithoutPreviousOnly Models.stake
    rw [← Finset.sum_inter_add_sum_sdiff (recentKeys y.state) (previousOnly x)]
    exact Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Nat.sub_le _ _) _
  -- The boundary: previous-only keys, new nonreference keys and the unslashed keys of `x`.
  have boundarySplit : boundaryStake y ≤
      Models.stake (effectiveWeight y.state) (recentKeys y.state ∩ previousOnly x) +
      Models.stake (effectiveWeight y.state) (newBoundary x y) +
      ∑ k ∈ unslashedKeys x.state,
        (if k ∈ recentKeys y.state \ activeKeys y.state then effectiveWeight y.state k else 0) := by
    unfold boundaryStake Models.stake
    rw [← Finset.sum_inter_add_sum_sdiff (recentKeys y.state \ activeKeys y.state) (previousOnly x),
      ← Finset.sum_inter_add_sum_sdiff ((recentKeys y.state \ activeKeys y.state) \ previousOnly x)
        (unslashedKeys x.state)]
    have newSame : ((recentKeys y.state \ activeKeys y.state) \ previousOnly x) \
        unslashedKeys x.state = newBoundary x y := by
      unfold newBoundary
      ext k
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    rw [newSame, Finset.sum_ite_mem]
    have one : ∑ k ∈ (recentKeys y.state \ activeKeys y.state) ∩ previousOnly x,
        effectiveWeight y.state k ≤
        ∑ k ∈ recentKeys y.state ∩ previousOnly x, effectiveWeight y.state k :=
      Finset.sum_le_sum_of_subset fun k member => by
        simp only [Finset.mem_inter, Finset.mem_sdiff] at member ⊢
        exact ⟨member.1.1, member.2⟩
    have two : ∑ k ∈ ((recentKeys y.state \ activeKeys y.state) \ previousOnly x) ∩
        unslashedKeys x.state, effectiveWeight y.state k ≤
        ∑ k ∈ unslashedKeys x.state ∩ (recentKeys y.state \ activeKeys y.state),
          effectiveWeight y.state k :=
      Finset.sum_le_sum_of_subset fun k member => by
        simp only [Finset.mem_inter, Finset.mem_sdiff] at member ⊢
        exact ⟨member.2, member.1.1⟩
    omega
  -- The unslashed keys of `x` at the boundary of `y` form two parts.
  --
  -- They are the scheduled keys exiting at `y`, and the new cohort's boundary.
  have indexSplit : ∑ k ∈ unslashedKeys x.state,
      (if k ∈ recentKeys y.state \ activeKeys y.state then effectiveWeight y.state k else 0) ≤
      (∑ i ∈ Finset.range x.state.validators.data.size,
        if (x.state.validators.data[i]?).any (fun v =>
          isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
        then effectiveAt x i else 0) +
      (∑ i ∈ sched.scheduled, sched.growth i) +
      (∑ i ∈ Finset.range x.state.validators.data.size,
        if (x.state.validators.data[i]?).any (fun v =>
          isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
        then effectiveAt y i - 2 * effectiveAt x i else 0) +
      ∑ i ∈ cuts.boundary, effectiveAt y i := by
    rw [unslashed_sum_indices uniqueX xEarly, ← Finset.sum_filter_add_sum_filter_not I p,
      scheduledSplit]
    -- A scheduled key at the boundary of `y` exits there, by its assigned exit.
    have scheduledPart : ∑ i ∈ sched.scheduled,
        (if keyAt x.state i ∈ recentKeys y.state \ activeKeys y.state then
          effectiveWeight y.state (keyAt x.state i) else 0) ≤
        ∑ i ∈ sched.scheduled, ((if (x.state.validators.data[i]?).any (fun v =>
          isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
          then effectiveAt x i else 0) + sched.growth i +
          (if (x.state.validators.data[i]?).any (fun v =>
          isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
          then effectiveAt y i - 2 * effectiveAt x i else 0)) := by
      refine Finset.sum_le_sum fun i member => ?_
      have inI : i ∈ I := by
        rw [← scheduledSplit] at member
        exact (Finset.mem_filter.mp member).1
      obtain ⟨v, w, found, located, keyed, key, active, unslashed, wx, wy, _⟩ :=
        unslashedIndex_reads kept uniqueX uniqueY inI
      have same : keyAt x.state i = w.pubkey := keyed.trans key.symm
      by_cases boundary : keyAt x.state i ∈ recentKeys y.state \ activeKeys y.state
      · rw [ite_eq_left_of_eq_true _ _ (eq_true boundary), wy]
        have assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH := by
          have scheduled := member
          rw [sched.exactScheduled, Finset.mem_filter] at scheduled
          simp only [found, Option.any_some, Bool.and_eq_true, decide_eq_true_eq] at scheduled
          exact scheduled.2.2.1
        obtain ⟨later, read, epochs⟩ := life.validators i v found
        obtain rfl := Option.some.inj (read.symm.trans located)
        have exitNow := boundary_exit uniqueY early located (same ▸ boundary)
        have exitNat : v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat := by
          rw [← epochs.exitEpoch assigned, exitNow]
        have guardTrue : (x.state.validators.data[i]?).any (fun v =>
            isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
            decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat)) = true := by
          simp [found, active, unslashed, exitNat]
        rw [ite_eq_left_of_eq_true _ _ (eq_true guardTrue),
          ite_eq_left_of_eq_true _ _ (eq_true guardTrue),
          sched.exactGrowth i member later located,
          ite_eq_left_of_eq_true _ _ (eq_true (same ▸ boundary))]
        omega
      · rw [ite_eq_right_of_eq_false _ _ (eq_false boundary)]
        exact Nat.zero_le _
    have scheduledRange : sched.scheduled ⊆ Finset.range x.state.validators.data.size := by
      rw [sched.exactScheduled]
      exact Finset.filter_subset _ _
    have lowO := Finset.sum_le_sum_of_subset (f := fun i =>
      if (x.state.validators.data[i]?).any (fun v =>
          isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
      then effectiveAt x i else 0) scheduledRange
    have lowR := Finset.sum_le_sum_of_subset (f := fun i =>
      if (x.state.validators.data[i]?).any (fun v =>
          isActiveValidator v (getCurrentEpoch x.state) && !v.slashed &&
          decide (v.exitEpoch.toNat = (getCurrentEpoch y.state).toNat))
      then effectiveAt y i - 2 * effectiveAt x i else 0) scheduledRange
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at scheduledPart
    -- An unscheduled unslashed key at the boundary of `y` is in the new cohort's boundary.
    have cohortPart : ∑ i ∈ I.filter (¬ p ·),
        (if keyAt x.state i ∈ recentKeys y.state \ activeKeys y.state then
          effectiveWeight y.state (keyAt x.state i) else 0) ≤
        ∑ i ∈ cuts.boundary, effectiveAt y i := by
      calc _ ≤ ∑ i ∈ I.filter (¬ p ·),
            (if i ∈ cuts.boundary then effectiveAt y i else 0) := by
            refine Finset.sum_le_sum fun i member => ?_
            have inI := (Finset.mem_filter.mp member).1
            obtain ⟨v, w, _, located, keyed, key, _, _, _, wy, slashed⟩ :=
              unslashedIndex_reads kept uniqueX uniqueY inI
            have same : keyAt x.state i = w.pubkey := keyed.trans key.symm
            by_cases boundary : keyAt x.state i ∈ recentKeys y.state \ activeKeys y.state
            · have wBoundary : w.pubkey ∈ recentKeys y.state \ activeKeys y.state :=
                same ▸ boundary
              have clean : w.slashed = false := by
                have notSlashed := (Finset.mem_filter.mp (Finset.mem_sdiff.mp wBoundary).1).2
                rw [same] at slashed
                cases flag : w.slashed
                · rfl
                · exact absurd (slashed.mpr flag) notSlashed
              have inCohort := (cohortIff i member).mpr (by simp [located, clean])
              have inBoundary : i ∈ cuts.boundary := by
                rw [cuts.exactBoundary]
                exact Finset.mem_filter.mpr ⟨inCohort,
                  by simpa [located] using Finset.mem_sdiff.mp wBoundary⟩
              rw [ite_eq_left_of_eq_true _ _ (eq_true boundary), wy,
                ite_eq_left_of_eq_true _ _ (eq_true inBoundary)]
            · rw [ite_eq_right_of_eq_false _ _ (eq_false boundary)]
              exact Nat.zero_le _
        _ = ∑ i ∈ I.filter (¬ p ·) ∩ cuts.boundary, effectiveAt y i := Finset.sum_ite_mem _ _ _
        _ ≤ ∑ i ∈ cuts.boundary, effectiveAt y i :=
            Finset.sum_le_sum_of_subset Finset.inter_subset_right
    omega
  have reservation := sched.reservation_bound
  have nonreference := nonreference_boundary_le (config := config) cuts uniqueX uniqueY early funded
  unfold stateDrift
  rw [loss]
  simp only [drift, guard, ↓reduceIte]
  omega

/-- The boundary keys of the new cohort are recent at the end of the tail. -/
private theorem NewCohortCuts.boundary_supported {x y : ForkedBeaconState preset}
    {tail : Run config checks x y} {high : Nat} {ledger : LedgerCuts tail}
    (cuts : NewCohortCuts tail high ledger) : cuts.boundary ⊆ cuts.supported := by
  intro i member
  rw [cuts.exactBoundary, Finset.mem_filter] at member
  rw [cuts.exactSupported, Finset.mem_filter]
  obtain ⟨inCohort, onKey⟩ := member
  refine ⟨inCohort, ?_⟩
  cases found : y.state.validators.data[i]? with
  | none => simp [found] at onKey
  | some w =>
    simp only [found, Option.any_some, decide_eq_true_eq, Finset.mem_sdiff] at onKey ⊢
    exact onKey.1

/-- Under the guard, a cutoff within the horizon is below the far future.

The guard keeps the horizon below half the slashings vector.

An epoch is at most half the slots. -/
private theorem cutoff_le_farFuture {x : ForkedBeaconState preset} {high cutoff : Nat}
    (guard : aprioriGuardAt config x high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (within : cutoff ≤ high + 1) : cutoff ≤ FAR_FUTURE_EPOCH.toNat := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, short, _⟩ := id guard
  change high + 2 - (getCurrentEpoch x.state).toNat + 2 <
    preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 at short
  have slotEpoch := getCurrentEpoch_toNat x.state
  have half : x.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ x.state.slot.toNat / 2 :=
    Nat.div_le_div_left twoSlots (by decide)
  have slotBound := x.state.slot.toNat_lt
  have vectorBound := preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat_lt
  have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  omega

/-- The common ledger from the new cohort's loss and boundary bound and the gain funding.

The scheduled allocation is read off the two ends.

The scheduled boundary at the end of the tail is bounded by `exitCohortGrowth`.

The old boundary is bounded by `previousOnlyStake + 2 adjacentExitStake`.

The slashed common stake is paid from the common reserve of the scheduled keys.

The cutoff is below the far future.

That matters: past it `exitedBefore` would admit keys with no exit.

The scheduled reserve does not hold such keys.

The guard excludes it (`cutoff_le_farFuture`). -/
private theorem commonLedger_of_cuts {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    {ledger : LedgerCuts tail} (cuts : NewCohortCuts tail high ledger)
    (lossBoundary : (∑ i ∈ cuts.cohort,
        (effectiveAt x i - if i ∈ cuts.supported then effectiveAt y i else 0)) +
      (∑ i ∈ cuts.boundary, effectiveAt y i) ≤
      departureBudgetAt (config := config) x high + duePartialWithdrawals x (driftHorizon x high) +
          startSlack x +
        windowPenalties (config := config) x high (driftHorizon x high + 1) +
            roundingBudget (config := config) x high +
        (∑ i ∈ cuts.boundary, (effectiveAt y i - effectiveAt x i)))
    (funded : gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high)
    (cutoff : Nat) (apart : exitedBefore x cutoff ∩ recentKeys y.state = ∅)
    (within : cutoff ≤ high + 1) :
    stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
      drift (config := config) x high := by
  have support := supported
  obtain ⟨genesis, _, _, _, early, endEpoch, guard⟩ := supported
  have xEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early
  have uniqueX := shared.pubkeysDistinct genesis
  have uniqueY := (shared.append tail).pubkeysDistinct genesis
  have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  obtain ⟨sched⟩ := ScheduledAllocation.ofReads tail high
  have core := stateDrift_scheduledReserve_le (config := config) uniqueX uniqueY early guard
    cuts lossBoundary sched funded
    (scheduledBoundaryProducer shared tail high support twoSlots _ epochs
      (by unfold horizonEnd driftHorizon; omega) rfl)
    (oldBoundary_le shared tail high support twoSlots)
  have reserve := commonSlashed_le_commonReserve sched uniqueX uniqueY xEarly within
    (cutoff_le_farFuture guard twoSlots within) apart
  omega

/-- The common ledger of a tail from Electra.

It comes from the new cohort's allocation and the gain funding. -/
private theorem commonLedger_of_allocation {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    {ledger : RoundLedger tail high} {owned : Ownership}
    {tokens : BLSPubkey → Finset TokenOrigin}
    (allocation : NewCohortAllocation tail high ledger owned tokens)
    (funded : gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high)
    (cutoff : Nat) (apart : exitedBefore x cutoff ∩ recentKeys y.state = ∅)
    (within : cutoff ≤ high + 1) :
    stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
      drift (config := config) x high :=
  commonLedger_of_cuts shared tail high supported twoSlots allocation.toNewCohortCuts
    (allocation.loss_boundary_bound allocation.toNewCohortCuts.boundary_supported) funded
    cutoff apart within

/-- The common ledger of a tail before Electra.

The new cohort and its round ledger exist before the fork.

The gain outside the previous-only keys fits `activationBudget`, which the gain budget contains. -/
private theorem commonLedger_pre {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (before : x.fork < .pectra)
    (cutoff : Nat) (apart : exitedBefore x cutoff ∩ recentKeys y.state = ∅)
    (within : cutoff ≤ high + 1) :
    stateDrift x y + 2 * commonSlashed x y (exitedBefore x cutoff) ≤
      drift (config := config) x high := by
  obtain ⟨genesis, _, _, _, early, endEpoch, _⟩ := id supported
  have uniqueY := (shared.append tail).pubkeysDistinct genesis
  have yBefore := (regime_of_supported shared tail supported).resolve_left
    (Nat.not_le_of_gt before)
  obtain ⟨ledger, -⟩ := (LedgerCuts.ofStops tail fun i => Classical.choice
    (Stop.exists tail i)).roundLedger_pre shared supported before twoSlots
  obtain ⟨cuts⟩ := NewCohortCuts.exists tail ledger.toLedgerCuts high uniqueY early twoSlots
    endEpoch
  obtain ⟨events, replayed⟩ := tail.balanceEvents_ok early high
  have funded : gainWithoutPreviousOnly x y ≤ gainBudget (config := config) x high := by
    obtain ⟨genesis, _, caps, aligned, _, within, guard⟩ := id supported
    have gain : gainWithoutPreviousOnly x y ≤ activationBudget (config := config) x high :=
      pre_gain_budget shared tail genesis caps aligned twoSlots yBefore high within guard
    unfold gainBudget
    omega
  exact commonLedger_of_cuts shared tail high supported twoSlots cuts
    (cuts.loss_boundary_pre shared tail supported ledger uniqueY before twoSlots replayed
      cuts.boundary_supported) funded cutoff apart within

end

section

open Cryptography.Bls Uint64

/-- Each fresh tag of a queue names a source whose exit is its tag epoch. -/
def FreshExits {fork : Fork} (s : BeaconState preset fork)
    (queue : List TaggedEntry) : Prop :=
  ∀ tag ∈ queue, ∀ n, tag.tag = .fresh n → ∃ v,
    s.validators.data[tag.entry.sourceIndex.toNat]? = some v ∧
      v.exitEpoch.toNat = tag.epoch ∧ v.exitEpoch ≠ FAR_FUTURE_EPOCH

/-- The replay of one block operation from `s` to `t` that records `added`.

The premises are the cut, the ownership and the run facts at the operation's input.

The conclusion is the replay over the operation and the same facts at its output.

`sites` lists the states at which the operation reads the consolidation churn.

It is `[]`, except for an accepted consolidation request, which reads it at `⟨fork, s⟩`.

`OperationReplay` closes this over the queue, the ownership and the positions. -/
def OperationReplayAt (x : ForkedBeaconState preset) (high : Nat)
    (rounding : Nat → Nat) {fork : Fork} (electra : .pectra ≤ fork)
    (s t : BeaconState preset fork) (added : List (BalanceEvent preset))
    (sites : List (ForkedBeaconState preset)) (queue : List TaggedEntry) (owned : Ownership)
    (eventPosition paymentPosition callPosition : Nat) : Prop :=
    ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned →
    AssignmentCut rounding queue owned →
    QueueErasure queue (pendingQueue ⟨fork, s⟩) →
    OwnershipBefore eventPosition paymentPosition owned →
    RetiredActivated s owned.retired →
    EndpointCoverAll x ⟨fork, s⟩ owned →
    FutureEffectiveCover x ⟨fork, s⟩ owned →
    BalancesMatch s → ExitsOrdered s →
    RegistryLifecycle x.state s →
    getCurrentEpoch x.state ≤ getCurrentEpoch s →
    getCurrentEpoch s < FAR_FUTURE_EPOCH →
    SlashedExitAssigned s →
    FreshExits s queue →
    ∃ (queue' : List TaggedEntry) (calls : List (IndexedDepartureCall preset config))
      (owned' : Ownership),
      ReservedReplay (config := config) (checks := checks) x high rounding
        ⟨fork, s⟩ (getCurrentEpoch s) ⟨fork, t⟩ (getCurrentEpoch t)
        eventPosition paymentPosition callPosition added queue queue' [] [] calls
        owned owned' ∧
      ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch t) (queue'.map (·.entry)) owned' ∧
      AssignmentCut rounding queue' owned' ∧
      QueueErasure queue' (pendingQueue ⟨fork, t⟩) ∧
      RetiredActivated t owned'.retired ∧
      EndpointCoverAll x ⟨fork, t⟩ owned' ∧
      FutureEffectiveCover x ⟨fork, t⟩ owned' ∧
      SlashedExitAssigned t ∧
      FreshExits t queue' ∧
      DepartureQueueTrace (s.earliestConsolidationEpoch electra)
        (s.consolidationBalanceToConsume electra) (calls.map (·.call))
        (t.earliestConsolidationEpoch electra) (t.consolidationBalanceToConsume electra) ∧
      ConsolidationCallSites preset config calls sites

/-- The replay of one block operation for every queue, ownership and position. -/
def OperationReplay (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat)
    {fork : Fork} (electra : .pectra ≤ fork) (s t : BeaconState preset fork)
    (added : List (BalanceEvent preset)) (sites : List (ForkedBeaconState preset)) : Prop :=
  ∀ (queue : List TaggedEntry) (owned : Ownership)
    (eventPosition paymentPosition callPosition : Nat),
    OperationReplayAt (config := config) (checks := checks) x high rounding electra s t added
      sites queue owned eventPosition paymentPosition callPosition

end

section

open Cryptography.Bls

/-- From Electra the upgrades of a slot record no crossing. -/
theorem upgradeBalanceReplay_electra_nil {u : ForkedBeaconState preset}
    {crossings : List (BalanceEvent preset)} (electra : .pectra ≤ u.fork)
    (replayed : upgradeBalanceReplay (config := config) (checks := checks) u = .ok crossings) :
    crossings = [] := by
  fun_induction upgradeBalanceReplay (config := config) (checks := checks) u
    generalizing crossings with
  | case1 s due ih =>
    obtain ⟨next, _, rest⟩ := bind_ok_iff.mp replayed
    obtain ⟨prior, priorOk, last⟩ := bind_ok_iff.mp rest
    have nextElectra := Nat.le_trans electra (Nat.le_of_lt next.property)
    have empty := ih next nextElectra priorOk
    have notDencun : s.fork ≠ .dencun := by
      intro dencun
      rw [dencun] at electra
      exact absurd electra (by decide)
    simp only [notDencun, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at last
    exact last ▸ empty
  | case2 =>
    cases replayed
    rfl

/-- From Electra the upgrades of a slot are silent frame steps. -/
private theorem upgrades_framePath_electra {u v : ForkedBeaconState preset}
    (electra : .pectra ≤ u.fork) (ok : processUpgrades config checks u = .ok v) :
    FramePath config checks u v := by
  fun_induction processUpgrades config checks u generalizing v with
  | case1 s due ih =>
    obtain ⟨next, nextOk, rest⟩ := bind_ok_iff.mp ok
    have notDencun : s.fork ≠ .dencun := by
      intro dencun
      rw [dencun] at electra
      exact absurd electra (by decide)
    exact .cons (.upgrade nextOk notDencun)
      (ih next (Nat.le_trans electra (Nat.le_of_lt next.property)) rest)
  | case2 =>
    cases ok
    exact .nil

/-- From Electra and before Gloas the upgrades of a slot keep the reserve cut and the queue.

They also keep the retired activations and both covers.

They keep the registry, the balances, the pending consolidations and the slot.

The cap of every validator is the Electra cap on both sides. -/
private theorem upgrades_reserved_facts {x u v : ForkedBeaconState preset} {high : Nat}
    {queue : List TaggedEntry} {owned : Ownership}
    (electra : .pectra ≤ u.fork) (early : v.fork < .glamsterdam)
    (ok : processUpgrades config checks u = .ok v)
    (reserve : ReserveCut x high u (getCurrentEpoch u.state) (queue.map (·.entry)) owned)
    (erasure : QueueErasure queue (pendingQueue u))
    (retired : RetiredActivated u.state owned.retired)
    (cover : EndpointCoverAll x u owned) (future : FutureEffectiveCover x u owned) :
    getCurrentEpoch v.state = getCurrentEpoch u.state ∧
      ReserveCut x high v (getCurrentEpoch v.state) (queue.map (·.entry)) owned ∧
      QueueErasure queue (pendingQueue v) ∧ RetiredActivated v.state owned.retired ∧
      EndpointCoverAll x v owned ∧ FutureEffectiveCover x v owned := by
  have target : .pectra ≤ v.fork := Nat.le_trans electra (processUpgrades_fork_le ok)
  obtain ⟨registry, balances, pending⟩ := processUpgrades_retained_data electra early ok target
  have slot := processUpgrades_slot ok
  obtain ⟨f, s⟩ := u
  obtain ⟨g, t⟩ := v
  dsimp only at electra target registry balances pending slot ⊢
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, slot]
  have cap : ∀ w : Validator, withdrawalMaxEffectiveBalance preset g w =
      withdrawalMaxEffectiveBalance preset f w := by
    intro w
    simp only [withdrawalMaxEffectiveBalance, electra, target, ↓reduceIte]
  have queueSame : pendingQueue (⟨g, t⟩ : ForkedBeaconState preset) = pendingQueue ⟨f, s⟩ := by
    simp only [pendingQueue, electra, target, ↓reduceDIte, pending]
  refine ⟨epoch, ?_, queueSame ▸ erasure, ?_, ?_, ?_⟩
  · simpa only [ReserveCut, FundingRelevant, effectiveAt, actualBalanceAt, registry, balances,
      cap, epoch] using reserve
  · simpa only [RetiredActivated, registry] using retired
  · simpa only [EndpointCoverAll, actualBalanceAt, registry, balances, cap, epoch] using cover
  · simpa only [FutureEffectiveCover, effectiveAt, registry, epoch] using future

/-- From Electra and before Gloas, the upgrades of a slot record nothing and are one frame. -/
theorem reservedReplay_upgrades {x u v : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {crossings : List (BalanceEvent preset)}
    {queue : List TaggedEntry} {owned : Ownership}
    {eventPosition paymentPosition callPosition : Nat}
    (ok : processUpgrades config checks u = .ok v)
    (electra : .pectra ≤ u.fork) (early : v.fork < .glamsterdam)
    (replayed : upgradeBalanceReplay (config := config) (checks := checks) u = .ok crossings)
    (frame : ReservedFrame (config := config) (checks := checks) x high rounding
      u u (getCurrentEpoch u.state) (getCurrentEpoch u.state) queue owned owned)
    (retired : RetiredActivated u.state owned.retired)
    (cover : EndpointCoverAll x u owned) (future : FutureEffectiveCover x u owned) :
    ∃ (queue' : List TaggedEntry) (calls' : List (IndexedDepartureCall preset config))
      (owned' : Ownership),
      ReservedReplay (config := config) (checks := checks) x high rounding
        u (getCurrentEpoch u.state) v (getCurrentEpoch v.state)
        eventPosition paymentPosition callPosition crossings queue queue' [] [] calls'
        owned owned' ∧
      ReservedFrame (config := config) (checks := checks) x high rounding
        v v (getCurrentEpoch v.state) (getCurrentEpoch v.state) queue' owned' owned' ∧
      RetiredActivated v.state owned'.retired ∧
      EndpointCoverAll x v owned' ∧ FutureEffectiveCover x v owned' := by
  obtain rfl := upgradeBalanceReplay_electra_nil electra replayed
  obtain ⟨_, _, _, assignment, _, erasure, _, reserve, _⟩ := frame
  obtain ⟨epoch, reserveV, erasureV, retiredV, coverV, futureV⟩ :=
    upgrades_reserved_facts electra early ok reserve erasure retired cover future
  have identity : OwnedFrame owned owned :=
    ⟨reserve.1, reserve.1, rfl, fun _ => Or.inl rfl, Finset.Subset.refl _, rfl,
      fun _ => Nat.le_refl _⟩
  refine ⟨queue, [], owned,
    .nil ⟨upgrades_framePath_electra electra ok, UInt64.le_of_eq epoch.symm, identity,
      assignment, assignment, erasure, erasureV, reserve, reserveV⟩,
    reservedFrame_refl reserveV assignment erasureV, retiredV, coverV, futureV⟩

/-- The deposit requests of a block change only the pending deposits and their start index.

So the registry, the balances, the slot and the pending consolidations stay.

The consolidation churn stays as well.

Every request is a silent frame step. -/
theorem depositRequests_kept {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} (requests : List DepositRequest)
    (ok : requests.foldlM (processDepositRequest · electra ·) s = .ok t) :
    t.validators = s.validators ∧ t.balances = s.balances ∧ t.slot = s.slot ∧
      t.pendingConsolidations = s.pendingConsolidations ∧
      t.earliestConsolidationEpoch = s.earliestConsolidationEpoch ∧
      t.consolidationBalanceToConsume = s.consolidationBalanceToConsume ∧
      FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ := by
  -- One request records its start index and appends a pending deposit, nothing else.
  have step : ∀ (u : BeaconState preset fork) (request : DepositRequest)
      (v : BeaconState preset fork),
      processDepositRequest u electra request = .ok v →
      v.validators = u.validators ∧ v.balances = u.balances ∧ v.slot = u.slot ∧
        v.pendingConsolidations = u.pendingConsolidations ∧
        v.earliestConsolidationEpoch = u.earliestConsolidationEpoch ∧
        v.consolidationBalanceToConsume = u.consolidationBalanceToConsume := by
    intro u request v first
    obtain ⟨-, -, -, start, pending, rfl⟩ := processDepositRequest_ok first
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨registry, balances, slot, pending, earliest, consume⟩ := foldlM_ok_invariant
    (fun u : BeaconState preset fork => u.validators = s.validators ∧ u.balances = s.balances ∧
      u.slot = s.slot ∧ u.pendingConsolidations = s.pendingConsolidations ∧
      u.earliestConsolidationEpoch = s.earliestConsolidationEpoch ∧
      u.consolidationBalanceToConsume = s.consolidationBalanceToConsume)
    (fun u request v ⟨registry, balances, slot, pending, earliest, consume⟩ computed => by
      obtain ⟨registry', balances', slot', pending', earliest', consume'⟩ :=
        step u request v computed
      exact ⟨registry'.trans registry, balances'.trans balances, slot'.trans slot,
        pending'.trans pending, earliest'.trans earliest, consume'.trans consume⟩)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ok
  exact ⟨registry, balances, slot, pending, earliest, consume,
    foldlM_framePath _ requests ok fun _ _ _ _ eq => .depositRequest electra eq⟩

/-- The staged headline with both common ledgers proved.

It needs only the selected inputs and the release. -/
theorem headline_ledger
    (hSelected : ∀ g x y : ForkedBeaconState preset,
      SelectedInputs (config := config) (checks := checks) (g := g) (x := x) (y := y))
    (hRelease : ∀ g x y : ForkedBeaconState preset,
      SelectedReleaseProducer (config := config) (checks := checks) (g := g) (x := x) (y := y)) :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) :=
  headline_staged hSelected hRelease (@commonLedger_of_allocation preset config checks)
    (@commonLedger_pre preset config checks)

end

/-- A paid pair carries a fresh tag exactly when its source is new.

A new source is one that is not an initial pending source at `x`. -/
theorem ReservedReplay.fresh_not_initial {g x y : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {events : List (BalanceEvent preset)}
    {final : List TaggedEntry} {allPayments : List (TaggedEntry × Payment preset)}
    {allAllocations : List OwnedRelease} {calls : List (IndexedDepartureCall preset config)}
    {before after : Ownership}
    (shared : Run config checks g x) (genesis : Genesis (config := config) (checks := checks) g)
    (electra : .pectra ≤ x.fork) (early : x.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0
      events (initialTags (x.state.pendingConsolidations electra).data.toList) final
      allPayments allAllocations calls before after)
    (lifecycle : ∀ e ∈ events, RegistryLifecycle x.state e.before.state) :
    ∀ pair ∈ allPayments, ((∃ n, pair.1.tag = .fresh n) ↔
      (x.state.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == pair.2.source) = false) := by
  have invariant := shared.pendingConsolidation_invariant genesis early electra delay
  have initialKnown :
      TagsKnown x (initialTags (x.state.pendingConsolidations electra).data.toList) := by
    intro tag member
    obtain ⟨⟨entry, position⟩, inside, rfl⟩ := List.mem_map.mp member
    refine ⟨fun _ _ => ?_, fun _ kind => by cases kind⟩
    simpa only [pendingQueue, electra, ↓reduceDIte] using List.fst_mem_of_mem_zipIdx inside
  obtain ⟨-, members⟩ := history.counters_original.2.2.2.2.2.2.1 lifecycle initialKnown
  intro pair member
  obtain ⟨known, source⟩ := members pair member
  have tagKnown := known pair.1 List.mem_cons_self
  cases kind : pair.1.tag with
  | initial p =>
    have inside := tagKnown.1 p kind
    simp only [pendingQueue, electra, ↓reduceDIte] at inside
    have found : (x.state.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == pair.2.source) = true :=
      List.any_eq_true.mpr ⟨_, inside, by rw [source, beq_self_eq_true]⟩
    rw [found]
    simp
  | fresh n =>
    refine ⟨fun _ => ?_, fun _ => ⟨n, rfl⟩⟩
    have far := tagKnown.2 n kind
    cases initial : (x.state.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == pair.2.source)
    · rfl
    · exfalso
      obtain ⟨c, inside, same⟩ := List.any_eq_true.mp initial
      obtain ⟨v, found, _, _, assigned⟩ := invariant.2 c inside
      rw [beq_iff_eq] at same
      rw [← source, ← same, found] at far
      simp only [Option.all_some, beq_iff_eq] at far
      exact assigned far

/-- Filtering zipped pairs on their first component, then keeping that component's image. -/
theorem zip_filter_fst_map {α β γ : Type} (p : α → Bool) (f : α → γ) :
    ∀ (l : List α) (r : List β), l.length = r.length →
      ((l.zip r).filter (fun pair => p pair.1)).map (fun pair => f pair.1) = (l.filter p).map f
  | [], _, _ => by simp
  | _ :: _, [], same => by simp at same
  | a :: l, b :: r, same => by
    have rest := zip_filter_fst_map p f l r (by simpa using same)
    by_cases chosen : p a <;> simp [chosen, rest]

/-- SelectedRelease's `ActualPaymentCoverage` premise, for the fresh payments of the history. -/
theorem ReservedReplay.actual_payment_coverage {x y : ForkedBeaconState preset}
    {high : Nat} {rounding : Nat → Nat} {events : List (BalanceEvent preset)}
    {final : List TaggedEntry} {allPayments : List (TaggedEntry × Payment preset)}
    {allAllocations : List OwnedRelease} {calls : List (IndexedDepartureCall preset config)}
    {before after : Ownership} (electra : .pectra ≤ x.fork)
    (history : ReservedReplay (config := config) (checks := checks) x high rounding
      x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0
      events (initialTags (x.state.pendingConsolidations electra).data.toList) final
      allPayments allAllocations calls before after)
    (notInitial : ∀ pair ∈ allPayments, ((∃ n, pair.1.tag = .fresh n) ↔
      (x.state.pendingConsolidations electra).data.toList.any
        (fun c => c.sourceIndex.toNat == pair.2.source) = false)) :
    ActualPaymentCoverage events
      (((allPayments.zip allAllocations).filter fun pair =>
        pair.1.1.tag.isFresh).map
          fun pair => pair.1.2)
      (x.state.pendingConsolidations electra).data.toList := by
  obtain ⟨per, related, flat⟩ := history.counters_original.2.2.2.2.2.1
  have lengths : events.length = per.length := related.length_eq
  refine ⟨fun j => (per[j.val]'(lengths ▸ j.isLt)).map Prod.snd, fun j => ?_, ?_⟩
  · exact (List.forall₂_iff_get.mp related).2 j.val j.isLt _
  have spread : (List.finRange events.length).flatMap
      (fun j : Fin events.length => (per[j.val]'(lengths ▸ j.isLt)).map Prod.snd) =
      (per.map (List.map Prod.snd)).flatten := by
    rw [List.flatMap_def]
    congr 1
    apply List.ext_getElem (by simp [lengths])
    intro i _ _
    simp
  rw [spread, ← List.map_flatten, ← flat, List.filter_map]
  have zipped := zip_filter_fst_map
    (fun pair : TaggedEntry × Payment preset =>
      pair.1.tag.isFresh)
    Prod.snd allPayments allAllocations history.paired_rounds.length_eq
  refine zipped.trans (congrArg (List.map Prod.snd) (List.filter_congr fun pair member => ?_))
  have same := notInitial pair member
  cases kind : pair.1.tag with
  | initial p =>
    have : ¬ ∃ n, pair.1.tag = .fresh n := fun ⟨_, fresh⟩ => by rw [kind] at fresh; cases fresh
    have initial := Bool.not_eq_false _ |>.mp (mt same.mpr this)
    simp only [Function.comp_apply]
    rw [initial]
    rfl
  | fresh n =>
    have initial := same.mp ⟨n, kind⟩
    simp only [Function.comp_apply]
    rw [initial]
    rfl

/-- The release partition of the selected release, the source rounds and both rho sums.

They come from the history's fresh payments. -/
theorem ReservedReplay.release_rounding {x y : ForkedBeaconState preset} {high : Nat}
    {tail : Run config checks x y}
        (ledger : RoundLedger (config := config) (checks := checks) tail high)
    {events : List (BalanceEvent preset)} {queue final : List TaggedEntry}
    {allPayments : List (TaggedEntry × Payment preset)} {allAllocations : List OwnedRelease}
    {calls : List (IndexedDepartureCall preset config)} {before after : Ownership}
    (history : ReservedReplay (config := config) (checks := checks) x high
      (fun i => if i ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)
      x (getCurrentEpoch x.state) y (getCurrentEpoch y.state) 0 0 0
      events queue final allPayments allAllocations calls before after)
    {selected : List SelectedCharge} {payments : List (Payment preset)}
    {tags : List TaggedEntry} {allocations : List OwnedRelease}
    (fresh : let pairs := (allPayments.zip allAllocations).filter fun pair =>
        pair.1.1.tag.isFresh
      payments = pairs.map (fun pair => pair.1.2) ∧ allocations = pairs.map Prod.snd ∧
        tags = pairs.map (fun pair => pair.1.1))
    (chosen : SelectedPayments selected payments tags) :
    ReleasePartition selected payments allocations ∧
    (∀ j : Fin allocations.length, ∃ p, payments[j.val]? = some p ∧
      allocations[j].sourceRound =
        if p.source ∈ ledger.sourceFalling then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) ∧
    (allocations.map (·.sourceRound)).sum ≤ roundingBudget (config := config) x high ∧
    (allocations.map (·.baseline)).sum ≤ (selected.map (·.amount)).sum +
        roundingBudget (config := config) x high := by
  dsimp only at fresh
  obtain ⟨rfl, rfl, rfl⟩ := fresh
  have rounds := history.fresh_source_round_bound ledger _ rfl
  have baselines := history.fresh_baseline_sum_le
  dsimp only at baselines
  have facts : ∀ pair ∈ (allPayments.zip allAllocations).filter (fun pair =>
      pair.1.1.tag.isFresh),
      pair.2.baseline ≤ pair.1.1.amount + pair.2.sourceRound ∧
      pair.1.2.amount = pair.2.external + pair.2.baseline ∧
      pair.2.sourceRound = if pair.1.2.source ∈ ledger.sourceFalling then
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0 := by
    intro pair member
    obtain ⟨zipped, chosenTag⟩ := List.mem_filter.mp member
    obtain ⟨parts, amount⟩ := List.forall₂_zip history.paired_releases zipped
    refine ⟨?_, amount, List.forall₂_zip history.paired_rounds zipped⟩
    cases kind : pair.1.1.tag with
    | initial p => rw [kind] at chosenTag; cases chosenTag
    | fresh n => simpa only [kind] using parts
  generalize (allPayments.zip allAllocations).filter (fun pair =>
      pair.1.1.tag.isFresh) = pairs
    at facts rounds baselines chosen ⊢
  obtain ⟨sizes, tagSizes, each⟩ := chosen
  simp only [List.length_map] at sizes tagSizes
  -- Each selected amount is its tag's amount.
  have amounts : selected.map (·.amount) = pairs.map (fun pair => pair.1.1.amount) := by
    apply List.ext_getElem (by simp [sizes])
    intro i inside _
    have below : i < selected.length := by simpa using inside
    obtain ⟨_, tag, _, found, _, _, _, _, _, amountEq, _, _⟩ := each ⟨i, below⟩
    simp only [Fin.getElem_fin, List.getElem?_map,
      List.getElem?_eq_getElem (show i < pairs.length by omega), Option.map_some,
      Option.some.injEq] at found amountEq
    simp only [List.getElem_map]
    rw [amountEq, ← found]
  refine ⟨⟨by simp, by simp [sizes], fun i => ?_⟩, fun j => ?_, ?_, ?_⟩
  · have inside : i.val < pairs.length := by simpa using i.isLt
    obtain ⟨below, amount, _⟩ := facts _ (List.getElem_mem inside)
    have selectedAmount := congrArg (·[i.val]?) amounts
    simp only [List.getElem?_map, List.getElem?_eq_getElem inside,
      List.getElem?_eq_getElem (show i.val < selected.length by omega), Option.map_some,
      Option.some.injEq] at selectedAmount
    refine ⟨(pairs[i.val]).2, selected[i.val]'(by omega), by simp [inside],
      List.getElem?_eq_getElem _, ?_, ?_⟩
    · simp only [Fin.getElem_fin, List.getElem_map]
      omega
    · omega
  · have inside : j.val < pairs.length := by simpa using j.isLt
    refine ⟨(pairs[j.val]).1.2, by simp [inside], ?_⟩
    simp only [Fin.getElem_fin, List.getElem_map]
    exact (facts _ (List.getElem_mem inside)).2.2
  · simpa only [List.map_map, Function.comp_def] using rounds
  · rw [amounts]
    simp only [List.map_map, Function.comp_def] at rounds ⊢
    omega

section

open Cryptography.Bls Uint64

/-- A strict drop of `i`'s effective balance between consecutive states of a path. -/
def PathDrop (path : List (ForkedBeaconState preset)) (i : Nat) : Prop :=
  ∃ j a b, path[j]? = some a ∧ path[j + 1]? = some b ∧ effectiveAt b i < effectiveAt a i

/-- A strict drop of `i`'s effective balance between consecutive states of a step's path. -/
def StepDrop {u v : ForkedBeaconState preset} (step : Step config checks u v)
    (i : Nat) : Prop :=
  ∃ j a b, step.balancePath[j]? = some a ∧ step.balancePath[j + 1]? = some b ∧
    effectiveAt b i < effectiveAt a i

/-- The bound a block hands to its requests: every key whose exit this block assigns. -/
def BlockAssigned (rounding : Nat → Nat) {f h : Fork} (m : BeaconState preset f)
    (n : BeaconState preset h) (o : Ownership) : Prop :=
  ∀ (i : Nat) (v w : Validator), m.validators.data[i]? = some v →
    n.validators.data[i]? = some w →
    v.exitEpoch = FAR_FUTURE_EPOCH → w.exitEpoch ≠ FAR_FUTURE_EPOCH →
    o.original i ≤ v.effectiveBalance.toNat + rounding i

/-- A proposer slashing records one slashings event with its limits read at `s`. -/
def ProposerSlashingReplay : Prop :=
  ∀ (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat) {fork : Fork}
    (electra : .pectra ≤ fork) (_early : fork < .glamsterdam)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {s t : BeaconState preset fork} (slashing : ProposerSlashing) {credit debit : Nat},
    slashingLimits [slashing.signedHeader1.message.proposerIndex] s = .ok (credit, debit) →
    processProposerSlashing config checks s slashing = .ok t →
    OperationReplay (config := config) (checks := checks) x high rounding electra s t
      [⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] []

/-- An attester slashing records one slashings event with its limits read at `s`. -/
def AttesterSlashingReplay : Prop :=
  ∀ (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat) {fork : Fork}
    (electra : .pectra ≤ fork) (_early : fork < .glamsterdam)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {s t : BeaconState preset fork} (slashing : AttesterSlashing preset fork)
    {credit debit : Nat},
    slashingLimits (slashingIndices slashing) s = .ok (credit, debit) →
    processAttesterSlashing config checks s slashing = .ok t →
    OperationReplay (config := config) (checks := checks) x high rounding electra s t
      [⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] []

/-- The voluntary exits of a block record nothing. -/
def VoluntaryExitsReplay : Prop :=
  ∀ (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat) {fork : Fork}
    (electra : .pectra ≤ fork) (_early : fork < .glamsterdam)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {s t : BeaconState preset fork} (exits : List SignedVoluntaryExit),
    exits.foldlM (processVoluntaryExit config checks) s = .ok t →
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] []

/-- The withdrawal requests of a block record nothing. -/
def WithdrawalRequestsReplay : Prop :=
  ∀ (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat) {fork : Fork}
    (electra : .pectra ≤ fork) (_early : fork < .glamsterdam)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {s t : BeaconState preset fork} (requests : List WithdrawalRequest),
    requests.foldlM (processWithdrawalRequest config · electra ·) s = .ok t →
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] []

/-- `OperationReplay` for a whole block from `s` to `t`.

It also takes `BlockAssigned` at the block input, which each consolidation request reads. -/
def BlockOperationReplay (x : ForkedBeaconState preset) (high : Nat)
    (rounding : Nat → Nat) {fork : Fork} (electra : .pectra ≤ fork)
    (s t : BeaconState preset fork) (added : List (BalanceEvent preset))
    (sites : List (ForkedBeaconState preset)) : Prop :=
  ∀ (queue : List TaggedEntry) (owned : Ownership)
    (eventPosition paymentPosition callPosition : Nat),
    BlockAssigned rounding s t owned →
    OperationReplayAt (config := config) (checks := checks) x high rounding electra s t added
      sites queue owned eventPosition paymentPosition callPosition

/-- A block step's replay is one block operation replay over its events.

Its sites are the block's consolidation sites. -/
def BlockReplay : Prop :=
  ∀ (x : ForkedBeaconState preset) (high : Nat) (rounding : Nat → Nat) {fork : Fork}
    (electra : .pectra ≤ fork) (_early : fork < .glamsterdam)
    (_delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (_compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {s t : BeaconState preset fork} (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork) (due : upgradeDue config ⟨fork, s⟩ = false)
    (ok : applySignedBlock config checks engine s signed true = .ok t)
    {events : List (BalanceEvent preset)},
    (Step.block engine signed due ok).balanceEvents = .ok events →
    BlockOperationReplay (config := config) (checks := checks) x high rounding electra s t
      events (Step.block (checks := checks) engine signed due ok).consolidationSites

/-- The replay of one slot step of a shared run, from `u` to `v`, inside the horizon.

The run facts at the epoch input come from the shared run and the branch prefix.

The run-level replay supplies the queue provenance and the zero initial tags from its history. -/
def SlotStepReplay : Prop :=
  ∀ {g x u v : ForkedBeaconState preset} {high : Nat} {rounding : Nat → Nat}
    {queue : List TaggedEntry} {owned : Ownership}
    {eventPosition paymentPosition callPosition : Nat}
    (_shared : Run config checks g x) (_pre : Run config checks x u)
    (_genesis : Genesis (config := config) (checks := checks) g) (_caps : CapOrder preset)
    (_twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (_delayTwo : 2 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (_electraX : .pectra ≤ x.fork) (electra : .pectra ≤ u.fork) (_early : v.fork < .glamsterdam)
    (_endEpoch : (getCurrentEpoch u.state).toNat ≤ high + 1)
    (ok : advanceSlotAcross config checks u = .ok v) {events : List (BalanceEvent preset)}
    (_replayed : (Step.slot ok).balanceEvents = .ok events)
    (_reserve : ReserveCut x high u (getCurrentEpoch u.state) (queue.map (·.entry)) owned)
    (_assignment : AssignmentCut rounding queue owned)
    (_erasure : QueueErasure queue (pendingQueue u))
    (_prior : OwnershipBefore eventPosition paymentPosition owned)
    (_retired : RetiredActivated u.state owned.retired)
    (_cover : EndpointCoverAll x u owned) (_future : FutureEffectiveCover x u owned)
    (_fresh : FreshExits u.state queue)
    (_provenance : ∀ c ∈ queue.map (·.entry), c ∈ pendingQueue x ∨
      (x.state.validators.data[c.sourceIndex.toNat]?).all (·.exitEpoch == FAR_FUTURE_EPOCH))
    (_initialZero : ∀ tag ∈ queue, ∀ n, tag.tag = .initial n →
      owned.original tag.entry.sourceIndex.toNat = 0),
    ∃ (queue' : List TaggedEntry) (payments : List (TaggedEntry × Payment preset))
      (allocations : List OwnedRelease) (owned' : Ownership),
      ReservedReplay (config := config) (checks := checks) x high rounding
        u (getCurrentEpoch u.state) v (getCurrentEpoch v.state)
        eventPosition paymentPosition callPosition events queue queue' payments allocations []
        owned owned' ∧
      ReserveCut x high v (getCurrentEpoch v.state) (queue'.map (·.entry)) owned' ∧
      AssignmentCut rounding queue' owned' ∧
      QueueErasure queue' (pendingQueue v) ∧
      OwnershipBefore (eventPosition + events.length) (paymentPosition + payments.length)
        owned' ∧
      RetiredActivated v.state owned'.retired ∧
      EndpointCoverAll x v owned' ∧ FutureEffectiveCover x v owned' ∧
      FreshExits v.state queue' ∧
      (∀ e ∈ events, e.source = .consolidations →
        PendingConsolidationInvariant config e.before.state) ∧
      (∀ pair ∈ payments, pair.2.epoch ≤ (getCurrentEpoch v.state).toNat) ∧
      (∀ pair ∈ payments, ∀ n, pair.1.tag = .fresh n → ∃ w,
        pair.2.before.state.validators.data[pair.2.source]? = some w ∧
          pair.1.epoch + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat ≤
            w.withdrawableEpoch.toNat) ∧
      (∀ pair ∈ payments, Paying pair.2) ∧
      (0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat → ∀ down : Nat → Prop,
        (∀ i, owned.original i ≤ effectiveAt u i +
          (if down i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) →
        ∀ i, owned'.original i ≤ effectiveAt v i +
          (if down i ∨ StepDrop (Step.slot ok) i then
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0)) ∧
      ∀ target : .pectra ≤ v.fork,
        DepartureQueueTrace (u.state.earliestConsolidationEpoch electra)
          (u.state.consolidationBalanceToConsume electra) []
          (v.state.earliestConsolidationEpoch target)
          (v.state.consolidationBalanceToConsume target)

/-- A registry step keeps the slot and the registry size.

It keeps each validator's key, effective balance and credentials, and unslashes nobody.

It only assigns exits that were at the far future, and keeps activity up to the current epoch.

It keeps each withdrawable epoch, or moves one after the current epoch to another after it.

It keeps the order of exits and withdrawals. -/
def RegistryStep {fork : Fork} (s t : BeaconState preset fork) : Prop :=
  RegistryEntriesKept s t ∧
    (∀ (i : Nat) (w₀ w : Validator), s.validators.data[i]? = some w₀ →
      t.validators.data[i]? = some w →
      w.withdrawableEpoch = w₀.withdrawableEpoch ∨
        (getCurrentEpoch s < w₀.withdrawableEpoch ∧ getCurrentEpoch s < w.withdrawableEpoch)) ∧
    (∀ (i : Nat) (w₀ w : Validator), s.validators.data[i]? = some w₀ →
      t.validators.data[i]? = some w → ∀ e ≤ getCurrentEpoch s,
        isActiveValidator w e = isActiveValidator w₀ e) ∧
    t.slot = s.slot ∧ RegistryLifecycle s t ∧
    t.validators.data.size = s.validators.data.size ∧ ExitsOrdered t

theorem RegistryStep.of_validators {fork : Fork} {s t : BeaconState preset fork}
    (validators : t.validators.data = s.validators.data) (slot : t.slot = s.slot)
    (ordered : ExitsOrdered s) : RegistryStep s t := by
  refine ⟨?_, ?_, ?_, slot, ⟨by rw [validators], fun i v found =>
    ⟨v, by rw [validators]; exact found, .refl v⟩⟩, by rw [validators], ?_⟩
  · intro i w found
    rw [validators] at found
    exact ⟨w, found, rfl, rfl, rfl, id, .refl w⟩
  · intro i w₀ w read found
    rw [validators, read] at found
    cases found
    exact .inl rfl
  · intro i w₀ w read found _ _
    rw [validators, read] at found
    cases found
    rfl
  · intro v member
    rw [validators] at member
    exact ordered v member

theorem RegistryStep.refl {fork : Fork} {s : BeaconState preset fork}
    (ordered : ExitsOrdered s) : RegistryStep s s :=
  .of_validators rfl rfl ordered

theorem RegistryStep.trans {fork : Fork} {s u t : BeaconState preset fork}
    (one : RegistryStep s u) (two : RegistryStep u t) : RegistryStep s t := by
  obtain ⟨kept₁, withdrawable₁, activity₁, slot₁, life₁, size₁, _⟩ := one
  obtain ⟨kept₂, withdrawable₂, activity₂, slot₂, life₂, size₂, ordered₂⟩ := two
  have epoch : getCurrentEpoch u = getCurrentEpoch s := by simp only [getCurrentEpoch, slot₁]
  -- The validator at an index of `t` is read in `u`, then in `s`.
  have middle : ∀ (i : Nat) (w : Validator), t.validators.data[i]? = some w →
      ∃ w₁, u.validators.data[i]? = some w₁ := fun i w found => by
    obtain ⟨w₁, read, _⟩ := kept₂ i w found
    exact ⟨w₁, read⟩
  refine ⟨?_, ?_, ?_, slot₂.trans slot₁, life₁.trans life₂, size₂.trans size₁, ordered₂⟩
  · intro i w found
    obtain ⟨w₁, read₁, key₂, effective₂, credentials₂, clean₂, kept₂'⟩ := kept₂ i w found
    obtain ⟨w₀, read₀, key₁, effective₁, credentials₁, clean₁, kept₁'⟩ := kept₁ i w₁ read₁
    exact ⟨w₀, read₀, key₂.trans key₁, effective₂.trans effective₁,
      credentials₂.trans credentials₁, clean₁ ∘ clean₂, kept₁'.trans kept₂'⟩
  · intro i w₀ w read₀ found
    obtain ⟨w₁, read₁⟩ := middle i w found
    rw [epoch] at withdrawable₂
    rcases withdrawable₁ i w₀ w₁ read₀ read₁ with same₁ | ⟨old₁, new₁⟩ <;>
      rcases withdrawable₂ i w₁ w read₁ found with same₂ | ⟨old₂, new₂⟩
    · exact .inl (same₂.trans same₁)
    · exact .inr ⟨same₁ ▸ old₂, new₂⟩
    · exact .inr ⟨old₁, same₂ ▸ new₁⟩
    · exact .inr ⟨old₁, new₂⟩
  · intro i w₀ w read₀ found e early
    obtain ⟨w₁, read₁⟩ := middle i w found
    rw [activity₂ i w₁ w read₁ found e (epoch ▸ early), activity₁ i w₀ w₁ read₀ read₁ e early]

/-- Replacing one validator by a record that keeps the fields of a registry step is one. -/
theorem RegistryStep.set {fork : Fork} {s t : BeaconState preset fork}
    {index : ValidatorIndex} {v w : Validator}
    (read : s.validators.data[index.toNat]? = some v)
    (set : s.setValidator index w = .ok t)
    (key : w.pubkey = v.pubkey) (effective : w.effectiveBalance = v.effectiveBalance)
    (credentials : withdrawalMaxEffectiveBalance preset fork w =
      withdrawalMaxEffectiveBalance preset fork v)
    (clean : w.slashed = false → v.slashed = false) (life : ValidatorLifecycle v w)
    (withdrawable : w.withdrawableEpoch = v.withdrawableEpoch ∨
      (getCurrentEpoch s < v.withdrawableEpoch ∧ getCurrentEpoch s < w.withdrawableEpoch))
    (activity : ∀ e ≤ getCurrentEpoch s, isActiveValidator w e = isActiveValidator v e)
    (orderedW : w.exitEpoch ≤ w.withdrawableEpoch) (ordered : ExitsOrdered s) :
    RegistryStep s t := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have lookup : ∀ (j : Nat) (u : Validator),
      (s.putValidator index.toNat inside w).validators.data[j]? = some u →
      (j = index.toNat ∧ u = w) ∨ (j ≠ index.toNat ∧ s.validators.data[j]? = some u) := by
    intro j u found
    simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set] at found
    by_cases same : index.toNat = j
    · subst same
      rw [Array.getElem?_set_self] at found
      exact .inl ⟨rfl, (Option.some.inj found).symm⟩
    · rw [Array.getElem?_set_ne _ same] at found
      exact .inr ⟨Ne.symm same, found⟩
  have size : (s.putValidator index.toNat inside w).validators.data.size =
      s.validators.data.size := by
    simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
  refine ⟨?_, ?_, ?_, rfl, ⟨by rw [size], fun j u before => ?_⟩, size, ?_⟩
  · intro j u found
    rcases lookup j u found with ⟨rfl, rfl⟩ | ⟨_, before⟩
    · exact ⟨v, read, key, effective, credentials, clean, life⟩
    · exact ⟨u, before, rfl, rfl, rfl, id, .refl u⟩
  · intro j u₀ u before found
    rcases lookup j u found with ⟨rfl, rfl⟩ | ⟨_, same⟩
    · obtain rfl := Option.some.inj (before.symm.trans read)
      exact withdrawable
    · rw [Option.some.inj (same.symm.trans before)]
      exact .inl rfl
  · intro j u₀ u before found e early
    rcases lookup j u found with ⟨rfl, rfl⟩ | ⟨_, same⟩
    · obtain rfl := Option.some.inj (before.symm.trans read)
      exact activity e early
    · rw [Option.some.inj (same.symm.trans before)]
  · by_cases same : j = index.toNat
    · subst same
      obtain rfl := Option.some.inj (before.symm.trans read)
      exact ⟨w, by simp [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set,
        inside], life⟩
    · refine ⟨u, ?_, .refl u⟩
      simp only [BeaconState.putValidator, Serialization.Ssz.RootedForkList.data_set]
      rw [Array.getElem?_set_ne _ (Ne.symm same)]
      exact before
  · exact ExitsOrdered.putValidator inside ordered orderedW

/-- A quiet step is a registry step that records no balance event.

It keeps the balances, the queue and the consolidation churn.

It also keeps the assigned exits of slashed validators. -/
def QuietStep {fork : Fork} (electra : .pectra ≤ fork) (s t : BeaconState preset fork) :
    Prop :=
  RegistryStep s t ∧ t.balances = s.balances ∧
    t.pendingConsolidations = s.pendingConsolidations ∧
    t.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra ∧
    t.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra ∧
    (SlashedExitAssigned s → SlashedExitAssigned t)

theorem QuietStep.refl {fork : Fork} {electra : .pectra ≤ fork}
    {s : BeaconState preset fork} (ordered : ExitsOrdered s) : QuietStep electra s s :=
  ⟨.refl ordered, rfl, rfl, rfl, rfl, id⟩

theorem QuietStep.trans {fork : Fork} {electra : .pectra ≤ fork}
    {s u t : BeaconState preset fork}
    (one : QuietStep electra s u) (two : QuietStep electra u t) : QuietStep electra s t :=
  ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.1.trans one.2.2.2.2.1,
    two.2.2.2.2.2 ∘ one.2.2.2.2.2⟩

/-- Initiating an exit is quiet. -/
private theorem QuietStep.initiateValidatorExit {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {index : ValidatorIndex}
    (ok : initiateValidatorExit config s index = .ok t)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) :
    QuietStep electra s t := by
  have held := initiateValidatorExit_slashed_exit_assigned ok delay
  obtain ⟨v, found, ⟨_, rfl⟩ | ⟨far, queued, exitEpoch, withdrawableEpoch, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok ok
  · exact .refl ordered
  · have later := exitQueue_lt queue
    have sum := (addChecked_ok_iff.mp summed).2
    obtain ⟨left, earliest, shape⟩ := exitQueue_eq queue
    have data : queued.validators.data = s.validators.data := by rw [shape]
    have read : s.validators.data[index.toNat]? = some v := getValidator_eq_ok_iff.mp found
    have readQ : queued.validators.data[index.toNat]? = some v := by rw [data]; exact read
    have foundQ : getValidator queued index = .ok v := getValidator_eq_ok_iff.mpr readQ
    have late : getCurrentEpoch s < exitEpoch := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have delayed : exitEpoch ≤ withdrawableEpoch := UInt64.le_iff_toNat_le.mpr (by omega)
    have epochQ : getCurrentEpoch queued = getCurrentEpoch s := by rw [shape]; rfl
    -- The old withdrawable epoch was at the far future, after the current epoch.
    have oldLate : getCurrentEpoch s < v.withdrawableEpoch := by
      have order := ordered v (Array.mem_of_getElem? read)
      rw [far] at order
      rw [UInt64.le_antisymm (le_far _) order]
      exact finite
    have first : RegistryStep s queued := .of_validators data (by rw [shape]) ordered
    have second : RegistryStep queued t := RegistryStep.set readQ set
      rfl rfl rfl id ⟨fun _ => rfl, fun unset => absurd far unset⟩
      (.inr ⟨epochQ ▸ oldLate, epochQ ▸ UInt64.lt_of_lt_of_le late delayed⟩)
      (fun e early => by
        have one : e < exitEpoch := UInt64.lt_of_le_of_lt (epochQ ▸ early) late
        have two : e < FAR_FUTURE_EPOCH := UInt64.lt_of_le_of_lt (epochQ ▸ early) finite
        simp only [isActiveValidator, far, one, two])
      delayed first.2.2.2.2.2.2
    obtain ⟨_, rfl⟩ := setValidator_ok set
    subst shape
    exact ⟨first.trans second, rfl, rfl, rfl, rfl, held⟩

/-- A voluntary exit is quiet. -/
private theorem QuietStep.voluntaryExit {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {signed : SignedVoluntaryExit}
    (ok : processVoluntaryExit config checks s signed = .ok t)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) :
    QuietStep electra s t := by
  unfold processVoluntaryExit at ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact .initiateValidatorExit exited delay ordered finite

/-- A withdrawal request is quiet. -/
private theorem QuietStep.withdrawalRequest {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {request : WithdrawalRequest}
    (ok : processWithdrawalRequest config s electra request = .ok t)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) :
    QuietStep electra s t := by
  rcases withdrawalRequest_cases ok with rfl | ⟨index, exited⟩ | ⟨index, v, owed, paid⟩
  · exact .refl ordered
  · exact .initiateValidatorExit exited delay ordered finite
  · simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure,
      Except.pure] at paid
    obtain ⟨_, _, _, _, paid⟩ := paid
    split at paid
    · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at paid
      obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := paid
      simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at churned
      obtain ⟨_, _, _, _, _, _, final⟩ := churned
      cases final
      exact ⟨.of_validators rfl rfl ordered, rfl, rfl, rfl, rfl, id⟩
    · cases paid
      exact .refl ordered

/-- A fold of steps, each of which keeps a property at the same current epoch, keeps it. -/
theorem foldlM_step {α : Type} {fork : Fork}
    (P : BeaconState preset fork → BeaconState preset fork → Prop)
    (refl : ∀ s, ExitsOrdered s → P s s)
    (trans : ∀ {s u t}, P s u → P u t → P s t)
    (ordered' : ∀ {s t}, P s t → ExitsOrdered t)
    (slot : ∀ {s t}, P s t → t.slot = s.slot)
    (action : BeaconState preset fork → α → Except TransitionError (BeaconState preset fork))
    (step : ∀ item a b, action a item = .ok b → ExitsOrdered a →
      getCurrentEpoch a < FAR_FUTURE_EPOCH → P a b)
    (items : List α) {s t : BeaconState preset fork}
    (ok : items.foldlM action s = .ok t)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) : P s t :=
  (foldlM_ok_invariant (fun u => P s u ∧ getCurrentEpoch u < FAR_FUTURE_EPOCH)
    (fun u item v ⟨held, bounded⟩ computed => by
      have one := step item u v computed (ordered' held) bounded
      have epoch : getCurrentEpoch v = getCurrentEpoch u := by
        simp only [getCurrentEpoch, slot one]
      exact ⟨trans held one, epoch ▸ bounded⟩)
    ⟨refl s ordered, finite⟩ ok).1

/-- A registry step keeps the reserve cut at the current epoch.

The cut after it is read in the state with its validators and the balances before it. -/
private theorem reserveCut_of_registryStep {x : ForkedBeaconState preset} {high : Nat}
    {fork : Fork} {s t : BeaconState preset fork} {suffix : List PendingConsolidation}
    {o : Ownership}
    (registry : RegistryStep s t) (retired : RetiredActivated s o.retired)
    (life : RegistryLifecycle x.state s) (started : getCurrentEpoch x.state ≤ getCurrentEpoch s)
    (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH)
    (reserve : ReserveCut x high ⟨fork, s⟩ (getCurrentEpoch s) suffix o) :
    ReserveCut x high ⟨fork, { s with validators := t.validators }⟩ (getCurrentEpoch s) suffix o :=
  reserveCut_of_kept (v := { s with validators := t.validators }) retired.assigned
    (lifecycle_start_active_assigned (u := ⟨fork, s⟩) life (UInt64.lt_of_le_of_lt started finite))
    registry.2.2.1 registry.1 registry.2.1 rfl reserve

/-- A quiet step along a frame path is an operation that records nothing. -/
theorem operationReplay_quiet {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork}
    (path : FramePath (config := config) (checks := checks) ⟨fork, s⟩ ⟨fork, t⟩)
    (quiet : ExitsOrdered s → getCurrentEpoch s < FAR_FUTURE_EPOCH → QuietStep electra s t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] := by
  intro queue owned eventPosition paymentPosition callPosition reserve assignment erasure _
    retired cover future _ ordered life started finite slashedExit fresh
  obtain ⟨registry, balances, sameQueue, earliest, left, slashed⟩ := quiet ordered finite
  obtain ⟨kept, _, _, slot, step, _, _⟩ := id registry
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  have pending : pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) = pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, sameQueue]
  have reserveT : ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch t) (queue.map (·.entry)) owned := by
    rw [epoch]
    exact reserveCut_of_kept retired.assigned
      (lifecycle_start_active_assigned (u := ⟨fork, s⟩) life
        (UInt64.lt_of_le_of_lt started finite))
      registry.2.2.1 kept registry.2.1 balances reserve
  have frame : ReservedFrame (config := config) (checks := checks) x high rounding
      ⟨fork, s⟩ ⟨fork, t⟩ (getCurrentEpoch s) (getCurrentEpoch t) queue owned owned :=
    ⟨path, epoch ▸ UInt64.le_refl _,
      (reservedFrame_refl (config := config) (checks := checks) reserve assignment
        erasure).2.2.1,
      assignment, assignment, erasure, pending ▸ erasure, reserve, reserveT⟩
  refine ⟨queue, [], owned, .nil frame, reserveT, assignment, pending ▸ erasure,
    retired.lifecycle step, endpointCover_of_kept kept balances epoch cover,
    futureCover_of_kept kept epoch future, slashed slashedExit, ?_,
    by rw [earliest, left]; exact .nil _ _, by simp [ConsolidationCallSites]⟩
  intro tag member n tagged
  obtain ⟨v, read, exit, assigned⟩ := fresh tag member n tagged
  obtain ⟨w, located, kept'⟩ := step.validators _ v read
  exact ⟨w, located, (kept'.exitEpoch assigned) ▸ exit, (kept'.exitEpoch assigned) ▸ assigned⟩

/-- The voluntary exits of a block record nothing. -/
theorem reservedReplay_voluntaryExits :
    VoluntaryExitsReplay (preset := preset) (config := config) (checks := checks) :=
  fun _ _ _ _ electra _ delay _ _ exits ok =>
  operationReplay_quiet (foldlM_framePath _ exits ok fun _ _ _ _ eq => .exit eq)
    (foldlM_step (QuietStep electra) (fun _ => .refl) .trans (·.1.2.2.2.2.2.2) (·.1.2.2.2.1) _
      (fun _ _ _ step => QuietStep.voluntaryExit step delay) exits ok)

/-- The withdrawal requests of a block record nothing. -/
theorem reservedReplay_withdrawalRequests :
    WithdrawalRequestsReplay (preset := preset) (config := config) (checks := checks) :=
  fun _ _ _ _ electra _ delay _ _ requests ok =>
  operationReplay_quiet
    (foldlM_framePath _ requests ok fun _ _ _ _ eq => .withdrawalRequest electra eq)
    (foldlM_step (QuietStep electra) (fun _ => .refl) .trans (·.1.2.2.2.2.2.2) (·.1.2.2.2.1) _
      (fun _ _ _ step => QuietStep.withdrawalRequest step delay) requests ok)

/-- A slashing step is a registry step that keeps the queue and the consolidation churn.

It also keeps the balance count. -/
def SlashStep {fork : Fork} (electra : .pectra ≤ fork) (s t : BeaconState preset fork) :
    Prop :=
  RegistryStep s t ∧ t.pendingConsolidations = s.pendingConsolidations ∧
    t.earliestConsolidationEpoch electra = s.earliestConsolidationEpoch electra ∧
    t.consolidationBalanceToConsume electra = s.consolidationBalanceToConsume electra ∧
    t.balances.data.size = s.balances.data.size

theorem SlashStep.refl {fork : Fork} {electra : .pectra ≤ fork}
    {s : BeaconState preset fork} (ordered : ExitsOrdered s) : SlashStep electra s s :=
  ⟨.refl ordered, rfl, rfl, rfl, rfl⟩

theorem SlashStep.trans {fork : Fork} {electra : .pectra ≤ fork}
    {s u t : BeaconState preset fork}
    (one : SlashStep electra s u) (two : SlashStep electra u t) : SlashStep electra s t :=
  ⟨one.1.trans two.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
    two.2.2.2.1.trans one.2.2.2.1, two.2.2.2.2.trans one.2.2.2.2⟩

/-- Setting one balance keeps every field of a slashing step. -/
private theorem SlashStep.setBalance {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {index : ValidatorIndex} {balance : Gwei}
    (set : s.setBalance index balance = .ok t) (ordered : ExitsOrdered s) :
    SlashStep electra s t := by
  have sizes := (sameSizes_setBalance set).2
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨.of_validators rfl rfl ordered, rfl, rfl, rfl, sizes⟩

/-- Slashing a validator that is slashable at the current epoch is a slashing step.

Its exit is assigned, or set after the current epoch.

Its withdrawable epoch is after the current epoch by slashability, and only grows. -/
private theorem SlashStep.slashValidator {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {index : ValidatorIndex} {v : Validator}
    (early : fork < .glamsterdam)
    (ok : slashValidator config s index none = .ok t)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (found : getValidator s index = .ok v)
    (slashable : isSlashableValidator v (getCurrentEpoch s) = true)
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) :
    SlashStep electra s t := by
  obtain ⟨exited, validator, withdrawable, marked, _, _, slashings, lowered, _, _, raised, last,
    exitedOk, foundE, _, markedOk, _, _, _, loweredOk, _, _, raisedOk, lastOk, done⟩ :=
    slashValidator_ok ok
  have quiet := QuietStep.initiateValidatorExit (electra := electra) exitedOk delay ordered finite
  have read : s.validators.data[index.toNat]? = some v := getValidator_eq_ok_iff.mp found
  have readE : exited.validators.data[index.toNat]? = some validator :=
    getValidator_eq_ok_iff.mp foundE
  have epochE : getCurrentEpoch exited = getCurrentEpoch s := by
    simp only [getCurrentEpoch, quiet.1.2.2.2.1]
  -- After the exit the withdrawable epoch is still after the current epoch.
  have slashableLate : getCurrentEpoch s < v.withdrawableEpoch := by
    simp only [isSlashableValidator, Bool.and_eq_true, decide_eq_true_eq] at slashable
    exact slashable.2
  have oldLate : getCurrentEpoch exited < validator.withdrawableEpoch := by
    rw [epochE]
    rcases quiet.1.2.1 _ v validator read readE with same | ⟨_, late⟩
    · exact same ▸ slashableLate
    · exact late
  have grows : validator.withdrawableEpoch ≤ max validator.withdrawableEpoch withdrawable := by
    rw [UInt64.max_def]
    split
    · assumption
    · exact UInt64.le_refl _
  have orderedE := quiet.1.2.2.2.2.2.2
  have mark : SlashStep electra exited marked := by
    have registry := RegistryStep.set readE markedOk rfl rfl rfl (fun flag => by simp at flag)
      ⟨fun _ => rfl, fun _ => rfl⟩ (.inr ⟨oldLate, UInt64.lt_of_lt_of_le oldLate grows⟩)
      (fun _ _ => rfl)
      (UInt64.le_trans (orderedE validator (Array.mem_of_getElem? readE)) grows) orderedE
    have sizes := (sameSizes_setValidator markedOk).2
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    exact ⟨registry, rfl, rfl, rfl, sizes⟩
  have orderedM := mark.1.2.2.2.2.2.2
  obtain ⟨_, loweredSet⟩ := decreaseBalance_ok loweredOk
  obtain ⟨_, raisedSet⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, lastSet⟩ := increaseBalance_ok lastOk
  have slashed : SlashStep electra marked { marked with slashings } :=
    ⟨.of_validators rfl rfl orderedM, rfl, rfl, rfl, rfl⟩
  have lower : SlashStep electra { marked with slashings } lowered :=
    .setBalance loweredSet orderedM
  have raise : SlashStep electra lowered raised := .setBalance raisedSet lower.1.2.2.2.2.2.2
  have pay : SlashStep electra raised last := .setBalance lastSet raise.1.2.2.2.2.2.2
  have final : t = last := by
    rw [done]
    split
    · rename_i gloas
      exact absurd gloas (Nat.not_le_of_gt early)
    · rfl
  subst final
  exact (SlashStep.trans ⟨quiet.1, quiet.2.2.1, quiet.2.2.2.1, quiet.2.2.2.2.1,
    by rw [quiet.2.1]⟩ mark).trans (slashed.trans (lower.trans (raise.trans pay)))

/-- Take a slashing that records one slashings event, at most its credit limit.

Let its registry part be a slashing step.

Then it is an operation that records that event. -/
private theorem operationReplay_slashing {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {credit debit : Nat}
    (step : ExitsOrdered s → getCurrentEpoch s < FAR_FUTURE_EPOCH → SlashStep electra s t)
    (bounded : balanceCredits s t ≤ credit)
    (slashedExit : SlashedExitAssigned s → SlashedExitAssigned t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t
      [⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] [] := by
  intro queue owned eventPosition paymentPosition callPosition reserve assignment erasure prior
    retired cover future matched ordered life started finite held fresh
  obtain ⟨registry, sameQueue, earliest, left, balanceSize⟩ := step ordered finite
  obtain ⟨kept, _, _, slot, lifecycle, size, _⟩ := id registry
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  have pending : pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) = pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, sameQueue]
  -- The registry part is read first.
  --
  -- It is read in the state with the validators after and the balances before.
  --
  -- The balance part is then a credit event with the same registry.
  let m : BeaconState preset fork := { s with validators := t.validators }
  let e : BalanceEvent preset := ⟨.slashings, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩
  let e' : BalanceEvent preset := ⟨.slashings, ⟨fork, m⟩, ⟨fork, t⟩, credit, debit⟩
  have notDeposit : BalanceSource.slashings ≠ .deposits := by decide
  have notTransfer : BalanceSource.slashings ≠ .consolidations := by decide
  have epochM : getCurrentEpoch t = getCurrentEpoch m := epoch
  have matchedT : t.validators.data.size = t.balances.data.size := by
    have : s.balances.data.size = s.validators.data.size := matched
    omega
  have matchedM : BalancesMatch m := by
    change s.balances.data.size = t.validators.data.size
    have : s.balances.data.size = s.validators.data.size := matched
    omega
  have frame := reservedFrame_refl (config := config) (checks := checks) reserve assignment erasure
  have fresh' := (prior.frame frame.2.2.1).credit_fresh (Nat.le_refl eventPosition)
  have credit : OwnedCredit eventPosition e owned (creditOwnership eventPosition e owned) :=
    ownedCredit_of_bounded reserve.1 fresh' electra notTransfer matchedT bounded
  have credit' : OwnedCredit eventPosition e' owned (creditOwnership eventPosition e' owned) :=
    ownedCredit_of_bounded reserve.1 fresh' electra notTransfer matchedT bounded
  have tokens : creditOwnership eventPosition e' owned = creditOwnership eventPosition e owned := by
    have units : ∀ i, eventCreditUnits e' i = eventCreditUnits e i := fun i => by
      simp only [eventCreditUnits, e, e', notDeposit, false_and, ↓reduceIte]
      rfl
    simp only [creditOwnership, eventCreditTokens, units]
    rfl
  have reserveM : ReserveCut x high ⟨fork, m⟩ (getCurrentEpoch s) (queue.map (·.entry)) owned :=
    reserveCut_of_registryStep registry retired life started finite reserve
  have reserveT : ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch t) (queue.map (·.entry))
      (creditOwnership eventPosition e owned) := by
    rw [epoch, ← tokens]
    exact reserveCut_credit_non_deposit (e := e') notDeposit rfl rfl matchedT fresh' credit'
      reserveM
  have event : ReservedEvent x high eventPosition paymentPosition rounding e queue queue [] []
      owned (creditOwnership eventPosition e owned) := by
    refine ⟨?_, assignment, assignment, ?_⟩
    · unfold OwnedEvent
      simp only [e, notTransfer, ↓reduceIte]
      exact ⟨trivial, trivial, .inl credit⟩
    · simp only [e, notTransfer, ↓reduceIte]
      exact ⟨reserve, reserveT⟩
  have tagged : TagEvent (config := config) e callPosition queue queue [] [] [] :=
    ⟨erasure, pending ▸ erasure, Or.inl ⟨notTransfer, rfl, rfl, rfl, rfl⟩⟩
  have coverM : EndpointCoverAll x ⟨fork, m⟩ owned := endpointCover_of_kept kept rfl rfl cover
  have futureM : FutureEffectiveCover x ⟨fork, m⟩ owned := futureCover_of_kept kept rfl future
  have coverT : EndpointCoverAll x ⟨fork, t⟩ (creditOwnership eventPosition e owned) := by
    rw [← tokens]
    exact endpointCover_nonDeposit (e := e') notDeposit rfl rfl epochM matchedM fresh' credit'
      coverM
  have futureT : FutureEffectiveCover x ⟨fork, t⟩ (creditOwnership eventPosition e owned) := by
    rw [← tokens]
    refine futureCover_credit (e := e') ⟨#[], by simp only [Array.append_empty]; rfl⟩ epochM
      matchedM ?_ fresh' credit'
      futureM
    intro j w outside read
    have inside := (Array.getElem?_eq_some_iff.mp read).1
    have before : e'.before.state.validators.data.size = t.validators.data.size := rfl
    have after : e'.after.state.validators.data.size = t.validators.data.size := rfl
    omega
  refine ⟨queue, [], creditOwnership eventPosition e owned,
    ReservedReplay.singleton_nonconsolidation notTransfer frame tagged event, reserveT,
    assignment, pending ▸ erasure, retired.lifecycle lifecycle, coverT, futureT,
    slashedExit held, ?_, by rw [earliest, left]; exact .nil _ _,
    by simp [ConsolidationCallSites]⟩
  intro tag member n fresh''
  obtain ⟨v, read, exit, assigned⟩ := fresh tag member n fresh''
  obtain ⟨w, located, kept'⟩ := lifecycle.validators _ v read
  exact ⟨w, located, (kept'.exitEpoch assigned) ▸ exit, (kept'.exitEpoch assigned) ▸ assigned⟩

/-- A proposer slashing records one slashings event with its limits read at `s`. -/
theorem reservedReplay_proposerSlashing :
    ProposerSlashingReplay (preset := preset) (config := config) (checks := checks) := by
  intro _ _ _ _ _ early delay s _ slashing _ _ limits ok
  obtain ⟨credit', debit', limits', credits, _⟩ := proposer_slashing_bounds slashing ok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (limits'.symm.trans limits))
  have held := fun prior : SlashedExitAssigned s =>
    processSlashing_slashed_exit_assigned (.inl ⟨slashing, ok⟩) delay prior
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, v, found, _, slashable, _, _, _, _, slashed⟩ := ok
  exact operationReplay_slashing
    (fun ordered finite => .slashValidator early slashed delay found slashable ordered finite)
    credits held

/-- Take the slashings of an attester slashing's indices.

Let each of them slash a slashable validator.

Then they are a slashing step. -/
private theorem SlashStep.foldlM_slashIfSlashable {fork : Fork} {electra : .pectra ≤ fork}
    (early : fork < .glamsterdam) (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (indices : List ValidatorIndex) {s t : BeaconState preset fork} {flag last : Bool}
    (ok : indices.foldlM (slashIfSlashable config) (s, flag) = .ok (t, last))
    (ordered : ExitsOrdered s) (finite : getCurrentEpoch s < FAR_FUTURE_EPOCH) :
    SlashStep electra s t :=
  (foldlM_ok_invariant
    (fun pair : BeaconState preset fork × Bool =>
      SlashStep electra s pair.1 ∧ getCurrentEpoch pair.1 < FAR_FUTURE_EPOCH)
    (fun ⟨u, _⟩ _ ⟨v, _⟩ ⟨held, bounded⟩ one => by
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at one
      obtain ⟨w, read, one⟩ := one
      have ordered := held.1.2.2.2.2.2.2
      have step : SlashStep electra u v := by
        split at one
        · rename_i slashable
          simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure,
            Except.ok.injEq, Prod.mk.injEq] at one
          obtain ⟨u', slashed, rfl, rfl⟩ := one
          exact .slashValidator early slashed delay read slashable ordered bounded
        · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at one
          obtain ⟨rfl, rfl⟩ := one
          exact .refl ordered
      have epoch : getCurrentEpoch v = getCurrentEpoch u := by
        simp only [getCurrentEpoch, step.1.2.2.2.1]
      exact ⟨held.trans step, epoch ▸ bounded⟩)
    (b := (s, flag)) ⟨.refl ordered, finite⟩ ok).1

/-- An attester slashing records one slashings event with its limits read at `s`. -/
theorem reservedReplay_attesterSlashing :
    AttesterSlashingReplay (preset := preset) (config := config) (checks := checks) := by
  intro _ _ _ _ _ early delay s _ slashing _ _ limits ok
  obtain ⟨credit', debit', limits', credits, _⟩ := attester_slashing_bounds slashing ok
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (limits'.symm.trans limits))
  have held := fun prior : SlashedExitAssigned s =>
    processSlashing_slashed_exit_assigned (.inr ⟨slashing, ok⟩) delay prior
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨u, flag⟩, folded, _, _, rfl⟩ := ok
  exact operationReplay_slashing
    (fun ordered finite => .foldlM_slashIfSlashable early delay _ folded ordered finite) credits
    held

end

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
