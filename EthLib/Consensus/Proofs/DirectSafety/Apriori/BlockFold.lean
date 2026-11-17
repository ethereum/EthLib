module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.SlotReplay

/-!
# The replay of a block

The operations of a block compose into one replay.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section

open Cryptography.Bls

/-! ## The block fold: composition and the carried pieces -/

/-- Take an operation that keeps the registry, the balances and the slot.

Let it also keep the pending consolidations and the consolidation churn.

It does so through silent frame steps.

Then it records nothing. -/
private theorem operationReplay_carry {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork}
    (path : FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩)
    (registry : t.validators = s.validators) (balances : t.balances = s.balances)
    (slot : t.slot = s.slot) (pending : t.pendingConsolidations = s.pendingConsolidations)
    (earliest : t.earliestConsolidationEpoch = s.earliestConsolidationEpoch)
    (consume : t.consolidationBalanceToConsume = s.consolidationBalanceToConsume) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] :=
  operationReplay_quiet path fun ordered _ =>
    ⟨RegistryStep.of_validators (congrArg (·.data) registry) slot ordered, balances, pending,
      congrFun earliest electra, congrFun consume electra,
      SlashedExitAssigned.of_validators_eq (congrArg (·.data) registry)⟩

/-- The deposit requests of a block record nothing and are one frame. -/
private theorem operationReplay_depositRequests (x : ForkedBeaconState preset) (high : Nat)
    (rounding : Nat → Nat) {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} (requests : List DepositRequest)
    (ok : requests.foldlM (processDepositRequest · electra ·) s = .ok t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] := by
  obtain ⟨registry, balances, slot, pending, earliest, consume, path⟩ :=
    depositRequests_kept requests ok
  exact operationReplay_carry path registry balances slot pending earliest consume

/-- An operation's replay for every input ownership that meets `guard`. -/
private def GuardedReplay (guard : Ownership → Prop) (x : ForkedBeaconState preset)
    (high : Nat) (rounding : Nat → Nat) {fork : Fork} (electra : .pectra ≤ fork)
    (s t : BeaconState preset fork) (added : List (BalanceEvent preset))
    (sites : List (ForkedBeaconState preset)) : Prop :=
  ∀ (queue : List TaggedEntry) (owned : Ownership)
    (eventPosition paymentPosition callPosition : Nat), guard owned →
    OperationReplayAt (config := config) (checks := checks) x high rounding electra s t added
      sites queue owned eventPosition paymentPosition callPosition

private theorem OperationReplay.guarded {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {electra : .pectra ≤ fork}
    {s t : BeaconState preset fork} {added : List (BalanceEvent preset)}
    {sites : List (ForkedBeaconState preset)} (guard : Ownership → Prop)
    (replay : OperationReplay (config := config) (checks := checks) x high rounding electra s t
      added sites) :
    GuardedReplay (config := config) (checks := checks) guard x high rounding electra s t added
      sites :=
  fun queue owned eventPosition paymentPosition callPosition _ =>
    replay queue owned eventPosition paymentPosition callPosition

/-- Two operations in sequence replay as one.

The run facts of the menu carry from the first operation's input to its output.

The guard holds of every ownership whose originals are below one that meets it. -/
private theorem GuardedReplay.append {guard : Ownership → Prop} {x : ForkedBeaconState preset}
    {high : Nat} {rounding : Nat → Nat} {fork : Fork} {electra : .pectra ≤ fork}
    {s m t : BeaconState preset fork} {first second : List (BalanceEvent preset)}
    {firstSites secondSites : List (ForkedBeaconState preset)}
    (one : GuardedReplay (config := config) (checks := checks) guard x high rounding electra s m
      first firstSites)
    (two : GuardedReplay (config := config) (checks := checks) guard x high rounding electra m t
      second secondSites)
    (lower : ∀ o o' : Ownership, guard o → (∀ i, o'.original i ≤ o.original i) → guard o')
    (epoch : getCurrentEpoch m = getCurrentEpoch s)
    (facts : BalancesMatch s → ExitsOrdered s → RegistryLifecycle x.state s →
      BalancesMatch m ∧ ExitsOrdered m ∧ RegistryLifecycle x.state m) :
    GuardedReplay (config := config) (checks := checks) guard x high rounding electra s t
      (first ++ second) (firstSites ++ secondSites) := by
  intro queue owned eventPosition paymentPosition callPosition held reserve assignment erasure
    prior retired cover future matched exits life start finite slashed fresh
  obtain ⟨queue₁, calls₁, owned₁, replay₁, reserve₁, assignment₁, erasure₁, retired₁, cover₁,
      future₁, slashed₁, fresh₁, trace₁, sites₁⟩ :=
    one queue owned eventPosition paymentPosition callPosition held reserve assignment erasure
      prior retired cover future matched exits life start finite slashed fresh
  obtain ⟨matched₁, exits₁, life₁⟩ := facts matched exits life
  have prior₁ := replay₁.counters prior
  simp only [List.length_nil, Nat.add_zero] at prior₁
  have held₁ := lower owned owned₁ held replay₁.counters_original.2.2.1
  obtain ⟨queue₂, calls₂, owned₂, replay₂, reserve₂, assignment₂, erasure₂, retired₂, cover₂,
      future₂, slashed₂, fresh₂, trace₂, sites₂⟩ :=
    two queue₁ owned₁ (eventPosition + first.length) paymentPosition
      (callPosition + calls₁.length) held₁ (epoch ▸ reserve₁) assignment₁ erasure₁ prior₁
      retired₁ cover₁ future₁ matched₁ exits₁ life₁ (epoch ▸ start) (epoch ▸ finite)
      slashed₁ fresh₁
  refine ⟨queue₂, calls₁ ++ calls₂, owned₂, ?_, reserve₂, assignment₂, erasure₂, retired₂,
    cover₂, future₂, slashed₂, fresh₂, ?_, ?_⟩
  · have joined := replay₁.append (rest := second) (restPayments := [])
      (restAllocations := []) (by simpa only [List.length_nil, Nat.add_zero] using replay₂)
    simpa only [List.append_nil] using joined
  · rw [List.map_append]
    exact trace₁.append trace₂
  · intro called member
    rcases List.mem_append.mp member with inFirst | inSecond
    · obtain ⟨site, at₁, rest⟩ := sites₁ called inFirst
      exact ⟨site, List.mem_append_left _ at₁, rest⟩
    · obtain ⟨site, at₂, rest⟩ := sites₂ called inSecond
      exact ⟨site, List.mem_append_right _ at₂, rest⟩

/-- An operation's replay stays valid with more sites. -/
private theorem GuardedReplay.sites_mono {guard : Ownership → Prop}
    {x : ForkedBeaconState preset} {high : Nat} {rounding : Nat → Nat} {fork : Fork}
    {electra : .pectra ≤ fork} {s t : BeaconState preset fork} {added : List (BalanceEvent preset)}
    {sites wider : List (ForkedBeaconState preset)}
    (replay : GuardedReplay (config := config) (checks := checks) guard x high rounding electra s
      t added sites)
    (included : ∀ site ∈ sites, site ∈ wider) :
    GuardedReplay (config := config) (checks := checks) guard x high rounding electra s t added
      wider := by
  intro queue owned eventPosition paymentPosition callPosition held reserve assignment erasure
    prior retired cover future matched exits life start finite slashed fresh
  obtain ⟨queue', calls, owned', replayed, reserve', assignment', erasure', retired', cover',
      future', slashed', fresh', trace, located⟩ :=
    replay queue owned eventPosition paymentPosition callPosition held reserve assignment
      erasure prior retired cover future matched exits life start finite slashed fresh
  refine ⟨queue', calls, owned', replayed, reserve', assignment', erasure', retired', cover',
    future', slashed', fresh', trace, ?_⟩
  intro called member
  obtain ⟨site, inside, rest⟩ := located called member
  exact ⟨site, included site inside, rest⟩

/-- The block header records nothing. -/
private theorem operationReplay_header {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} {block : BeaconBlock preset fork}
    (ok : processBlockHeader s block = .ok t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] := by
  have path : FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ := .cons (.header ok) .nil
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ok
  exact operationReplay_carry path rfl rfl rfl rfl rfl rfl

/-- The randao reveal records nothing. -/
private theorem operationReplay_randao {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (ok : processRandao config checks s body = .ok t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] := by
  have path : FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ := .cons (.randao ok) .nil
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ok
  exact operationReplay_carry path rfl rfl rfl rfl rfl rfl

/-- The eth1 vote records nothing. -/
private theorem operationReplay_eth1 {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} {body : BeaconBlockBody preset fork} {early : fork < .hegota}
    (ok : processEth1Data early s body = .ok t) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t [] [] := by
  have path : FramePath config checks ⟨fork, s⟩ ⟨fork, t⟩ := .cons (.eth1 early ok) .nil
  have same := (processEth1Data_eq ok).2.2
  exact operationReplay_carry path (congrArg (·.validators) same) (congrArg (·.balances) same)
    (congrArg (·.slot) same) (congrArg (·.pendingConsolidations) same)
    (congrArg (·.earliestConsolidationEpoch) same)
    (congrArg (·.consolidationBalanceToConsume) same)

/-- The execution part of a block keeps the slot and the pending consolidations.

It also keeps the consolidation churn.

Its withdrawals only lower balances and move withdrawal indices. -/
private theorem processBlockExecution_consolidations {fork : Fork}
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t) :
    t.pendingConsolidations = s.pendingConsolidations ∧
      t.earliestConsolidationEpoch = s.earliestConsolidationEpoch ∧
      t.consolidationBalanceToConsume = s.consolidationBalanceToConsume ∧ t.slot = s.slot := by
  let R := fun (a b : BeaconState preset fork) =>
    b.pendingConsolidations = a.pendingConsolidations ∧
      b.earliestConsolidationEpoch = a.earliestConsolidationEpoch ∧
      b.consolidationBalanceToConsume = a.consolidationBalanceToConsume ∧ b.slot = a.slot
  have refl : ∀ a, R a a := fun _ => ⟨rfl, rfl, rfl, rfl⟩
  have trans : ∀ {a b c}, R a b → R b c → R a c := fun one two =>
    ⟨two.1.trans one.1, two.2.1.trans one.2.1, two.2.2.1.trans one.2.2.1,
      two.2.2.2.trans one.2.2.2⟩
  refine processBlockExecution_of R refl trans ?_ ?_ ?_ ok
  · intro a b body' execution paid
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact refl _
  · intro a b gloas _ _
    exact absurd gloas (Nat.not_le_of_lt early)
  · intro a b capella payload withdrawn
    obtain ⟨expected, _, _, applied⟩ := processWithdrawals_expected early withdrawn
    refine applyExpectedWithdrawals_of_updates R refl trans ?_ (fun _ _ => refl _)
      (fun _ _ => refl _) (fun _ _ => refl _) (fun _ _ => refl _) (fun _ _ => refl _)
      (fun _ _ _ => refl _) applied
    intro c d w one
    unfold applyWithdrawal at one
    split at one
    · rename_i gloas
      exact absurd gloas.1 (Nat.not_le_of_lt early)
    · obtain ⟨_, rfl⟩ := decreaseBalance_eq_ok_iff.mp one
      exact refl _

/-- The execution part of a block records one withdrawals event, with no credit. -/
private theorem operationReplay_execution {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) {s t : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork} {debit : Nat}
    (ok : processBlockExecution config checks engine s body bellatrix = .ok t)
    (bounded : (⟨.withdrawals, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩ : BalanceEvent preset).credits ≤
      0) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t
      [⟨.withdrawals, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩] [] := by
  intro queue owned eventPosition paymentPosition callPosition reserve assignment erasure _
    retired cover future _ _ _ _ _ slashed fresh
  let e : BalanceEvent preset := ⟨.withdrawals, ⟨fork, s⟩, ⟨fork, t⟩, 0, debit⟩
  have registry := processBlockExecution_validators ok
  obtain ⟨pending, earliest, consume, slot⟩ := processBlockExecution_consolidations early ok
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  have notTransfer : e.source ≠ .consolidations := fun same => by cases same
  have queueSame : pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) =
      pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, electra, ↓reduceDIte, pending]
  have decreases : ∀ i, actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt ⟨fork, s⟩ i := by
    intro i
    by_cases inside : i < t.balances.data.size
    · have single := Finset.single_le_sum
        (fun j (_ : j ∈ Finset.range t.balances.data.size) =>
          Nat.zero_le (actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) j -
            actualBalanceAt ⟨fork, s⟩ j))
        (Finset.mem_range.mpr inside)
      change actualBalanceAt (⟨fork, t⟩ : ForkedBeaconState preset) i -
        actualBalanceAt ⟨fork, s⟩ i ≤ e.credits at single
      have zero : e.credits ≤ 0 := bounded
      omega
    · simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt inside)]
  have tagged : TagEvent (config := config) e callPosition queue queue [] [] [] :=
    ⟨erasure, queueSame ▸ erasure, Or.inl ⟨notTransfer, rfl, rfl, rfl, rfl⟩⟩
  have owned' := reservedEvent_zero_credit (eventPosition := eventPosition)
    (paymentPosition := paymentPosition) (e := e) notTransfer rfl
    (congrArg (·.data) registry) epoch bounded rfl reserve assignment
  have frame := reservedFrame_refl (config := config) (checks := checks)
    (rounding := rounding) reserve assignment erasure
  have replay := ReservedReplay.singleton_nonconsolidation (callPosition := callPosition)
    notTransfer frame tagged owned'
  have reserveT : ReserveCut x high ⟨fork, t⟩ (getCurrentEpoch t) (queue.map (·.entry))
      owned := by
    rw [epoch]
    exact reserveCut_balance_decrease (u := ⟨fork, s⟩) (v := ⟨fork, t⟩) rfl
      (congrArg (·.data) registry) decreases reserve
  refine ⟨queue, [], owned, replay, reserveT, assignment, queueSame ▸ erasure, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa only [RetiredActivated, registry] using retired
  · apply endpointCover_mono (u := ⟨fork, s⟩) ?_ (fun _ => Nat.le_refl _) cover
    intro i w found clean notExited current
    have foundS : s.validators.data[i]? = some w := by
      change t.validators.data[i]? = some w at found
      rwa [registry] at found
    exact ⟨w, foundS, clean, notExited, epoch ▸ current, rfl,
      min_le_min (decreases i) (Nat.le_refl _)⟩
  · exact futureCover_records registry (UInt64.le_of_eq epoch.symm) future
  · simpa only [SlashedExitAssigned, registry] using slashed
  · simpa only [FreshExits, registry] using fresh
  · rw [earliest, consume]
    exact .nil _ _
  · intro called member
    cases member

/-- Take an operation that keeps the registry, the slot and the pending consolidations.

Let it also keep the consolidation churn and record one bounded credit, not a deposit.

Then it replays as that event.

The ownership grows by the event's credit tokens. -/
private theorem operationReplay_credit {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} {source : BalanceSource} {credit debit : Nat}
    (notDeposit : source ≠ .deposits) (notTransfer : source ≠ .consolidations)
    (registry : t.validators = s.validators) (slot : t.slot = s.slot)
    (pending : t.pendingConsolidations = s.pendingConsolidations)
    (earliest : t.earliestConsolidationEpoch = s.earliestConsolidationEpoch)
    (consume : t.consolidationBalanceToConsume = s.consolidationBalanceToConsume)
    (sizes : BalancesMatch s → BalancesMatch t)
    (bounded : (⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ : BalanceEvent preset).credits ≤
      credit) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t
      [⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] [] := by
  intro queue owned eventPosition paymentPosition callPosition reserve assignment erasure prior
    retired cover future matchedS _ _ _ _ slashed fresh
  let e : BalanceEvent preset := ⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩
  have epoch : getCurrentEpoch t = getCurrentEpoch s := by simp only [getCurrentEpoch, slot]
  have queueSame : pendingQueue (⟨fork, t⟩ : ForkedBeaconState preset) =
      pendingQueue ⟨fork, s⟩ := by
    simp only [pendingQueue, electra, ↓reduceDIte, pending]
  have matched : t.validators.data.size = t.balances.data.size := (sizes matchedS).symm
  have frame := reservedFrame_refl (config := config) (checks := checks)
    (rounding := rounding) reserve assignment erasure
  obtain ⟨tagged, event⟩ := reservedCredit_facts (e := e) (callPosition := callPosition)
    electra notDeposit notTransfer rfl (congrArg (·.data) registry) epoch matched queueSame
    bounded frame prior
  have replay := ReservedReplay.singleton_nonconsolidation notTransfer frame tagged event
  have fresh' := prior.credit_fresh (Nat.le_refl eventPosition)
  have owned' := ownedCredit_of_bounded (e := e) reserve.1 fresh' electra notTransfer matched
    bounded
  have reserveT := event.2.2.2
  simp only [e, notTransfer, ↓reduceIte] at reserveT
  refine ⟨queue, [], _, replay, reserveT.2, event.2.2.1, queueSame ▸ erasure, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simpa only [RetiredActivated, registry, creditOwnership] using retired
  · exact endpointCover_nonDeposit (e := e) notDeposit rfl (congrArg (·.data) registry) epoch
      matchedS fresh' owned' cover
  · refine futureCover_credit (e := e) ⟨#[], by
      change t.validators.data = s.validators.data ++ #[]
      rw [registry, Array.append_empty]⟩ epoch matchedS ?_ fresh' owned' future
    intro j w outside found
    have inside : j < t.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
    change s.validators.data.size ≤ j at outside
    have same : t.validators.data.size = s.validators.data.size := by rw [registry]
    omega
  · simpa only [SlashedExitAssigned, registry] using slashed
  · simpa only [FreshExits, registry] using fresh
  · rw [earliest, consume]
    exact .nil _ _
  · intro called member
    cases member

/-- A recorded fold replays as one operation when each of its steps does.

Each step records one event at its input, and the run facts of the menu carry across it.

A step may read the items before it, which reach its input from the fold's start `start`. -/
private theorem GuardedReplay.recordFold {guard : Ownership → Prop}
    {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} {electra : .pectra ≤ fork} {α : Type}
    {source : BalanceSource} {wide : List (ForkedBeaconState preset)}
    {limits : α → BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : α → BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {all : List α} {start : BeaconState preset fork}
    (step : ∀ (done rest : List α) (item : α) (a b : BeaconState preset fork)
      (credit debit : Nat), all = done ++ item :: rest →
      done.foldlM (fun a i => action i a) start = .ok a →
      limits item a = .ok (credit, debit) → action item a = .ok b →
      (⟨source, ⟨fork, a⟩, ⟨fork, b⟩, credit, debit⟩ : BalanceEvent preset).credits ≤ credit →
      GuardedReplay (config := config) (checks := checks) guard x high rounding electra a b
        [⟨source, ⟨fork, a⟩, ⟨fork, b⟩, credit, debit⟩] wide ∧
      getCurrentEpoch b = getCurrentEpoch a ∧
      (BalancesMatch a → ExitsOrdered a → RegistryLifecycle x.state a →
        BalancesMatch b ∧ ExitsOrdered b ∧ RegistryLifecycle x.state b))
    (lower : ∀ o o' : Ownership, guard o → (∀ i, o'.original i ≤ o.original i) → guard o') :
    ∀ (items done : List α) (s t : BeaconState preset fork)
      (prior events : List (BalanceEvent preset)), all = done ++ items →
      done.foldlM (fun a i => action i a) start = .ok s →
      items.foldlM (fun pre item => recordBalance source (limits item) (action item) pre)
        (s, prior) = .ok (t, events) →
      EventsBounded events →
      ∃ added, events = prior ++ added ∧
        GuardedReplay (config := config) (checks := checks) guard x high rounding electra s t
          added wide ∧ getCurrentEpoch t = getCurrentEpoch s ∧
        (BalancesMatch s → ExitsOrdered s → RegistryLifecycle x.state s →
          BalancesMatch t ∧ ExitsOrdered t ∧ RegistryLifecycle x.state t) := by
  intro items
  induction items with
  | nil =>
    intro done s t prior events _ _ ok _
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    refine ⟨[], by simp, ?_, rfl, fun a b c => ⟨a, b, c⟩⟩
    exact ((operationReplay_carry .nil rfl rfl rfl rfl rfl rfl).guarded guard).sites_mono
      (by simp)
  | cons item items ih =>
    intro done s t prior events split reached ok bounded
    simp only [List.foldlM_cons, bind_ok_iff] at ok
    obtain ⟨⟨m, middle⟩, first, rest⟩ := ok
    simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at first
    obtain ⟨⟨credit, debit⟩, limitsOk, post, actionOk, same⟩ := first
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    let event : BalanceEvent preset := ⟨source, ⟨fork, s⟩, ⟨fork, post⟩, credit, debit⟩
    have reachedNext : (done ++ [item]).foldlM (fun a i => action i a) start = .ok post := by
      rw [List.foldlM_append, reached]
      simp only [List.foldlM_cons, List.foldlM_nil, bind_ok_iff, pure, Except.pure]
      exact ⟨s, rfl, post, actionOk, rfl⟩
    obtain ⟨added, rfl, replay, epoch, facts⟩ := ih (done ++ [item]) post t _ events
      (by simp [split]) reachedNext rest bounded
    have own := bounded event (by simp [event])
    obtain ⟨single, epoch₁, facts₁⟩ := step done items item s post credit debit split reached
      limitsOk actionOk own.1
    refine ⟨event :: added, by simp [event], ?_, epoch.trans epoch₁, ?_⟩
    · simpa only [List.singleton_append] using
        (single.append replay lower epoch₁ facts₁).sites_mono (fun site member => by
          rcases List.mem_append.mp member with inside | inside <;> exact inside)
    · intro matched exits life
      obtain ⟨matched₁, exits₁, life₁⟩ := facts₁ matched exits life
      exact facts matched₁ exits₁ life₁

/-- Before Gloas an attestation changes only participation flags and the proposer's balance. -/
private theorem processAttestation_kept {fork : Fork} (early : fork < .glamsterdam)
    {s t : BeaconState preset fork} {parentSlot : Slot} {attestation : Attestation preset fork}
    (altair : .altair ≤ fork)
    (ok : processAttestation config checks s parentSlot attestation = .ok t) :
    t.validators = s.validators ∧ t.slot = s.slot ∧
      t.pendingConsolidations = s.pendingConsolidations ∧
      t.earliestConsolidationEpoch = s.earliestConsolidationEpoch ∧
      t.consolidationBalanceToConsume = s.consolidationBalanceToConsume := by
  unfold processAttestation at ok
  simp only [altair, ↓reduceDIte] at ok
  unfold processAttestationAltair at ok
  simp only [bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := ok
  split at final
  · rename_i gloas
    exact absurd gloas (Nat.not_le_of_lt early)
  · cases final
    obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
    obtain ⟨_, rfl⟩ := setBalance_ok set
    unfold setEpochParticipation
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The attestations of a block replay as one operation, one rewards event each. -/
private theorem guardedReplay_attestations {guard : Ownership → Prop}
    {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    (early : fork < .glamsterdam) (parentSlot : Slot) (credit : Attestation preset fork →
      BeaconState preset fork → Except TransitionError (Nat × Nat))
    (lower : ∀ o o' : Ownership, guard o → (∀ i, o'.original i ≤ o.original i) → guard o') :
    ∀ (items : List (Attestation preset fork)) (s t : BeaconState preset fork)
      (prior events : List (BalanceEvent preset)),
      items.foldlM (fun pre item => recordBalance .rewards (credit item)
        (processAttestation config checks · parentSlot item) pre) (s, prior) = .ok (t, events) →
      EventsBounded events →
      ∃ added, events = prior ++ added ∧
        GuardedReplay (config := config) (checks := checks) guard x high rounding electra s t
          added [] ∧ getCurrentEpoch t = getCurrentEpoch s ∧
        (BalancesMatch s → ExitsOrdered s → RegistryLifecycle x.state s →
          BalancesMatch t ∧ ExitsOrdered t ∧ RegistryLifecycle x.state t) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  intro items s t prior events ok bounded
  refine GuardedReplay.recordFold (all := items) (start := s) ?_ lower items [] s t prior events
    (by simp) rfl ok bounded
  intro _ _ item a b credit' debit _ _ _ ok bounded
  obtain ⟨registry, slot, pending, earliest, consume⟩ := processAttestation_kept early altair ok
  have frame := frame_processAttestation ok
  refine ⟨(operationReplay_credit electra (fun same => by cases same)
      (fun same => by cases same) registry slot pending earliest consume frame.balancesMatch
      bounded).guarded guard,
    by simp only [getCurrentEpoch, slot], ?_⟩
  intro matched exits life
  exact ⟨frame.balancesMatch matched, frame.exitsOrdered exits,
    life.trans (registryLifecycle_processAttestation ok)⟩

/-- The sync aggregate records one sync event. -/
private theorem operationReplay_sync {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork)
    {s t : BeaconState preset fork} {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    {credit debit : Nat} (ok : processSyncAggregate config checks s altair aggregate = .ok t)
    (bounded : (⟨.sync, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩ : BalanceEvent preset).credits ≤
      credit) :
    OperationReplay (config := config) (checks := checks) x high rounding electra s t
      [⟨.sync, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] [] := by
  have frame := frame_processSyncAggregate ok
  obtain ⟨_, rfl⟩ := processSyncAggregate_eq ok
  exact operationReplay_credit electra (fun same => by cases same) (fun same => by cases same)
    rfl rfl rfl rfl rfl frame.balancesMatch bounded

/-- One recorded operation: its limits at the input, its action, and one appended event. -/
private theorem recordBalance_single {fork : Fork} {source : BalanceSource}
    {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
    {s t : BeaconState preset fork} {prior events : List (BalanceEvent preset)}
    (ok : recordBalance source limits action (s, prior) = .ok (t, events)) :
    ∃ credit debit, limits s = .ok (credit, debit) ∧ action s = .ok t ∧
      events = prior ++ [⟨source, ⟨fork, s⟩, ⟨fork, t⟩, credit, debit⟩] := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨⟨credit, debit⟩, limitsOk, post, actionOk, same⟩ := ok
  simp only [Prod.mk.injEq] at same
  obtain ⟨rfl, rfl⟩ := same
  exact ⟨credit, debit, limitsOk, actionOk, rfl⟩

/-- A recorded fold runs the plain fold of its actions. -/
private theorem recordFold_plain {fork : Fork} {α : Type} {source : BalanceSource}
    {limits : α → BeaconState preset fork → Except TransitionError (Nat × Nat)}
    {action : α → BeaconState preset fork → Except TransitionError (BeaconState preset fork)} :
    ∀ (items : List α) (s t : BeaconState preset fork) (prior events : List (BalanceEvent preset)),
      items.foldlM (fun pre item => recordBalance source (limits item) (action item) pre)
        (s, prior) = .ok (t, events) →
      items.foldlM (fun a i => action i a) s = .ok t := by
  intro items
  induction items with
  | nil =>
    intro s t prior events ok
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
    rw [ok.1]
    rfl
  | cons item items ih =>
    intro s t prior events ok
    simp only [List.foldlM_cons, bind_ok_iff] at ok ⊢
    obtain ⟨⟨m, middle⟩, first, rest⟩ := ok
    obtain ⟨_, _, _, actionOk, _⟩ := recordBalance_single first
    exact ⟨m, actionOk, ih m t middle events rest⟩

/-- The block's assignment bound holds of every ownership with lower originals. -/
private theorem blockAssigned_lower {rounding : Nat → Nat} {f h : Fork}
    {m : BeaconState preset f} {n : BeaconState preset h} {o o' : Ownership}
    (held : BlockAssigned rounding m n o) (lower : ∀ i, o'.original i ≤ o.original i) :
    BlockAssigned rounding m n o' :=
  fun i v w found later unset assigned => (lower i).trans (held i v w found later unset assigned)

/-- One consolidation request of a block, under the block's assignment bound.

Its request bound comes from the block's bound.

It goes through the lifecycle and the kept effective balances from the block input to the request.

It then goes through the lifecycle from the request to the block output.

An accepted request reads the churn at its input, which is a site of the block. -/
private theorem guardedReplay_consolidationRequest {x : ForkedBeaconState preset} {high : Nat}
    {rounding : Nat → Nat} {fork : Fork} (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (compounding : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA)
    {S T a b : BeaconState preset fork} {request : ConsolidationRequest}
    {wide : List (ForkedBeaconState preset)}
    (ok : processConsolidationRequest config a electra request = .ok b)
    (lifeSA : RegistryLifecycle S a) (keptSA : EffectiveKept S a)
    (lifeBT : RegistryLifecycle b T)
    (sizeX : x.state.validators.data.size ≤ S.validators.data.size)
    (siteIn : (b.pendingConsolidations electra).data.size ≠
      (a.pendingConsolidations electra).data.size → (⟨fork, a⟩ : ForkedBeaconState preset) ∈ wide) :
    GuardedReplay (config := config) (checks := checks) (BlockAssigned rounding S T) x high
      rounding electra a b
      [⟨.excess, ⟨fork, a⟩, ⟨fork, b⟩, 0,
        match findValidatorByPubkey a request.sourcePubkey with
        | none => 0
        | some i => actualBalanceAt ⟨fork, a⟩ i.val - preset.MIN_ACTIVATION_BALANCE.toNat⟩]
      wide := by
  intro queue owned eventPosition paymentPosition callPosition held reserve assignment erasure
    _ retired cover future _ _ life _ _ slashed fresh
  have frame := reservedFrame_refl (config := config) (checks := checks) (rounding := rounding)
    reserve assignment erasure
  have assigned := requestAssigned_of_block held lifeSA keptSA lifeBT (fun _ => Nat.le_refl _)
    reserve sizeX
  have callOf := (consolidationQueue_dispatch (config := config) (checks := checks) electra early
    (s := a) (t := b)).2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨queue', calls', owned', replay, frameT, retiredT, coverT, futureT, trace, sitesA,
      freshTags, grow⟩ :=
    reservedReplay_consolidationRequest (eventPosition := eventPosition)
      (paymentPosition := paymentPosition) (callPosition := callPosition) frame retired cover
      future life electra ok compounding slashed assigned delay callOf
      (fun _ switch e before after notTransfer => reservedReplay_switchToCompounding electra
        switch frame retired cover future compounding e before after notTransfer)
  obtain ⟨_, _, _, _, assignmentT, _, erasureT, _, reserveT⟩ := frameT
  refine ⟨queue', calls', owned', replay, reserveT, assignmentT, erasureT, retiredT, coverT,
    futureT, processConsolidationRequest_slashed_exit_assigned compounding ok delay slashed, ?_,
    trace electra, ?_⟩
  · intro tag member n isFresh
    by_cases old : tag ∈ queue
    · obtain ⟨v, found, epoch, assignedExit⟩ := fresh tag old n isFresh
      obtain ⟨w, foundB, kept⟩ :=
        (registryLifecycle_processConsolidationRequest ok).validators _ v found
      have same := kept.exitEpoch assignedExit
      exact ⟨w, foundB, same ▸ epoch, same ▸ assignedExit⟩
    · obtain ⟨_, v, found, epoch, assignedExit⟩ := freshTags tag member old
      exact ⟨v, found, epoch, assignedExit⟩
  · intro called member
    rcases grow with empty | grows
    · rw [empty] at member
      cases member
    · obtain ⟨site, inA, rest⟩ := sitesA called member
      rw [List.mem_singleton] at inA
      subst inA
      exact ⟨_, siteIn grows, rest⟩

/-- A fold whose steps keep the lifecycle and the effective balances keeps both. -/
private theorem keptFold {fork : Fork} {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ a item b, step a item = .ok b → RegistryLifecycle a b ∧ EffectiveKept a b)
    {items : List α} {a b : BeaconState preset fork} (ok : items.foldlM step a = .ok b) :
    RegistryLifecycle a b ∧ EffectiveKept a b :=
  foldlM_ok_invariant (fun u => RegistryLifecycle a u ∧ EffectiveKept a u)
    (fun u item u' held one => by
      obtain ⟨life, kept⟩ := each u item u' one
      exact ⟨held.1.trans life, effectiveKept_trans held.2 kept held.1.size_le⟩)
    ⟨.refl a, effectiveKept_refl a⟩ ok

private theorem keptTrans {f : Fork} {a b c : BeaconState preset f}
    (one : RegistryLifecycle a b ∧ EffectiveKept a b)
    (two : RegistryLifecycle b c ∧ EffectiveKept b c) :
    RegistryLifecycle a c ∧ EffectiveKept a c :=
  ⟨one.1.trans two.1, effectiveKept_trans one.2 two.2 one.1.size_le⟩

private theorem keptSame {f : Fork} {a b : BeaconState preset f}
    (same : b.validators = a.validators) : RegistryLifecycle a b ∧ EffectiveKept a b :=
  ⟨.of_data (congrArg (·.data) same), effectiveKept_data (congrArg (·.data) same)⟩

/-- The replay of a block is one operation under the block's assignment bound. -/
theorem blockReplay_proved :
    BlockReplay (preset := preset) (config := config) (checks := checks) := by
  intro x high rounding fork electra early delay compounding s t engine signed due ok events
    replayed
  have altair : Fork.altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : Fork.bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have capella : Fork.shapella ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ Fork.glamsterdam ≤ fork := Nat.not_le_of_lt early
  have whole := Step.balanceEvents_block (config := config) (checks := checks) early replayed
  have replay := whole
  simp only [blockBalanceReplay, altair, bellatrix, electra, capella, ↓reduceDIte, bind_ok_iff,
    carryBalance, pure, Except.pure, ensure_ok_iff, Except.ok.injEq] at replay
  obtain ⟨_, ⟨headed, headerOk, rfl⟩, ⟨executed, execEvents⟩, executionRec, _,
    ⟨revealed, randaoOk, rfl⟩, _, ⟨voted, eth1Ok, rfl⟩, expected, expectedOk, _, countOk,
    ⟨proposed, propEvents⟩, proposedRec, ⟨slashedS, slashEvents⟩, slashedRec,
    ⟨attested, attEvents⟩, attestedRec, ⟨deposited, depEvents⟩, depositedRec, _,
    ⟨exited, exitedOk, rfl⟩, _, ⟨changed, changedOk, rfl⟩, _, ⟨requested, requestedOk, rfl⟩, _,
    ⟨withdrawn, withdrawnOk, rfl⟩, ⟨consolidated, consEvents⟩, consolidatedRec, syncRec⟩ := replay
  -- The plain folds of the recorded operations.
  have proposedOk := recordFold_plain _ _ _ _ _ proposedRec
  have slashedOk := recordFold_plain _ _ _ _ _ slashedRec
  have attestedOk := recordFold_plain _ _ _ _ _ attestedRec
  have depositedOk := recordFold_plain _ _ _ _ _ depositedRec
  have consolidatedOk := recordFold_plain _ _ _ _ _ consolidatedRec
  dsimp only at randaoOk eth1Ok expectedOk exitedOk changedOk requestedOk withdrawnOk
  obtain ⟨wCredit, wDebit, wLimits, executionOk, execEq⟩ := recordBalance_single executionRec
  obtain ⟨syncCredit, syncDebit, _, syncOk, syncEq⟩ := recordBalance_single syncRec
  simp only [bind_ok_iff, Except.ok.injEq, Prod.mk.injEq] at wLimits
  obtain ⟨_, _, rfl, _⟩ := wLimits
  -- The guard is the block's assignment bound; it holds of every ownership with lower originals.
  let G := BlockAssigned rounding s t
  have lower : ∀ o o' : Ownership, G o → (∀ i, o'.original i ≤ o.original i) → G o' :=
    fun _ _ held below => blockAssigned_lower held below
  let wide := (Step.block (checks := checks) engine signed due ok).consolidationSites
  -- The lifecycle and the kept effective balances from the block input to the requests.
  have kHead : RegistryLifecycle s withdrawn ∧ EffectiveKept s withdrawn := by
    have k1 : RegistryLifecycle s headed ∧ EffectiveKept s headed := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
      exact keptSame rfl
    have k2 := keptSame (processBlockExecution_validators executionOk)
    have k3 : RegistryLifecycle executed revealed ∧ EffectiveKept executed revealed := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
      exact keptSame rfl
    have k4 : RegistryLifecycle revealed voted ∧ EffectiveKept revealed voted := by
      have same := (processEth1Data_eq eth1Ok).2.2
      exact keptSame (congrArg (·.validators) same)
    have k5 := keptFold (fun _ _ _ one => ⟨registryLifecycle_processProposerSlashing one,
      effectiveKept_proposerSlashing one⟩) proposedOk
    have k6 := keptFold (fun _ _ _ one => ⟨registryLifecycle_processAttesterSlashing one,
      effectiveKept_attesterSlashing one⟩) slashedOk
    have k7 := keptFold (fun _ _ _ one => keptSame (processAttestation_registry one).1) attestedOk
    have k8 := keptFold (fun _ _ _ one => ⟨registryLifecycle_processDeposit one,
      effectiveKept_processDeposit one⟩) depositedOk
    have k9 := keptFold (fun _ _ _ one => ⟨registryLifecycle_processVoluntaryExit one,
      effectiveKept_voluntaryExit one⟩) (by simpa only [← Array.foldlM_toList] using exitedOk)
    have k10 : RegistryLifecycle exited changed ∧ EffectiveKept exited changed := by
      simp only [processBlsToExecutionChanges, capella, ↓reduceDIte] at changedOk
      exact keptFold (fun _ _ _ one => ⟨registryLifecycle_processBlsToExecutionChange one,
        effectiveKept_blsChange one⟩) (by simpa only [← Array.foldlM_toList] using changedOk)
    have k11 := keptFold (fun _ _ _ one => ⟨registryLifecycle_processDepositRequest one,
      effectiveKept_depositRequest one⟩) (by simpa only [← Array.foldlM_toList] using requestedOk)
    have k12 := keptFold (fun _ _ _ one => ⟨registryLifecycle_processWithdrawalRequest one,
      effectiveKept_withdrawalRequest one⟩)
      (by simpa only [← Array.foldlM_toList] using withdrawnOk)
    exact keptTrans k1 <| keptTrans k2 <| keptTrans k3 <| keptTrans k4 <| keptTrans k5 <|
      keptTrans k6 <| keptTrans k7 <| keptTrans k8 <| keptTrans k9 <| keptTrans k10 <|
      keptTrans k11 k12
  have syncLife : RegistryLifecycle consolidated t := by
    obtain ⟨_, rfl⟩ := processSyncAggregate_eq syncOk
    exact .of_data rfl
  intro queue owned eventPosition paymentPosition callPosition held reserve assignment erasure
    prior retired cover future matched exits life start finite slashed fresh
  have bounded : EventsBounded events :=
    blockBalanceReplay_bounded (config := config) (checks := checks) early engine signed.message
      matched whole
  have sizeX := life.size_le
  -- The consolidation requests, each under the block's bound, at the block's sites.
  rw [syncEq] at bounded
  obtain ⟨addedC, consEq, replayC, epochC, factsC⟩ :=
    GuardedReplay.recordFold (config := config) (checks := checks) (x := x) (high := high)
      (rounding := rounding) (guard := G) (wide := wide)
      (all := (signed.message.body.executionRequests ⟨electra, early⟩).consolidations.data.toList)
      (start := withdrawn)
      (fun done rest item a b credit debit split reached limitsOk actionOk _ => by
        simp only [Except.ok.injEq, Prod.mk.injEq] at limitsOk
        obtain ⟨rfl, rfl⟩ := limitsOk
        have kept := keptTrans kHead (keptFold (fun _ _ _ one =>
          ⟨registryLifecycle_processConsolidationRequest one,
            effectiveKept_consolidationRequest one⟩) reached)
        have restOk : rest.foldlM (fun u i => processConsolidationRequest config u electra i) b =
            .ok consolidated := by
          have all := consolidatedOk
          rw [split] at all
          simp only [List.foldlM_append, List.foldlM_cons, bind_ok_iff] at all
          obtain ⟨a', reachedA, b', steppedB, restB⟩ := all
          obtain rfl := Except.ok.inj (reachedA.symm.trans reached)
          obtain rfl := Except.ok.inj (steppedB.symm.trans actionOk)
          exact restB
        have lifeBT := (RegistryLifecycle.foldlM (fun _ _ _ one =>
          registryLifecycle_processConsolidationRequest one) restOk).trans syncLife
        refine ⟨guardedReplay_consolidationRequest (config := config) (checks := checks) (x := x)
          (high := high) electra early delay compounding actionOk
          kept.1 kept.2 lifeBT sizeX ?_, (runFacts_consolidationRequest (x := x) actionOk).1,
          (runFacts_consolidationRequest (x := x) actionOk).2⟩
        intro grows
        exact Step.consolidationSites_of_request electra early
          ⟨s, headed, executed, revealed, by simp only [notGloas, ↓reduceDIte]; rfl,
            headerOk,
            by simpa [bellatrix] using executionOk, randaoOk, by simpa [before] using eth1Ok⟩
          expectedOk countOk (by simpa only [← Array.foldlM_toList] using proposedOk)
          (by simpa only [← Array.foldlM_toList] using slashedOk)
          (by simpa only [← Array.foldlM_toList] using attestedOk)
          (by simpa only [← Array.foldlM_toList] using depositedOk) exitedOk changedOk
          requestedOk withdrawnOk consolidatedOk split reached actionOk grows)
      lower _ [] withdrawn consolidated depEvents consEvents (by simp) rfl consolidatedRec
      (fun e member => bounded e (List.mem_append_left _ member))
  rw [consEq] at bounded
  obtain ⟨addedD, depEq, replayD, epochD, factsD⟩ :=
    GuardedReplay.recordFold (config := config) (checks := checks) (x := x) (high := high)
      (rounding := rounding) (guard := G) (wide := [])
      (all := (signed.message.body.deposits before).data.toList) (start := attested)
      (fun _ _ item a b credit debit _ _ limitsOk actionOk bnd => by
        have r := operationReplay_deposit (x := x) (high := high) (rounding := rounding) electra
          item a b credit debit limitsOk actionOk bnd
        exact ⟨r.1.guarded G, r.2.1, r.2.2⟩)
      lower _ [] attested deposited attEvents depEvents (by simp) rfl depositedRec
      (fun e member => bounded e (List.mem_append_left _ (List.mem_append_left _ member)))
  rw [depEq] at bounded
  obtain ⟨addedA, attEq, replayA, epochA, factsA⟩ :=
    guardedReplay_attestations (guard := G) (x := x) (high := high) (rounding := rounding)
      electra early s.latestBlockHeader.slot _ lower _ slashedS attested slashEvents attEvents
      attestedRec (fun e member => bounded e
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))))
  rw [attEq] at bounded
  obtain ⟨addedS, slashEq, replayS, epochS, factsS⟩ :=
    GuardedReplay.recordFold (config := config) (checks := checks) (x := x) (high := high)
      (rounding := rounding) (guard := G) (wide := [])
      (all := signed.message.body.attesterSlashings.data.toList) (start := proposed)
      (fun _ _ item a b credit debit _ _ limitsOk actionOk _ =>
        ⟨(reservedReplay_attesterSlashing x high rounding electra early delay item limitsOk
          actionOk).guarded G, (runFacts_attesterSlashing (x := x) actionOk).1,
          (runFacts_attesterSlashing (x := x) actionOk).2⟩)
      lower _ [] proposed slashedS propEvents slashEvents (by simp) rfl slashedRec
      (fun e member => bounded e (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ member)))))
  rw [slashEq] at bounded
  obtain ⟨addedP, propEq, replayP, epochP, factsP⟩ :=
    GuardedReplay.recordFold (config := config) (checks := checks) (x := x) (high := high)
      (rounding := rounding) (guard := G) (wide := [])
      (all := signed.message.body.proposerSlashings.data.toList) (start := voted)
      (fun _ _ item a b credit debit _ _ limitsOk actionOk _ =>
        ⟨(reservedReplay_proposerSlashing x high rounding electra early delay item limitsOk
          actionOk).guarded G, (runFacts_proposerSlashing (x := x) actionOk).1,
          (runFacts_proposerSlashing (x := x) actionOk).2⟩)
      lower _ [] voted proposed execEvents propEvents (by simp) rfl proposedRec
      (fun e member => bounded e (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ member))))))
  rw [propEq, execEq] at bounded
  -- The single operations and the carried folds.
  have execBound := (bounded _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))))))))).1
  have syncBound := (bounded _ (List.mem_append_right _ (List.mem_singleton_self _))).1
  have exitsList : signed.message.body.voluntaryExits.data.toList.foldlM
      (processVoluntaryExit config checks) deposited = .ok exited := by
    simpa only [Array.foldlM_toList] using exitedOk
  have requestsList :
      (signed.message.body.executionRequests ⟨electra, early⟩).deposits.data.toList.foldlM
        (processDepositRequest · electra ·) changed = .ok requested := by
    simpa only [Array.foldlM_toList] using requestedOk
  have withdrawalsList :
      (signed.message.body.executionRequests ⟨electra, early⟩).withdrawals.data.toList.foldlM
        (processWithdrawalRequest config · electra ·) requested = .ok withdrawn := by
    simpa only [Array.foldlM_toList] using withdrawnOk
  have requestFacts :=
      runFacts_of_frame (x := x)
      (BlockFrame.foldlM (fun _ _ _ one => frame_processDepositRequest one) requestsList)
    (RegistryLifecycle.foldlM (fun _ _ _ one => registryLifecycle_processDepositRequest one)
          requestsList)
  have syncFrame := frame_processSyncAggregate syncOk
  have composite :=
    ((operationReplay_header (x := x) (high := high) (rounding := rounding) electra
      headerOk).guarded G).append
    (((operationReplay_execution (x := x) (high := high) (rounding := rounding) electra early
      executionOk execBound).guarded G).append
    (((operationReplay_randao (x := x) (high := high) (rounding := rounding) electra
      randaoOk).guarded G).append
    (((operationReplay_eth1 (x := x) (high := high) (rounding := rounding) electra
      eth1Ok).guarded G).append
    (replayP.append (replayS.append (replayA.append (replayD.append
    (((reservedReplay_voluntaryExits x high rounding electra early delay _ exitsList).guarded
      G).append
    (((operationReplay_blsChanges x high rounding electra delay _ changedOk).guarded G).append
    (((operationReplay_depositRequests x high rounding electra _ requestsList).guarded G).append
    (((reservedReplay_withdrawalRequests x high rounding electra early delay _
      withdrawalsList).guarded G).append
    (replayC.append ((operationReplay_sync (x := x) (high := high) (rounding := rounding)
      electra syncOk syncBound).guarded G)
      lower epochC factsC)
      lower (runFacts_withdrawalRequests (x := x) withdrawalsList).1
        (runFacts_withdrawalRequests (x := x) withdrawalsList).2)
      lower requestFacts.1 requestFacts.2)
      lower (runFacts_blsChanges (x := x) changedOk).1
        (runFacts_blsChanges (x := x) changedOk).2)
      lower (runFacts_voluntaryExits (x := x) exitsList).1
        (runFacts_voluntaryExits (x := x) exitsList).2)
      lower epochD factsD) lower epochA factsA) lower epochS factsS) lower epochP factsP)
      lower (runFacts_of_frame (x := x) (frame_processEth1Data eth1Ok)
        (registryLifecycle_processEth1Data eth1Ok)).1
        (runFacts_of_frame (x := x) (frame_processEth1Data eth1Ok)
          (registryLifecycle_processEth1Data eth1Ok)).2)
      lower (runFacts_of_frame (x := x) (frame_processRandao randaoOk)
        (registryLifecycle_processRandao randaoOk)).1
        (runFacts_of_frame (x := x) (frame_processRandao randaoOk)
          (registryLifecycle_processRandao randaoOk)).2)
      lower (runFacts_of_frame (x := x) (frame_processBlockExecution executionOk)
        (.of_data (congrArg (·.data) (processBlockExecution_validators executionOk)))).1
        (runFacts_of_frame (x := x) (frame_processBlockExecution executionOk)
          (.of_data (congrArg (·.data) (processBlockExecution_validators executionOk)))).2)
      lower (runFacts_of_frame (x := x) (frame_processBlockHeader headerOk)
        (registryLifecycle_processBlockHeader headerOk)).1
        (runFacts_of_frame (x := x) (frame_processBlockHeader headerOk)
          (registryLifecycle_processBlockHeader headerOk)).2
  have shape : events = [] ++ ([⟨.withdrawals, ⟨fork, headed⟩, ⟨fork, executed⟩, 0, wDebit⟩] ++
      ([] ++ ([] ++ (addedP ++ (addedS ++ (addedA ++ (addedD ++ ([] ++ ([] ++ ([] ++ ([] ++
        (addedC ++ [⟨.sync, ⟨fork, consolidated⟩, ⟨fork, t⟩, syncCredit, syncDebit⟩]))))))))))))
      := by
    rw [syncEq, consEq, depEq, attEq, slashEq, propEq, execEq]
    simp only [List.nil_append, List.append_assoc]
  rw [shape]
  exact (composite.sites_mono (fun site member => by simpa using member)) queue owned
    eventPosition paymentPosition callPosition held reserve assignment erasure prior retired
    cover future matched exits life start finite slashed fresh

end

/-- The pending deposits of an epoch read at most the exit flow of that epoch.

They read the churn after the six stages before them.

That state has the validators and the slot of the epoch's input `a`.

Those stages keep activity and effective balances.

So that churn reads the total active balance at `a`, which the ceiling bounds.

From Electra the flow of an epoch is the activation and exit churn of the ceiling. -/
private theorem deposit_churn_le_exits {g x a : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x a) (high : Nat)
    (supported : Supported shared pre high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (cached reset : BeaconState preset a.fork) (churn : Gwei)
    (validators : cached.validators = a.state.validators) (slot : cached.slot = a.state.slot)
    (trace : EpochTrace (EpochStage.action config checks)
      [.justification, .inactivity, .rewards, .registry, .slashings, .eth1Reset] cached reset)
    (churnOk : depositChurnLimit config reset = .ok churn) :
    churn.toNat ≤ exitFlowAt (config := config) x high
      ((getCurrentEpoch a.state).toNat - (getCurrentEpoch x.state).toNat) := by
  obtain ⟨genesis, _, _, aligned, aEarly, _, guard⟩ := id supported
  have xEarly : x.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) aEarly
  have unit := ceiling_unit_of_guard shared genesis aligned xEarly electra guard
  have ceiling := (ceilingFloor_electra shared pre high supported twoSlots electra).1
  -- The six stages keep activity at the current epoch and the effective balances.
  have kept : ActiveStep cached reset ∧ EffectiveKept cached reset ∧
      cached.validators.data.size ≤ reset.validators.data.size := by
    refine trace.transport (fun s t => ActiveStep s t ∧ EffectiveKept s t ∧
        s.validators.data.size ≤ t.validators.data.size)
      (fun s => ⟨.refl s, effectiveKept_refl s, Nat.le_refl _⟩)
      (fun one two => ⟨one.1.trans two.1, effectiveKept_trans one.2.1 two.2.1 one.2.2,
        one.2.2.trans two.2.2⟩) ?_
    intro k member s t computed
    have edge := EpochStage.action_cases.mp computed
    by_cases registry : k = .registry
    · subst registry
      have keeps := stepKeeps_processRegistryUpdates
        (show processRegistryUpdates config s = .ok t from edge)
      exact ⟨keeps.2, effectiveKept_registry edge, keeps.1⟩
    · have same := edge.validators_eq ⟨registry, by rintro rfl; simp at member,
        by rintro rfl; simp at member⟩
      exact ⟨ActiveStep.of_validators (congrArg (·.data) same) (edge.slot_eq),
        effectiveKept_data (congrArg (·.data) same),
        Nat.le_of_eq (congrArg (·.data.size) same).symm⟩
  have resetEpoch : getCurrentEpoch reset = getCurrentEpoch cached := by
    simp only [getCurrentEpoch, kept.1.1]
  have resetTotal := total_active_congr aEarly aEarly
    (kept.1.2.mono (getCurrentEpoch_le_activityFixedEpoch cached)) resetEpoch kept.2.1
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch a.state := by
    simp only [getCurrentEpoch, slot]
  have cachedTotal := total_active_congr aEarly aEarly
    (ActiveKept.of_validators (congrArg (·.data) validators) _) cachedEpoch
    (effectiveKept_data (congrArg (·.data) validators))
  -- Before Gloas the deposit churn is the activation and exit churn.
  have notGloas : ¬ .glamsterdam ≤ a.fork := Nat.not_le_of_lt aEarly
  rw [depositChurnLimit_of_lt aEarly] at churnOk
  have exitOk : exitChurnLimit config reset = .ok churn := by
    simpa only [exitChurnLimit, notGloas, ↓reduceIte] using churnOk
  cases read : getTotalActiveBalance reset with
  | error e =>
    simp [exitChurnLimit, notGloas, getActivationExitChurnLimit, getBalanceChurnLimit, read,
      bind, Except.bind] at exitOk
  | ok total =>
    have rate := exit_rate_le_churn aEarly read exitOk
    have readA : getTotalActiveBalance a.state = .ok total := by
      rw [← cachedTotal, ← resetTotal]
      exact read
    have bounded := total_le_ceiling_of_read (u := a) readA
      (unit.trans (ceilingAt_mono electra high (Nat.zero_le _))) ceiling
    have notBefore : ¬ x.fork < .pectra := Nat.not_lt_of_ge electra
    have flow : exitFlowAt (config := config) x high
        ((getCurrentEpoch a.state).toNat - (getCurrentEpoch x.state).toNat) =
        activationExitChurn preset config (stakeCeilingAt config x high (ix x a)) := by
      simp [exitFlowAt, exitFlow, preElectraEpochs, notBefore]
    rw [flow]
    exact rate.trans (exit_churn_mono bounded)

/-- From Electra, take the deposit credits of a branch plus its final carry.

They fit its starting carry and the exit flow of each epoch of the window. -/
private theorem depositExits_proved {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (tail : Run config checks x y) (high : Nat)
    (supported : Supported shared tail high) (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (electra : .pectra ≤ x.fork) (events : List (BalanceEvent preset))
    (replayed : tail.balanceEvents high = .ok events) :
    (events.map funding_deposit_credit).sum + fundingCarry y ≤
      fundingCarry x +
          ((List.range (driftHorizon x high + 1)).map
            (exitFlowAt (config := config) x high)).sum := by
  obtain ⟨genesis, parameters, caps, aligned, early, endEpoch, guard⟩ := id supported
  have bound := funding_deposit_run_rate shared tail genesis early high endEpoch events replayed
    (fun e => exitFlowAt (config := config) x high (e - (getCurrentEpoch x.state).toNat))
    (fun pre aEarly aEpoch cached reset churn validators slot trace churnOk =>
      deposit_churn_le_exits shared pre high
        ⟨genesis, parameters, caps, aligned, aEarly, aEpoch, guard⟩ twoSlots electra cached reset
        churn validators slot trace churnOk)
  simp only [Nat.add_sub_cancel_left] at bound
  have count : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤
      driftHorizon x high + 1 := by
    unfold driftHorizon
    omega
  have widen := Finset.sum_le_sum_of_subset (f := exitFlowAt (config := config) x high)
    (Finset.range_mono count)
  have list : ∑ k ∈ Finset.range (driftHorizon x high + 1), exitFlowAt (config := config) x high k =
      ((List.range (driftHorizon x high + 1)).map (exitFlowAt (config := config) x high)).sum := by
    simp [Finset.sum, Finset.range_val, Multiset.range]
  omega

/-- The headline with its `deposits` premise discharged; it waits only on `BlockReplay`. -/
theorem headline_of_block_deposits
    (block : BlockReplay (preset := preset) (config := config) (checks := checks)) :
    AccountableDriftBound (preset := preset) (config := config) (checks := checks) ∧
      AccountableWindowBound (preset := preset) (config := config) (checks := checks) :=
  headline_of_block block fun _ _ _ shared tail high supported twoSlots electra events replayed =>
    depositExits_proved shared tail high supported twoSlots electra events replayed

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
