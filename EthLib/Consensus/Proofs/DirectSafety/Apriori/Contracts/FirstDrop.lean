module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ownership

/-!
# The supported branch and the first drop of a key

A supported branch meets the premises of the bound.

Along it, this module follows each key to the first drop of its effective balance.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Classical Cryptography.Bls Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

section RunContracts
variable {g x y : ForkedBeaconState preset}

def Supported (_shared : Run config checks g x) (_tail : Run config checks x y) (high : Nat) :
    Prop :=
  Genesis (config := config) (checks := checks) g ∧ Parameters preset ∧ CapOrder preset ∧
    MaxEffectiveBalancesAligned preset ∧ y.fork < .glamsterdam ∧
    (getCurrentEpoch y.state).toNat ≤ high + 1 ∧ aprioriGuardAt config x high
def FirstDown (tail : Run config checks x y) (i : Nat) : Prop :=
  ∃ j before after, tail.balancePath[j]? = some before ∧
    tail.balancePath[j + 1]? = some after ∧ effectiveAt after i < effectiveAt before i ∧
    ∀ k u v, k < j → tail.balancePath[k]? = some u →
      tail.balancePath[k + 1]? = some v → effectiveAt u i ≤ effectiveAt v i
/-- A trace from an account keeps the floor, less the penalty of a slash if it holds one.

The penalty is the slash term of the trace at the high-water mark of the slash. -/
theorem FloorTrace.balance_floor_general
    {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (initial : low ≤ a.balance + a.debt) :
    low ≤ b.balance + b.debt +
      b.slashedHigh.elim 0 (fun h => base / quotient + (h - base)) := by
  induction trace with
  | nil => exact Nat.le_trans initial (Nat.le_add_right _ _)
  | credit prior paid ih =>
    dsimp only at *
    omega
  | debit prior paid ih =>
    dsimp only at *
    omega
  | sweep prior paid ih =>
    dsimp only at *
    omega
  | update prior backed ih => exact ih
  | slash prior unused paid cap ih =>
    rename_i b balance penalty
    dsimp only at *
    rw [unused] at ih
    simp only [Option.elim] at ih ⊢
    omega
theorem FloorTrace.unslashed_balance_floor
    {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b)
    (initial : low ≤ a.balance + a.debt) (unslashed : b.slashedHigh = none) :
    low ≤ b.balance + b.debt := by
  simpa [unslashed] using trace.balance_floor_general initial
theorem FloorTrace.unslashed_high_deficit
    {low base quotient : Nat} {a b : FloorAccount}
    (trace : FloorTrace low base quotient a b) (unslashed : b.slashedHigh = none) :
    b.high - b.balance ≤ (a.high - a.balance) + b.debt := by
  induction trace with
  | nil => omega
  | credit prior paid ih =>
    have bound := ih unslashed
    dsimp only at *
    omega
  | debit prior paid ih =>
    have bound := ih unslashed
    dsimp only at *
    omega
  | sweep prior paid ih =>
    dsimp only at *
    omega
  | update prior backed ih =>
    have bound := ih unslashed
    dsimp only at *
    omega
  | slash prior unused paid cap ih => cases unslashed
private theorem FloorTrace.replay_deficit_resources
    {x middle : ForkedBeaconState preset} {i old : Nat}
    {prefixEvents events : List (BalanceEvent preset)}
    {low base quotient : Nat} {account : FloorAccount}
    (trace : FloorTrace low base quotient
      ⟨actualBalanceAt x i, 0, effectiveAt x i, none⟩ account)
    (clean : account.slashedHigh = none)
    (balance : account.balance = actualBalanceAt middle i)
    (effective : old ≤ account.high)
    (debt : account.debt =
      ((prefixEvents ++ events).map (floorPenaltyDebit i)).sum +
      ((prefixEvents ++ events).map (floorPartialDebit (UInt64.ofNat i))).sum) :
    old - actualBalanceAt middle i ≤ (effectiveAt x i - actualBalanceAt x i) +
      ((prefixEvents ++ events).map (floorPenaltyDebit i)).sum +
      ((prefixEvents ++ events).map (floorPartialDebit (UInt64.ofNat i))).sum := by
  have bound := FloorTrace.unslashed_high_deficit trace clean
  dsimp only at bound
  rw [balance, debt] at bound
  omega
private theorem floor_slot_before_update {g x m y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (ok : advanceSlotAcross config checks m = .ok y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (middle : m.state.validators.data[i.toNat]? = some u)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false)
    (short : (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat)
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {low base quotient : Nat} {a b : FloorAccount} (trace : FloorTrace low base quotient a b)
    (balance : b.balance = actualBalanceAt m i.toNat)
    (budget : (if b.slashedHigh.isSome then 1 else 0) +
      events.countP (floorSlash i.toNat) ≤ 1)
    (capped : max low b.high ≤ (withdrawalMaxEffectiveBalance preset m.fork u).toNat) :
    ∃ before advanced, FloorTrace low base quotient a before ∧
      advanceSlot config checks m.state = .ok advanced ∧
      before.balance = actualBalanceAt ⟨m.fork, advanced⟩ i.toNat ∧
      before.debt = b.debt + (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      before.high = b.high ∧
      (if before.slashedHigh.isSome then 1 else 0) =
        (if b.slashedHigh.isSome then 1 else 0) + events.countP (floorSlash i.toNat) := by
  let step := Step.slot ok
  have holds := (run_justified_separated (shared.append pre) genesis).1
  obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
  obtain ⟨p, first, second, path, split, empty, start, ends, linked,
    _empty', _, _, _, crossed⟩ := step.balanceChain early replayed
  have pathEq : step.balancePath = [m, ⟨m.fork, advanced⟩, y] := by
    simp [step, Step.balancePath, advanceOk, Except.toOption]
  have point : p = ⟨m.fork, advanced⟩ := by
    rw [pathEq] at path
    rcases path with ⟨impossible, _⟩ | same
    · simp at impossible
    · simpa using same.symm
  subst p
  have none : second = [] := List.eq_nil_iff_forall_not_mem.mpr (fun e member =>
    noCrossing e (split ▸ List.mem_append_right first member) (crossed pathEq e member))
  subst second
  simp only [List.append_nil] at split
  subst first
  have sites := step.balanceEvents_sites early holds caps.compounding replayed
  have slash := slot_delayed_slashing_nondebit pre ok caps early holds delay replayed
    i v u initial middle unslashed short
  obtain ⟨before, folded, nil, finish, debt, kept, used⟩ := FloorTrace.step_events step caps early
    holds replayed i u w middle final high
    (fun e member => (sites e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans endEpoch)
    (fun e member pending => by
      have bound := (sites e member).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 pending
      omega) retained noCrossing (List.Sublist.refl events)
    (linked.imp (fun _ _ h => h i.toNat))
    trace (fun e member => balance.trans (start e member i.toNat).symm) budget capped
    (fun e member source c prior balance _ _ => by
      obtain ⟨paid, validators⟩ := slash e member source
      have zero : floorSlash i.toNat e = false := by
        simp only [floorSlash, validators]
        cases found : e.before.state.validators.data[i.toNat]? with
        | none => simp
        | some z => cases z.slashed <;> simp
      exact ⟨{ c with balance := actualBalanceAt e.after i.toNat },
        prior.credit (by omega), rfl, by simp [floorPenaltyDebit, penaltyDebit,
          floorPartialDebit, source], rfl, by simp [zero]⟩)
  have atBefore : before.balance = actualBalanceAt ⟨m.fork, advanced⟩ i.toNat := by
    cases events with
    | nil => exact (nil rfl).trans (balance.trans (empty rfl i.toNat).symm)
    | cons e rest =>
      have found := List.getLast?_eq_some_getLast (l := e :: rest) (by simp)
      exact (finish _ found).trans (ends _ found i.toNat)
  exact ⟨before, advanced, folded, advanceOk, atBefore, debt, kept, used⟩
theorem slot_update_deficit_resources {g x m y : ForkedBeaconState preset}
    (shared : Run config checks g x) (pre : Run config checks x m)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (ok : advanceSlotAcross config checks m = .ok y) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    {prefixEvents events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (i : ValidatorIndex) (v u w : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (located : m.state.validators.data[i.toNat]? = some u)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (short : (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
        (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat)
    (high : Nat) (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (retained : high + 1 < w.exitEpoch.toNat)
    (noCrossing : ∀ e ∈ events, e.source ≠ .crossing)
    {low base quotient : Nat} {account : FloorAccount}
    (trace : FloorTrace low base quotient
      ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ account)
    (balance : account.balance = actualBalanceAt m i.toNat)
    (unmarked : account.slashedHigh = none)
    (debt : account.debt = (prefixEvents.map (floorPenaltyDebit i.toNat)).sum +
      (prefixEvents.map (floorPartialDebit i)).sum)
    (capped : max low account.high ≤ (withdrawalMaxEffectiveBalance preset m.fork u).toNat)
    (covered : effectiveAt m i.toNat ≤ account.high)
    {advanced middle : BeaconState preset m.fork}
    (advanceOk : advanceSlot config checks m.state = .ok advanced)
    (middleBalance : advanced.balances = middle.balances) :
    effectiveAt m i.toNat - actualBalanceAt ⟨m.fork, middle⟩ i.toNat ≤
      (effectiveAt x i.toNat - actualBalanceAt x i.toNat) +
        ((prefixEvents ++ events).map (floorPenaltyDebit i.toNat)).sum +
        ((prefixEvents ++ events).map (floorPartialDebit i)).sum := by
  have holds := (run_justified_separated (shared.append pre) genesis).1
  have count := floorSlash_step_bound (.slot ok) caps early holds replayed
    i.toNat u w located final
  have zero : events.countP (floorSlash i.toNat) = 0 := by
    simp only [clean, Bool.false_eq_true, ↓reduceIte] at count
    omega
  have budget : (if account.slashedHigh.isSome then 1 else 0) +
      events.countP (floorSlash i.toNat) ≤ 1 := by simp [unmarked, zero]
  obtain ⟨before, actual, folded, actualOk, atBefore, exactDebt, sameHigh, used⟩ :=
    floor_slot_before_update shared pre genesis caps ok early delay replayed i v u w
      initial located final unslashed short high endEpoch retained noCrossing trace balance
      budget capped
  have same : actual = advanced := Except.ok.inj (actualOk.symm.trans advanceOk)
  subst actual
  have beforeClean : before.slashedHigh = none := by
    simp only [unmarked, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, zero,
      Nat.zero_add] at used
    cases flag : before.slashedHigh with
    | none => rfl
    | some n => simp [flag] at used
  have atMiddle : before.balance = actualBalanceAt ⟨m.fork, middle⟩ i.toNat := by
    simpa only [actualBalanceAt, middleBalance] using atBefore
  have totalDebt : before.debt =
      ((prefixEvents ++ events).map (floorPenaltyDebit i.toNat)).sum +
      ((prefixEvents ++ events).map (floorPartialDebit (UInt64.ofNat i.toNat))).sum := by
    simp only [UInt64.ofNat_toNat, List.map_append, List.sum_append]
    omega
  have bound := FloorTrace.replay_deficit_resources folded beforeClean atMiddle
    (covered.trans (Nat.le_of_eq sameHigh.symm)) totalDebt
  simpa only [UInt64.ofNat_toNat] using bound
private theorem effective_loss_le_of_routed_floor
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) (debt : Nat)
    (floor : ∀ p ∈ tail.balancePath,
      min (effectiveAt x i) (actualBalanceAt x i) ≤ actualBalanceAt p i + debt) :
    effectiveAt x i ≤ effectiveAt y i + (effectiveAt x i - actualBalanceAt x i) + debt +
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  let amount := min (effectiveAt x i) (actualBalanceAt x i) - debt
  let rounded := amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  have amount_le : amount ≤ v.effectiveBalance.toNat := by
    have effective : effectiveAt x i = v.effectiveBalance.toNat := by simp [effectiveAt, found]
    dsimp [amount]
    omega
  have rounded_le : rounded ≤ amount := Nat.sub_le _ _
  have small : rounded < 2 ^ 64 := lt_of_le_of_lt (rounded_le.trans amount_le)
    v.effectiveBalance.toNat_lt
  let reference : Gwei := rounded.toUInt64
  have value : reference.toNat = rounded := by
    dsimp [reference]
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  have capped := shared.effectiveBalance_capped genesis caps.activation caps.compounding
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early) v
    (Array.mem_of_getElem? found)
  have bound := tail.effectiveAt_ge_of_balanceFloor caps early i v found activated reference
    (by
      rw [value]
      dsimp [rounded]
      have division := Nat.mod_add_div amount preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      have equal : amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            (amount / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by omega
      rw [equal, Nat.mul_mod_right])
    (fun p member => by
      have funded := floor p member
      rw [value]
      dsimp [rounded, amount]
      omega)
    (by rw [value]; dsimp [rounded, amount]; omega)
    (UInt64.le_iff_toNat_le.mpr (by
      have cap := UInt64.le_iff_toNat_le.mp capped
      rw [value]
      omega))
  have remainder := Nat.mod_lt amount increment
  rw [value] at bound
  dsimp [rounded, amount] at *
  omega
theorem balanceEvents_eq_of_endpoint_le
    (tail : Run config checks x y)
    (one : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (two : (getCurrentEpoch y.state).toNat ≤ localHigh + 1) :
    tail.balanceEvents high = tail.balanceEvents localHigh := by
  induction tail with
  | nil => rfl
  | @snoc m n pre step ih =>
    have order := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step).chainSteps)
    have first := order.trans one
    have second := order.trans two
    simp only [Run.balanceEvents, ih first second, first, second, ↓reduceIte]
theorem retained_local_replay
    {i : Nat} (tail : Run config checks x y)
    (positive : 0 < (getCurrentEpoch y.state).toNat)
    (endpoint : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (replayed : tail.balanceEvents high = .ok events)
    (w : Validator) (final : y.state.validators.data[i]? = some w)
    (active : (getCurrentEpoch y.state).toNat < w.exitEpoch.toNat) :
    tail.balanceEvents ((getCurrentEpoch y.state).toNat - 1) = .ok events ∧
      ∀ {m : ForkedBeaconState preset} (_rest : Run config checks m y) (v : Validator),
        m.state.validators.data[i]? = some v →
        (getCurrentEpoch y.state).toNat - 1 + 1 < v.exitEpoch.toNat := by
  constructor
  · rw [← balanceEvents_eq_of_endpoint_le tail endpoint (by omega)]
    exact replayed
  · intro m rest v found
    have cutoff := prefix_exit_gt_of_endpoint rest v w found final active
    omega
private theorem Stop.selected_local_replay
    {tail : Run config checks x y} (stop : Stop tail i)
    (chosen : stop.charge = some c)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (endpoint : (getCurrentEpoch stop.state.state).toNat ≤ high + 1)
    (replayed : stop.pre.balanceEvents high = .ok events) :
    stop.pre.balanceEvents (getCurrentEpoch stop.state.state).toNat = .ok events ∧
      ∀ {m : ForkedBeaconState preset} (_rest : Run config checks m stop.state)
        (v : Validator), m.state.validators.data[i]? = some v →
        (getCurrentEpoch stop.state.state).toNat + 1 < v.exitEpoch.toNat := by
  constructor
  · rw [← balanceEvents_eq_of_endpoint_le stop.pre endpoint (by omega)]
    exact replayed
  · intro m rest v found
    exact stop.selected_prefix_exit_gt chosen rest v found
      (getCurrentEpoch_succ_lt_farFuture twoSlots stop.state.state)
/-- The effective balance of a key reached from genesis is at most its largest. -/
private theorem effectiveAt_le_withdrawalMax (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (early : x.fork < .glamsterdam) {i : Nat} {v : Validator}
    (initial : x.state.validators.data[i]? = some v) :
    effectiveAt x i ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat := by
  have cap := shared.effectiveBalance_capped genesis caps.activation caps.compounding early v
    (Array.mem_of_getElem? initial)
  simpa [effectiveAt, initial] using UInt64.le_iff_toNat_le.mp cap

/-- The per-key accounting trace of a branch, from a floor.

The floor is at most the key's largest effective balance at the start.

A sweep or a switch to compounding leaves at least that much, and the largest only grows.

Each step extends the trace, keeping the carried account.

The trace is marked slashed only if the key ends the branch slashed.

The key is unslashed at the start.

Or it is slashed at the start, and its delayed penalty is not due along the branch.

The high-water mark of the trace stays within any bound on the effective balance of the branch. -/
theorem FloorTrace.run_of_le_cap_general
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ValidatorIndex) (v : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (low base quotient : Nat) (low_le : low ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∧
      ((v.slashed = false → (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∧
        (v.slashed = true → (getCurrentEpoch m.state).toNat +
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat)) ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ last, FloorTrace low base quotient
        ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      ∃ w, y.state.validators.data[i.toNat]? = some w ∧
        max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
        (if last.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) ∧
        (∀ p ∈ tail.balancePath, ∃ c, FloorTrace low base quotient
            ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ c ∧
          c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧
          (if c.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0)) ∧
        (∀ bound, effectiveAt x i.toNat ≤ bound →
          (∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
            (step : Step config checks m n) (post : Run config checks n y),
            (pre.snoc step).append post = tail → effectiveAt m i.toNat ≤ bound) →
          last.high ≤ max bound (effectiveAt y i.toNat) ∧
            ∀ h, last.slashedHigh = some h → h ≤ bound) ∧
        (v.slashed = true → last.slashedHigh = none) := by
  have assignedStart : v.slashed = true → v.exitEpoch ≠ FAR_FUTURE_EPOCH := fun slashed =>
    run_slashed_exit_assigned shared genesis caps.activation caps.compounding
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early) delay i.toNat v initial
      slashed
  induction tail generalizing events with
  | nil =>
    have empty : events = [] := Except.ok.inj replayed.symm
    subst events
    have cap := shared.effectiveBalance_capped genesis caps.activation caps.compounding
      early v (Array.mem_of_getElem? initial)
    have capped : max low (effectiveAt x i.toNat) ≤
        (withdrawalMaxEffectiveBalance preset x.fork v).toNat := by
      have atStart : effectiveAt x i.toNat = v.effectiveBalance.toNat := by
        simp [effectiveAt, initial]
      have numeric := UInt64.le_iff_toNat_le.mp cap
      omega
    refine ⟨⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩,
      .nil, rfl, by simp, le_rfl, v, initial, capped, by simp, ?_,
      fun bound atStart _ => ⟨atStart.trans (Nat.le_max_left _ _), nofun⟩, fun _ => rfl⟩
    intro p member
    have same : p = x := List.mem_singleton.mp member
    subst p
    exact ⟨_, .nil, rfl, le_rfl, by simp⟩
  | @snoc m n pre step ih =>
    have middleEpoch := (UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step).chainSteps)).trans endEpoch
    have middleEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    obtain ⟨prior, priorOk, _⟩ := pre.balanceEvents_prefix (Run.nil.snoc step) high events
      (by simpa [Run.append] using replayed)
    obtain ⟨added, addedOk⟩ := step.balanceEvents_ok early
    have exactEvents : events = prior ++ added := by
      simp only [Run.balanceEvents, priorOk, middleEpoch, ↓reduceIte, addedOk,
        bind, Except.bind, pure, Except.pure, Except.ok.injEq] at replayed
      exact replayed.symm
    have priorGuards : ∀ {a b : ForkedBeaconState preset} (head : Run config checks x a)
        (edge : Step config checks a b) (rest : Run config checks b m),
        (head.snoc edge).append rest = pre → ∀ w,
        b.state.validators.data[i.toNat]? = some w →
        high + 1 < w.exitEpoch.toNat ∧
        ((v.slashed = false → (getCurrentEpoch a.state).toNat < (getCurrentEpoch x.state).toNat +
          preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
            (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat) ∧
          (v.slashed = true → (getCurrentEpoch a.state).toNat +
            (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat < v.withdrawableEpoch.toNat)) ∧
        quotient ≤ (EthLib.Consensus.parameters preset a.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
        ∀ events, edge.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing := by
      intro a b head edge rest split w found
      apply guards head edge (rest.snoc step)
      · simp only [Run.append, split]
      · exact found
    obtain ⟨before, trace, balance, debt, effective, u, middle, capped, flagged, earlier,
      priorHigh, priorNone⟩ := ih middleEarly middleEpoch priorGuards priorOk
    obtain ⟨w, final, _⟩ := (Run.nil.snoc step).registryLifecycle.validators i.toNat u middle
    obtain ⟨retained, window, quotient_le, noCrossing⟩ := guards pre step .nil rfl w final
    obtain ⟨old, located, life⟩ := pre.registryLifecycle.validators i.toNat v initial
    have same := Option.some.inj (located.symm.trans middle)
    subst old
    have assigned : u.activationEpoch ≠ FAR_FUTURE_EPOCH := by
      rwa [life.activationEpoch activated]
    obtain ⟨last, done, atEnd, exactDebt, highBound, capBound, used, later, stepHigh, marks,
      stepNone⟩ :=
      FloorTrace.step_general shared pre genesis caps step early delay addedOk i v u w
        initial middle final assignedStart assigned
        (by
          cases flag : v.slashed
          · exact .inl ⟨rfl, window.1 flag⟩
          · exact .inr ⟨rfl, window.2 flag⟩)
        high endEpoch retained
        (noCrossing added addedOk) trace balance flagged capped effective positive quotient_le
    -- A key slashed by `m` stays slashed at `n`.
    have persists : (if u.slashed then 1 else 0) ≤ (if w.slashed then 1 else 0) := by
      cases flag : u.slashed with
      | false => simp
      | true =>
        obtain ⟨z, located, marked⟩ :=
          (Run.nil.snoc step).slashedPersistence i.toNat u middle flag
        have equal := Option.some.inj (located.symm.trans final)
        subst z
        simp [marked]
    refine ⟨last, done, atEnd, ?_, highBound, w, final, capBound, used, ?_, ?_, ?_⟩
    · simp only [exactEvents, List.map_append, List.sum_append]
      omega
    · intro p member
      rcases List.mem_append.mp member with member | member
      · obtain ⟨c, traced, atState, spent, flag⟩ := earlier p member
        exact ⟨c, traced, atState, by omega, flag.trans persists⟩
      · obtain ⟨c, traced, atState, spent, flag⟩ := later p member
        exact ⟨c, traced, atState, spent, flag.trans used⟩
    · intro bound atStart strict
      have prior := priorHigh bound atStart fun {_ _} head edge rest split =>
        strict head edge (rest.snoc step) (by simp only [Run.append, split])
      have atMiddle : effectiveAt m i.toNat ≤ bound := strict pre step .nil rfl
      have priorTop : before.high ≤ bound := (prior.1).trans (max_le le_rfl atMiddle)
      refine ⟨stepHigh.trans (max_le_max priorTop le_rfl), fun h hh => ?_⟩
      rcases marks h hh with seen | top
      · exact prior.2 h seen
      · exact top ▸ priorTop
    · intro slashed
      obtain ⟨z, located', marked⟩ := pre.slashedPersistence i.toNat v initial slashed
      have equal := Option.some.inj (located'.symm.trans middle)
      subst z
      exact stepNone marked (priorNone slashed)

/-- The per-key accounting trace of a branch, from a floor.

The floor is at most the key's largest effective balance at the start.

A sweep or a switch to compounding leaves at least that much, and the largest only grows.

Each step extends the trace, keeping the carried account.

The trace is marked slashed only if the key ends the branch slashed. -/
theorem FloorTrace.run_of_le_cap
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ValidatorIndex) (v : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (unslashed : v.slashed = false) (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (low base quotient : Nat) (low_le : low ≤ (withdrawalMaxEffectiveBalance preset x.fork v).toNat)
    (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ last, FloorTrace low base quotient
        ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      ∃ w, y.state.validators.data[i.toNat]? = some w ∧
        max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
        (if last.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) ∧
        ∀ p ∈ tail.balancePath, ∃ c, FloorTrace low base quotient
            ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ c ∧
          c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧
          (if c.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) := by
  obtain ⟨last, trace, balance, debt, effective, w, final, capped, used, path, -⟩ :=
    FloorTrace.run_of_le_cap_general shared tail genesis caps delay early high endEpoch i v
      initial activated low base quotient low_le positive
      (fun pre step post split w found => by
        obtain ⟨retained, short, quotient_le, noCrossing⟩ := guards pre step post split w found
        exact ⟨retained, ⟨fun _ => short, fun h => absurd h (by simp [unslashed])⟩, quotient_le,
          noCrossing⟩) replayed
  exact ⟨last, trace, balance, debt, effective, w, final, capped, used, path⟩

/-- The per-key accounting trace of a branch, through any slashing of the key.

Each step extends the trace, keeping the carried account.

The trace is marked slashed only if the key ends the branch slashed. -/
theorem FloorTrace.run
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ValidatorIndex) (v : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (unslashed : v.slashed = false) (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (low base quotient : Nat) (low_le : low ≤ effectiveAt x i.toNat)
    (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      high + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events) :
    ∃ last, FloorTrace low base quotient
        ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧
      ∃ w, y.state.validators.data[i.toNat]? = some w ∧
        max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat ∧
        (if last.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) ∧
        ∀ p ∈ tail.balancePath, ∃ c, FloorTrace low base quotient
            ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ c ∧
          c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧
          (if c.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0) :=
  FloorTrace.run_of_le_cap shared tail genesis caps delay early high endEpoch i v initial unslashed
    activated low base quotient (low_le.trans (effectiveAt_le_withdrawalMax shared genesis caps
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps tail.chainSteps) early) initial)) positive
    guards replayed

theorem unslashed_floor_run
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : y.fork < .glamsterdam) (high : Nat)
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (i : ValidatorIndex) (v : Validator)
    (initial : x.state.validators.data[i.toNat]? = some v)
    (unslashed : v.slashed = false) (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (low base quotient : Nat) (low_le : low ≤ effectiveAt x i.toNat)
    (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n y),
      (pre.snoc step).append post = tail → ∀ w, n.state.validators.data[i.toNat]? = some w →
      w.slashed = false ∧ high + 1 < w.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing)
    (replayed : tail.balanceEvents high = .ok events) :
    ∃ last, FloorTrace low base quotient
        ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ last ∧
      last.balance = actualBalanceAt y i.toNat ∧
      last.debt = (events.map (floorPenaltyDebit i.toNat)).sum +
        (events.map (floorPartialDebit i)).sum ∧
      effectiveAt y i.toNat ≤ last.high ∧ last.slashedHigh = none ∧
      (∃ w, y.state.validators.data[i.toNat]? = some w ∧
        max low last.high ≤ (withdrawalMaxEffectiveBalance preset y.fork w).toNat) ∧
      ∀ p ∈ tail.balancePath, ∃ c, FloorTrace low base quotient
          ⟨actualBalanceAt x i.toNat, 0, effectiveAt x i.toNat, none⟩ c ∧
        c.balance = actualBalanceAt p i.toNat ∧ c.debt ≤ last.debt ∧ c.slashedHigh = none := by
  have noFlag {account : FloorAccount} {w : Validator} (clean : w.slashed = false)
      (bound : (if account.slashedHigh.isSome then 1 else 0) ≤ (if w.slashed then 1 else 0)) :
      account.slashedHigh = none := by
    cases flag : account.slashedHigh with
    | none => rfl
    | some value => simp [flag, clean] at bound
  obtain ⟨last, trace, balance, debt, effective, w, final, capped, used, path⟩ :=
    FloorTrace.run shared tail genesis caps delay early high endEpoch i v initial unslashed
      activated low base quotient low_le positive
      (fun pre step post split w found => (guards pre step post split w found).2) replayed
  -- The key ends the branch unslashed: at `x` itself, or after a step that keeps it clean.
  have clean : w.slashed = false := by
    cases tail with
    | nil =>
      have same := Option.some.inj (initial.symm.trans final)
      subst w
      exact unslashed
    | snoc pre step => exact (guards pre step .nil rfl w final).1
  refine ⟨last, trace, balance, debt, effective, noFlag clean used, ⟨w, final, capped⟩, ?_⟩
  intro p member
  obtain ⟨c, traced, atState, spent, flag⟩ := path p member
  exact ⟨c, traced, atState, spent, noFlag clean flag⟩

private theorem effectiveAt_le_of_not_firstDown
    (tail : Run config checks x y) (none : ¬ FirstDown tail i) :
    effectiveAt x i ≤ effectiveAt y i := by
  have ordered (j : Nat) (before after : ForkedBeaconState preset)
      (one : tail.balancePath[j]? = some before)
      (two : tail.balancePath[j + 1]? = some after) :
      effectiveAt before i ≤ effectiveAt after i := by
    by_contra decrease
    have existsDrop : ∃ j, ∃ before after, tail.balancePath[j]? = some before ∧
        tail.balancePath[j + 1]? = some after ∧ effectiveAt after i < effectiveAt before i :=
      ⟨j, before, after, one, two, by omega⟩
    obtain ⟨before, after, one, two, less⟩ := Nat.find_spec existsDrop
    apply none
    refine ⟨Nat.find existsDrop, before, after, one, two, less, ?_⟩
    intro k u v earlier atU atV
    have absent := Nat.find_min existsDrop earlier
    by_contra bad
    exact absent ⟨u, v, atU, atV, by omega⟩
  have starts : ∃ rest, tail.balancePath = x :: rest := by
    clear none ordered
    induction tail with
    | nil => exact ⟨[], rfl⟩
    | snoc pre step ih =>
      obtain ⟨rest, path⟩ := ih
      exact ⟨rest ++ step.balancePath, by simp [Run.balancePath, path]⟩
  obtain ⟨rest, starts⟩ := starts
  obtain ⟨pre, ends⟩ := Run.balancePath_last tail
  have first : tail.balancePath[0]? = some x := by simp [starts]
  have last : tail.balancePath[pre.length]? = some y := by simp [ends]
  have bound (n : Nat) : ∀ state, tail.balancePath[n]? = some state →
      effectiveAt x i ≤ effectiveAt state i := by
    induction n with
    | zero =>
      intro state atState
      have same := Option.some.inj (first.symm.trans atState)
      subst state
      exact le_rfl
    | succ n ih =>
      intro state atState
      have length : n < tail.balancePath.length := by
        obtain ⟨inside, _⟩ := List.getElem?_eq_some_iff.mp atState
        omega
      have atBefore : tail.balancePath[n]? = some tail.balancePath[n] :=
        List.getElem?_eq_getElem length
      exact (ih _ atBefore).trans (ordered n _ state atBefore atState)
  exact bound _ y last
private theorem adjacent_decrease_append
    (left right : List (ForkedBeaconState preset))
    (last : left[left.length - 1]? = some middle)
    (start : right[0]? = some middle)
    (one : (left ++ right)[j]? = some before)
    (two : (left ++ right)[j + 1]? = some after)
    (decreases : effectiveAt after i < effectiveAt before i) :
    (j + 1 < left.length ∧ left[j]? = some before ∧ left[j + 1]? = some after) ∨
      (left.length ≤ j ∧ right[j - left.length]? = some before ∧
        right[j - left.length + 1]? = some after) := by
  by_cases within : j + 1 < left.length
  · exact Or.inl ⟨within, (List.getElem?_append_left (by omega)).symm.trans one,
      (List.getElem?_append_left within).symm.trans two⟩
  · by_cases beyond : left.length ≤ j
    · right
      refine ⟨beyond, (List.getElem?_append_right beyond).symm.trans one, ?_⟩
      have found := (List.getElem?_append_right (l₁ := left) (l₂ := right)
        (i := j + 1) (by omega)).symm.trans two
      have offset : j + 1 - left.length = j - left.length + 1 := by omega
      simpa only [offset] using found
    · have boundary : j + 1 = left.length := by omega
      have atBefore : left[left.length - 1]? = some before := by
        have found :=
            (List.getElem?_append_left (l₂ := right) (by omega : j < left.length)).symm.trans one
        simpa only [← boundary, Nat.add_sub_cancel] using found
      have atAfter : right[0]? = some after := by
        have found := (List.getElem?_append_right (l₁ := left) (l₂ := right)
          (i := j + 1) (by omega)).symm.trans two
        simpa only [boundary, Nat.sub_self] using found
      have equalBefore := Option.some.inj (last.symm.trans atBefore)
      have equalAfter := Option.some.inj (start.symm.trans atAfter)
      rw [← equalBefore, ← equalAfter] at decreases
      exact False.elim (Nat.lt_irrefl _ decreases)
theorem adjacent_decrease_step
    (tail : Run config checks x y)
    (one : tail.balancePath[j]? = some before)
    (two : tail.balancePath[j + 1]? = some after)
    (decreases : effectiveAt after i < effectiveAt before i) :
    ∃ m n, ∃ (pre : Run config checks x m) (step : Step config checks m n),
      ∃ (post : Run config checks n y) (k : Nat),
      (pre.snoc step).append post = tail ∧ j = pre.balancePath.length + k ∧
      step.balancePath[k]? = some before ∧ step.balancePath[k + 1]? = some after := by
  induction tail generalizing j with
  | nil =>
    have impossible := two
    simp [Run.balancePath] at impossible
  | @snoc m n pre step ih =>
    obtain ⟨rest, path⟩ := Run.balancePath_last pre
    have last : pre.balancePath[pre.balancePath.length - 1]? = some m := by
      simp [path]
    have start : step.balancePath[0]? = some m := by
      cases step with
      | block => rfl
      | slot ok =>
        obtain ⟨advanced, advanceOk, _⟩ := bind_ok_iff.mp ok
        simp [Step.balancePath, advanceOk, Except.toOption]
    rcases adjacent_decrease_append pre.balancePath step.balancePath last start one two decreases
        with
      earlier | latest
    · obtain ⟨a, b, head, actual, post, k, split, offset, found, next⟩ := ih earlier.2.1 earlier.2.2
      exact ⟨a, b, head, actual, post.snoc step, k,
        by simp only [Run.append, split], offset, found, next⟩
    · exact ⟨m, n, pre, step, Run.nil, j - pre.balancePath.length,
        rfl, by omega, latest.2.1, latest.2.2⟩
theorem step_decrease_of_regime
    (step : Step config checks m n) (regime : .pectra ≤ m.fork ∨ n.fork < .pectra)
    (early : n.fork < .glamsterdam) (inside : i < m.state.validators.data.size)
    (one : step.balancePath[k]? = some before)
    (two : step.balancePath[k + 1]? = some after)
    (decreases : effectiveAt after i < effectiveAt before i) :
    ∃ (ok : advanceSlotAcross config checks m = .ok n),
      step = Step.slot ok ∧ ∃ advanced,
        advanceSlot config checks m.state = .ok advanced ∧
        k = 0 ∧ before = m ∧ after = ⟨m.fork, advanced⟩ := by
  cases step with
  | block engine signed due ok =>
    have index : k = 0 := by
      have length := (List.getElem?_eq_some_iff.mp two).1
      simp only [Step.balancePath, List.length_cons, List.length_nil] at length
      omega
    subst k
    simp only [Step.balancePath, List.getElem?_cons_zero, Option.some.injEq] at one
    simp only [Step.balancePath, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at two
    subst before
    subst after
    have kept := effectiveKept_block early (applySignedBlock_ok ok).2.1 i inside
    dsimp only at kept
    omega
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgraded⟩ := bind_ok_iff.mp ok
    have path : (Step.slot ok).balancePath = [m, ⟨m.fork, advanced⟩, n] := by
      simp [Step.balancePath, advanceOk, Except.toOption]
    have bound : k ≤ 1 := by
      have length := (List.getElem?_eq_some_iff.mp two).1
      rw [path] at length
      simp only [List.length_cons, List.length_nil] at length
      omega
    have zero : k = 0 := by
      by_contra nonzero
      have index : k = 1 := by omega
      rw [path, index] at one two
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at one two
      subst before
      subst after
      have kept : effectiveAt n i = effectiveAt ⟨m.fork, advanced⟩ i := by
        rcases regime with electra | preElectra
        · have target : .pectra ≤ n.fork := Nat.le_trans electra
            (processUpgrades_fork_le (forked := ⟨m.fork, advanced⟩) upgraded)
          have data := processUpgrades_retained_data (s := ⟨m.fork, advanced⟩)
            electra early upgraded target
          simp only [effectiveAt, data]
        · have data := upgrades_validators upgraded preElectra
          simp only [effectiveAt, data]
      omega
    refine ⟨ok, rfl, advanced, advanceOk, zero, ?_, ?_⟩
    · simpa only [path, zero, List.getElem?_cons_zero, Option.some.injEq] using one.symm
    · simpa only [path, zero, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] using two.symm
theorem advanceSlot_decrease_last
    {fork : Fork} {s t : BeaconState preset fork}
    (ok : advanceSlot config checks s = .ok t)
    (decreases : effectiveAt ⟨fork, t⟩ i < effectiveAt ⟨fork, s⟩ i) :
    ∃ next cached epoched,
      addChecked s.slot 1 = .ok next ∧ next % preset.SLOTS_PER_EPOCH = 0 ∧
      processSlot s = .ok cached ∧ processEpoch config checks cached = .ok epoched ∧
      t = { epoched with slot := next } := by
  obtain ⟨next, cached, epoched, sum, cachedOk, epochOk, rfl⟩ := advanceSlot_ok ok
  have checked : addChecked s.slot 1 = .ok next :=
    addChecked_ok_iff.mpr ⟨by
      change s.slot.toNat + 1 < 2 ^ 64
      have small := next.toNat_lt
      omega, sum⟩
  have last : next % preset.SLOTS_PER_EPOCH = 0 := by
    by_contra nonlast
    simp only [epochIfLast, nonlast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epoched
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    simp only [effectiveAt, Nat.lt_irrefl] at decreases
  simp only [epochIfLast, last, ↓reduceIte] at epochOk
  exact ⟨next, cached, epoched, checked, last, cachedOk, epochOk, rfl⟩
theorem slot_epoch_events_eq
    {m y : ForkedBeaconState preset}
    (ok : advanceSlotAcross config checks m = .ok y)
    {cached middle advanced : BeaconState preset m.fork} {next : Slot}
    {events : List (BalanceEvent preset)}
    (cachedOk : processSlot m.state = .ok cached)
    (nextOk : addChecked m.state.slot 1 = .ok next)
    (last : next % preset.SLOTS_PER_EPOCH = 0)
    (replayed : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, events))
    (advancedOk : advanceSlot config checks m.state = .ok advanced)
    (noCrossing : ∀ found, (Step.slot ok).balanceEvents = .ok found →
      ∀ e ∈ found, e.source ≠ .crossing) :
    (Step.slot ok).balanceEvents = .ok events := by
  obtain ⟨actual, advance, upgrades⟩ := bind_ok_iff.mp ok
  have same : actual = advanced := Except.ok.inj (advance.symm.trans advancedOk)
  subst actual
  obtain ⟨crossings, crossed, _bounded⟩ := upgradeBalanceReplay_bounded upgrades
  have checked : liftAccessor (liftArith (addChecked m.state.slot 1)) =
      (Except.ok next : Except TransitionError Slot) := by
    simp [nextOk, liftArith, liftAccessor, Except.mapError]
  have full := Step.balanceEvents_epoch_slot ok cachedOk checked last replayed advancedOk crossed
  have empty : crossings = [] := List.eq_nil_iff_forall_not_mem.mpr (by
    intro e member
    exact noCrossing _ full e (List.mem_append_right events member)
      (upgradeBalanceReplay_crossing crossed e member))
  simpa only [empty, List.append_nil] using full
private theorem effectiveKept_epoch_replay_middle
    {fork : Fork} {s t middle : BeaconState preset fork}
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t)
    (replayed : epochBalanceReplay (config := config) (checks := checks) s =
      .ok (middle, events)) : EffectiveKept s middle := by
  obtain ⟨actual, updated, recorded, replay, _update, _validators, _balances, processed⟩ :=
    epochBalanceReplay_result_before s t early ok
  have same := Except.ok.inj (replay.symm.trans replayed)
  have stateEq : actual = middle := congrArg Prod.fst same
  subst actual
  exact effectiveKept_epochBeforePayments processed
private theorem capped_epoch_replay_middle
    {fork : Fork} {s t middle : BeaconState preset fork}
    (early : fork < .glamsterdam) (ok : processEpoch config checks s = .ok t)
    (replayed : epochBalanceReplay (config := config) (checks := checks) s =
      .ok (middle, events))
    (capped : ∀ v ∈ s.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v) :
    ∀ v ∈ middle.validators.data,
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork v := by
  obtain ⟨actual, updated, recorded, replay, _update, _validators, _balances, processed⟩ :=
    epochBalanceReplay_result_before s t early ok
  have same := Except.ok.inj (replay.symm.trans replayed)
  have stateEq : actual = middle := congrArg Prod.fst same
  subst actual
  exact capped_epochBeforePayments processed capped
private theorem slot_replay_middle_effective
    {fork : Fork} {s cached epoched middle : BeaconState preset fork}
    (early : fork < .glamsterdam) (cachedOk : processSlot s = .ok cached)
    (epochOk : processEpoch config checks cached = .ok epoched)
    (replayed : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, events)) : EffectiveKept s middle := by
  have kept := effectiveKept_epoch_replay_middle early epochOk replayed
  have same : cached.validators = s.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  intro i inside
  have valid : i < cached.validators.data.size := by simpa only [same] using inside
  simpa only [effectiveAt, same] using kept i valid
private theorem reachable_replay_middle_bounds
    {g outer : ForkedBeaconState preset}
    (shared : Run config checks g outer)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    {cached epoched middle : BeaconState preset outer.fork}
    (early : outer.fork < .glamsterdam)
    (cachedOk : processSlot outer.state = .ok cached)
    (epochOk : processEpoch config checks cached = .ok epoched)
    (replayed : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, events))
    (inside : i < outer.state.validators.data.size)
    (found : middle.validators.data[i]? = some v) :
    v.effectiveBalance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
      v.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset outer.fork v := by
  have same : cached.validators = outer.state.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have originalCaps := shared.effectiveBalance_capped genesis caps.activation caps.compounding early
  have middleCaps := capped_epoch_replay_middle early epochOk replayed
    (by simpa only [same] using originalCaps)
  refine ⟨?_, middleCaps v (Array.mem_of_getElem? found)⟩
  have kept := slot_replay_middle_effective early cachedOk epochOk replayed i inside
  have original := reachable_effective_alignment shared genesis aligned
    outer.state.validators.data[i] (by simp)
  have originalRead := Array.getElem?_eq_getElem inside
  simp only [effectiveAt, found, originalRead, Option.map_some, Option.getD_some] at kept
  rw [kept]
  exact original
theorem effective_update_input_reads
    {fork : Fork} {middle updated : BeaconState preset fork}
    (update : processEffectiveBalanceUpdates middle = .ok updated)
    (inside : i < middle.validators.data.size) :
    ∃ v amount, middle.validators.data[i]? = some v ∧
      middle.balances.data[i]? = some amount := by
  have stepBalances : ∀ {s t : BeaconState preset fork} {j : Nat},
      updateEffectiveBalance s j = .ok t → t.balances = s.balances := by
    intro s t j step
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨validator, _found, balance, _read, effective, _scalar, set⟩ := step
    obtain ⟨_valid, rfl⟩ := setValidatorAt_ok set
    rfl
  unfold processEffectiveBalanceUpdates at update
  obtain ⟨atState, next, prefixOk, atIndex, _rest⟩ :=
    (foldlM_ok_steps (fun _ _ => True) (fun _ => trivial) (fun _ _ => trivial)
      (fun _ _ _ _ => trivial) update).2 i (by simpa using inside)
  simp only [List.getElem_range] at atIndex
  have balances : atState.balances = middle.balances :=
    foldlM_ok_invariant (fun current : BeaconState preset fork =>
      current.balances = middle.balances)
      (fun _ _ _ kept step => (stepBalances step).trans kept) rfl prefixOk
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at atIndex
  obtain ⟨validator, _found, amount, read, _effective, _scalar, _set⟩ := atIndex
  refine ⟨middle.validators.data[i], amount, Array.getElem?_eq_getElem inside, ?_⟩
  rw [getBalanceAt_eq_ok_iff, balances] at read
  exact read
private theorem effective_update_decrease_reads
    {fork : Fork} {s middle updated : BeaconState preset fork}
    (kept : EffectiveKept s middle)
    (update : processEffectiveBalanceUpdates middle = .ok updated)
    (inside : i < s.validators.data.size)
    (decreases : effectiveAt ⟨fork, updated⟩ i < effectiveAt ⟨fork, s⟩ i) :
    ∃ v amount, middle.validators.data[i]? = some v ∧
      middle.balances.data[i]? = some amount := by
  have preserved := kept i inside
  have valid : i < middle.validators.data.size := by
    by_contra missing
    have absent : middle.validators.data[i]? = none :=
      Array.getElem?_eq_none (by omega)
    have zero : effectiveAt ⟨fork, middle⟩ i = 0 := by
      simp only [effectiveAt, absent, Option.map_none, Option.getD_none]
    rw [zero] at preserved
    omega
  exact effective_update_input_reads update valid
private theorem effective_update_decrease_at
    {fork : Fork} {s middle updated : BeaconState preset fork}
    (kept : EffectiveKept s middle)
    (update : processEffectiveBalanceUpdates middle = .ok updated)
    (found : middle.validators.data[i]? = some v)
    (balance : middle.balances.data[i]? = some amount)
    (inside : i < s.validators.data.size)
    (decreases : effectiveAt ⟨fork, updated⟩ i < effectiveAt ⟨fork, s⟩ i) :
    ∃ effective,
      updated.validators.data[i]? = some { v with effectiveBalance := effective } ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork v)
        amount v.effectiveBalance = .ok effective ∧
      effective < v.effectiveBalance ∧ v.effectiveBalance.toNat = effectiveAt ⟨fork, s⟩ i := by
  obtain ⟨effective, after, computed⟩ :=
    processEffectiveBalanceUpdates_effectiveBalance_eq update found balance
  have before := kept i inside
  simp only [effectiveAt, found, Option.map_some, Option.getD_some] at before
  have lower : effective.toNat < v.effectiveBalance.toNat := by
    simpa only [effectiveAt, after, Option.map_some, Option.getD_some, ← before] using decreases
  exact ⟨effective, after, computed, UInt64.lt_iff_toNat_lt.mpr lower, before⟩
private theorem effective_update_decrease_witness
    {fork : Fork} {s middle updated : BeaconState preset fork}
    (kept : EffectiveKept s middle)
    (update : processEffectiveBalanceUpdates middle = .ok updated)
    (inside : i < s.validators.data.size)
    (decreases : effectiveAt ⟨fork, updated⟩ i < effectiveAt ⟨fork, s⟩ i) :
    ∃ v amount effective,
      middle.validators.data[i]? = some v ∧
      middle.balances.data[i]? = some amount ∧
      updated.validators.data[i]? = some { v with effectiveBalance := effective } ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset fork v)
        amount v.effectiveBalance = .ok effective ∧
      effective < v.effectiveBalance ∧ v.effectiveBalance.toNat = effectiveAt ⟨fork, s⟩ i := by
  obtain ⟨v, amount, found, balance⟩ :=
    effective_update_decrease_reads kept update inside decreases
  obtain ⟨effective, after, scalar, lower, before⟩ :=
    effective_update_decrease_at kept update found balance inside decreases
  exact ⟨v, amount, effective, found, balance, after, scalar, lower, before⟩
private theorem scalar_decrease_gap {largest amount old effective : Gwei}
    (aligned : old.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (capped : old ≤ largest)
    (computed : updatedEffectiveBalance preset largest amount old = .ok effective)
    (lower : effective < old) :
    preset.downwardBand < old.toNat - amount.toNat := by
  have lowerNat := UInt64.lt_iff_toNat_lt.mp lower
  have cappedNat := UInt64.le_iff_toNat_le.mp capped
  rcases updatedEffectiveBalance_split computed with ⟨same, _⟩ | ⟨rounded, down | up⟩
  · subst effective
    omega
  · omega
  · have below : old.toNat ≤ amount.toNat := by omega
    have quotient : old.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        amount.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat := Nat.div_le_div_right below
    have product := Nat.mul_le_mul_right preset.EFFECTIVE_BALANCE_INCREMENT.toNat quotient
    rw [Nat.mul_comm (old.toNat / _), Nat.mul_comm (amount.toNat / _)] at product
    have oldDiv := Nat.mod_add_div old.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have amountDiv := Nat.mod_add_div amount.toNat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have roundedNat := toNat_rounded (preset := preset) (balance := amount)
    have roundedLower : old ≤ amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT := by
      rw [UInt64.le_iff_toNat_le, roundedNat]
      omega
    have resultLower : old ≤ effective := by
      rw [rounded, UInt64.min_def]
      split
      · exact roundedLower
      · exact capped
    exact False.elim (by have := UInt64.le_iff_toNat_le.mp resultLower; omega)
theorem reachable_update_decrease_gap
    {g outer : ForkedBeaconState preset}
    (shared : Run config checks g outer)
    (genesis : Genesis (config := config) (checks := checks) g)
    (caps : CapOrder preset) (aligned : MaxEffectiveBalancesAligned preset)
    {cached epoched middle updated : BeaconState preset outer.fork}
    (early : outer.fork < .glamsterdam)
    (cachedOk : processSlot outer.state = .ok cached)
    (epochOk : processEpoch config checks cached = .ok epoched)
    (replayed : epochBalanceReplay (config := config) (checks := checks) cached =
      .ok (middle, events))
    (update : processEffectiveBalanceUpdates middle = .ok updated)
    (inside : i < outer.state.validators.data.size)
    (decreases : effectiveAt ⟨outer.fork, updated⟩ i < effectiveAt outer i) :
    ∃ v amount effective,
      middle.validators.data[i]? = some v ∧
      middle.balances.data[i]? = some amount ∧
      updated.validators.data[i]? = some { v with effectiveBalance := effective } ∧
      updatedEffectiveBalance preset (withdrawalMaxEffectiveBalance preset outer.fork v)
        amount v.effectiveBalance = .ok effective ∧
      effective < v.effectiveBalance ∧ v.effectiveBalance.toNat = effectiveAt outer i ∧
      preset.downwardBand < v.effectiveBalance.toNat - amount.toNat := by
  have kept := slot_replay_middle_effective early cachedOk epochOk replayed
  obtain ⟨v, amount, effective, found, balance, after, scalar, lower, before⟩ :=
    effective_update_decrease_witness kept update inside decreases
  obtain ⟨whole, capped⟩ := reachable_replay_middle_bounds shared genesis caps aligned early
    cachedOk epochOk replayed inside found
  exact ⟨v, amount, effective, found, balance, after, scalar, lower, before,
    scalar_decrease_gap whole capped scalar lower⟩
theorem noEarlier_of_localized_decrease
    (tail : Run config checks x y) (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    (split : (pre.snoc step).append post = tail)
    (offset : j = pre.balancePath.length + k)
    (ordered : ∀ q u v, q < j → tail.balancePath[q]? = some u →
      tail.balancePath[q + 1]? = some v → effectiveAt u i ≤ effectiveAt v i) :
    ∀ q u v, pre.balancePath[q]? = some u → pre.balancePath[q + 1]? = some v →
      effectiveAt u i ≤ effectiveAt v i := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [split, Run.balancePath, List.append_assoc] at path
  intro q u v one two
  have within : q + 1 < pre.balancePath.length := (List.getElem?_eq_some_iff.mp two).1
  apply ordered q u v (by omega)
  · rw [path, List.getElem?_append_left (by omega)]
    exact one
  · rw [path, List.getElem?_append_left within]
    exact two
/-- Take a key whose balance minus a debt stays above a lower bound at `x`.

That bound is the smaller of the key's effective balance and balance at `x`.

Then its effective balance drops by at most its slack, the debt and one increment. -/
theorem effective_loss_le_of_floor
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) (debt : Nat)
    (floor : ∀ p ∈ tail.balancePath,
      min (effectiveAt x i) (actualBalanceAt x i) ≤ actualBalanceAt p i + debt) :
    effectiveAt x i ≤ effectiveAt y i + (effectiveAt x i - actualBalanceAt x i) + debt +
      (if FirstDown tail i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) := by
  by_cases drop : FirstDown tail i
  · have bound := effective_loss_le_of_routed_floor shared tail genesis caps increment early
      v found activated debt floor
    simp only [drop, ↓reduceIte]
    omega
  · have bound := effectiveAt_le_of_not_firstDown tail drop
    simp only [drop, ↓reduceIte]
    omega
theorem effective_loss_le_of_unslashed_traces
    (shared : Run config checks g x) (tail : Run config checks x y)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (early : y.fork < .glamsterdam)
    (v : Validator) (found : x.state.validators.data[i]? = some v)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH) (debt base quotient : Nat)
    (traces : ∀ p ∈ tail.balancePath, ∃ c,
      FloorTrace (min (effectiveAt x i) (actualBalanceAt x i)) base quotient
        ⟨actualBalanceAt x i, 0, effectiveAt x i, none⟩ c ∧
      c.balance = actualBalanceAt p i ∧ c.debt ≤ debt ∧ c.slashedHigh = none) :
    effectiveAt x i ≤ effectiveAt y i + (effectiveAt x i - actualBalanceAt x i) + debt +
      (if FirstDown tail i then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) :=
  effective_loss_le_of_floor shared tail genesis caps increment early v found activated debt
    fun p member => by
      obtain ⟨c, trace, balance, used, clean⟩ := traces p member
      have lower := FloorTrace.unslashed_balance_floor trace (by dsimp only; omega) clean
      rw [balance] at lower
      omega
private theorem Stop.selected_effective_loss
    {tail : Run config checks x y} (stop : Stop tail i.toNat)
    (chosen : stop.charge = some c) (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : stop.state.fork < .glamsterdam)
    (v w : Validator) (initial : x.state.validators.data[i.toNat]? = some v)
    (final : stop.state.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (endpoint : (getCurrentEpoch stop.state.state).toNat ≤ high + 1)
    (replayed : stop.pre.balanceEvents high = .ok events)
    (base quotient : Nat) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n stop.state),
      (pre.snoc step).append post = stop.pre →
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing) :
    effectiveAt x i.toNat ≤ effectiveAt stop.state i.toNat +
      (effectiveAt x i.toNat - actualBalanceAt x i.toNat) +
      ((events.map (floorPenaltyDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum) +
      (if FirstDown stop.pre i.toNat then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) := by
  obtain ⟨localReplay, exits⟩ := stop.selected_local_replay chosen twoSlots endpoint replayed
  have localGuards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n stop.state),
      (pre.snoc step).append post = stop.pre → ∀ u,
      n.state.validators.data[i.toNat]? = some u →
      u.slashed = false ∧ (getCurrentEpoch stop.state.state).toNat + 1 < u.exitEpoch.toNat ∧
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing := by
    intro m n pre step post split u found
    obtain ⟨short, quotientBound, noCrossing⟩ := guards pre step post split
    have unmarked : u.slashed = false := by
      cases flag : u.slashed with
      | false => rfl
      | true =>
        obtain ⟨last, located, marked⟩ := post.slashedPersistence i.toNat u found flag
        have same := Option.some.inj (located.symm.trans final)
        subst last
        simp [clean] at marked
    exact ⟨unmarked, exits post u found, short, quotientBound, noCrossing⟩
  obtain ⟨last, _, _, debt, _, _, _, path⟩ := unslashed_floor_run shared stop.pre
    genesis caps delay early (getCurrentEpoch stop.state.state).toNat (by omega)
    i v initial unslashed activated (min (effectiveAt x i.toNat) (actualBalanceAt x i.toNat))
    base quotient (Nat.min_le_left _ _) positive localGuards localReplay
  apply effective_loss_le_of_unslashed_traces shared stop.pre genesis caps increment early
    v initial activated _ base quotient
  simpa only [debt] using path
theorem Stop.clean_read_of_endpoint
    {tail : Run config checks x y} (stop : Stop tail i)
    (v w : Validator) (initial : x.state.validators.data[i]? = some v)
    (final : y.state.validators.data[i]? = some w) (clean : w.slashed = false) :
    ∃ u, stop.state.state.validators.data[i]? = some u ∧ u.slashed = false := by
  obtain ⟨u, found, _⟩ := stop.pre.registryLifecycle.validators i v initial
  refine ⟨u, found, ?_⟩
  cases flag : u.slashed with
  | false => rfl
  | true =>
    obtain ⟨last, located, marked⟩ := stop.post.slashedPersistence i u found flag
    have same := Option.some.inj (located.symm.trans final)
    subst last
    simp [clean] at marked
theorem Stop.selected_charge_loss
    {tail : Run config checks x y} (stop : Stop tail i.toNat)
    (chosen : stop.charge = some c) (shared : Run config checks g x)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (early : stop.state.fork < .glamsterdam)
    (v w : Validator) (initial : x.state.validators.data[i.toNat]? = some v)
    (final : y.state.validators.data[i.toNat]? = some w)
    (unslashed : v.slashed = false) (clean : w.slashed = false)
    (activated : v.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (endpoint : (getCurrentEpoch stop.state.state).toNat ≤ high + 1)
    (replayed : stop.pre.balanceEvents high = .ok events)
    (base quotient : Nat) (positive : 0 < quotient)
    (guards : ∀ {m n : ForkedBeaconState preset} (pre : Run config checks x m)
      (step : Step config checks m n) (post : Run config checks n stop.state),
      (pre.snoc step).append post = stop.pre →
      (getCurrentEpoch m.state).toNat < (getCurrentEpoch x.state).toNat +
        preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat -
          (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2).toNat ∧
      quotient ≤ (EthLib.Consensus.parameters preset m.fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ∧
      ∀ events, step.balanceEvents = .ok events → ∀ e ∈ events, e.source ≠ .crossing) :
    effectiveAt x i.toNat ≤ c.amount + (effectiveAt x i.toNat - actualBalanceAt x i.toNat) +
      ((events.map (floorPenaltyDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum) +
      (if FirstDown stop.pre i.toNat then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0) := by
  obtain ⟨u, found, unmarked⟩ := stop.clean_read_of_endpoint v w initial final clean
  have bound := stop.selected_effective_loss chosen shared genesis caps increment twoSlots
    delay early v u initial found unslashed unmarked activated endpoint replayed
    base quotient positive guards
  have selected := stop.selected
  rw [chosen] at selected
  rwa [← selected.2.2.1] at bound

end RunContracts

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
