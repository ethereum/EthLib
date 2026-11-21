module

import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import Mathlib.Algebra.Order.Floor.Div
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.SeatDebits

/-! The setting and costs for the pin reserve. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

namespace Internal

/-- The gain budget separates compounding flows from the cap charge for new keys. -/
theorem creditGain_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).creditGain =
      (pinTerms config state ancestor finalizedState).creditLow +
        (pinTerms config state ancestor finalizedState).creditCap := rfl

/-- The branch exit charge sums the stake and rise of keys that start exiting after the split. -/
theorem exitedR_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).exitedR =
      ∑ i ∈ (pinTerms config state ancestor finalizedState).positions with
        (pinTerms config state ancestor finalizedState).exitedRB i = true,
        (balanceAt state i + (pinTerms config state ancestor finalizedState).rise i) := rfl

/-- The branch slashing count includes keys slashed on this branch after the finalized epoch. -/
theorem slashedR_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).slashedR =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).slashedRB i = true).card := rfl

/-- The queue budget separates deposits from exits and consolidations. -/
theorem queues_split (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queues =
      (pinTerms config state ancestor finalizedState).queueDep +
        (pinTerms config state ancestor finalizedState).queueExit := rfl

/-- Each queued exit is charged a rounding band and gains at the largest rate. -/
theorem queueRise_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueRise =
      if (pinTerms config state ancestor finalizedState).tight then 0 else
        3 * (pinTerms config state ancestor finalizedState).queueKeys *
          (preset.upwardBand + (pinTerms config state ancestor finalizedState).depth *
            (pinTerms config state ancestor finalizedState).gainRateMax) := rfl

/-- The exit count divides churn by the minimum charge and allows for ends, low and new keys. -/
theorem queueKeys_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).queueKeys =
      (pinTerms config state ancestor finalizedState).queueWindow /
          (pinTerms config state ancestor finalizedState).exitFloor + 2 +
        (pinTerms config state ancestor finalizedState).lowKeys +
        (pinTerms config state ancestor finalizedState).newKeySeats := rfl

/-- A key's fall is its effective balance less its floor within the delay, and all of it beyond. -/
theorem fall_eq (config : Config) (state ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).fall i =
      if (getCurrentEpoch state).toNat + 2 - (getCurrentEpoch finalizedState).toNat ≤
          config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat then
        balanceAt state i - (pinTerms config state ancestor finalizedState).floorC i
      else balanceAt state i := rfl

/-- The lower bound subtracts losses from the least starting balance, capped at activation. -/
theorem lowEB_unfold (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    (i : ℕ) :
    (pinTerms config state ancestor finalizedState).lowEB i =
      min (min (min (balanceAt state i) (balanceAt finalizedState i))
            (((finalizedState.balances.data[i]?).map (·.toNat)).getD 0) -
          (pinTerms config state ancestor finalizedState).partialsDue i)
        preset.MIN_ACTIVATION_BALANCE.toNat -
        (pinTerms config state ancestor finalizedState).drop i := rfl

/-- A finalized key's starting balance is its actual balance at that state, capped. -/
theorem base0_of_found (config : Config) (pulled anc fin : BeaconState preset fork)
    {i : ℕ} {val : Validator} (initial : fin.validators.data[i]? = some val) :
    (pinTerms config pulled anc fin).base0 i =
      min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        (withdrawalMaxEffectiveBalance preset fork val).toNat := by
  simp only [pinTerms, PinTerms.capAt, initial, Option.map_some, Option.getD_some]
  rfl

/-- The loss bound for a finalized key includes its starting shortfall and leak. -/
theorem drop_of_found (config : Config) (pulled anc fin : BeaconState preset fork)
    {i : ℕ} {val : Validator} (initial : fin.validators.data[i]? = some val) :
    (pinTerms config pulled anc fin).drop i =
      ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            ((pinTerms config pulled anc fin).base0 i +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  simp only [pinTerms, PinTerms.capAt, initial, Option.map_some, Option.getD_some]
  rfl

/-- The low-balance count includes every key marked below the new-key floor. -/
theorem lowKeys_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) :
    (pinTerms config state ancestor finalizedState).lowKeys =
      ((pinTerms config state ancestor finalizedState).positions.filter fun i =>
        (pinTerms config state ancestor finalizedState).lowB i = true).card := rfl

end Internal

/-! ## The setting of the pin -/

/-- The setting of the pin's drift bound for one call.

The call's own-epoch runs are left out. -/
structure Setting (config : Config) (checks : SignatureChecks) (g : ForkedBeaconState preset)
    (split fin pulled anc counted : BeaconState preset fork) (V : Finset ValidatorIndex) :
    Prop where
  genesis : Genesis config checks g
  toFin : Nonempty (Run config checks g ⟨fork, fin⟩)
  fromFin : Nonempty (Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
  toPulled : Nonempty (Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
  toCounted : Nonempty (Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
  early : fork < .glamsterdam
  fulu : .fusaka ≤ fork
  bands : preset.IncrementWithinUpwardBand
  caps : CapOrder preset
  window : preset.SeedLookaheadAtLeastThree
  parameters : DirectSafety.Parameters preset
  aligned : MaxEffectiveBalancesAligned preset
  twoSlots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat
  shallow : (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat ≤
    config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat
  pulledTotal : ∃ t, getTotalActiveBalance pulled = .ok t
  facts : PinPresetFacts preset
  guard : DirectSafety.Apriori.aprioriGuardAt config ⟨fork, fin⟩ (getCurrentEpoch pulled).toNat
  finalized : anc.finalizedCheckpoint.epoch ≤ getCurrentEpoch split
  later : getCurrentEpoch pulled ≤ getCurrentEpoch counted
  near : (getCurrentEpoch counted).toNat ≤ (getCurrentEpoch pulled).toNat + 1
  voting : ∀ v ∈ V, v ∈ activeVoters pulled ∧ (slashedFlagAt counted v.toNat).getD false = false

namespace Internal

/-- The call's epoch is at or after the split's, since a run leads from one to the other. -/
theorem Setting.called {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    getCurrentEpoch split ≤ getCurrentEpoch pulled := by
  obtain ⟨toPulled⟩ := h.toPulled
  exact currentEpoch_le_of_chainSteps toPulled.chainSteps

/-- The withdrawal delay is positive, since it is at least the two epochs past the finalized one. -/
theorem Setting.delay {g : ForkedBeaconState preset}
    {split fin pulled anc counted : BeaconState preset fork} {V : Finset ValidatorIndex}
    (h : Setting config checks g split fin pulled anc counted V) :
    0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have order : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps (fromFin.append toPulled).chainSteps)
  have := h.shallow
  omega

/-! ## Flows of the two branches -/

/-- The deposits applied to the key on R's branch.

They are over the replayed events of the run from the split. -/
def credDepR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .deposits)).map (Internal.keyCredit v)).sum

/-- The consolidation credits to the key over the replayed events of a run.

The bound sums the consolidation credits over the target keys. -/
def consAmt (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .consolidations)).map (Internal.keyCredit v)).sum

/-! ### The C-side credits of a key, read from the run

The run itself supplies the credits and the balance rise after an exit.

A block step's `.rewards` events are its proposer's credits.

A slot step's `.rewards` events are the epoch's flag rewards.

So a slot step counts only the sources named below.

Sync rewards are accounted for with the committee seats. -/

/-- Proposer and due-consolidation credits to the key on C's branch since the split.

The reserve counts one rounding band per credited key.

The reserve counts consolidation bands separately. -/
def propC {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations)) v high tail)

/-- Proposer credits to the key on C's branch since the split, without the consolidation credits.

A credited stake compounds by at most a tenth.

The bounds of the terms charge an exact tenth of the keys' total, at ten times their terms.

Consolidation credits and their compounding draw on the consolidation budget instead. -/
def propN {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards)) (fun _ => false) v high tail)

/-- Proposer and deposit credits to the key on C's branch since the split.

Consolidation credits are excluded.

A credited stake compounds by at most a tenth.

The bounds of the terms charge an exact tenth of the keys' total, at ten times their terms. -/
def credN {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards)) (fun s => decide (s = .deposits)) v high
    tail)

/-- The deposits credited to a key by events whose state before them does not hold it slashed.

A slashed key's whistleblower reward reads its effective balance at the slashing.

Of the deposits and proposer credits, only those before slashing can raise that balance.

This holds because a slashed key proposes no block. -/
def depPre (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter fun e => e.source = .deposits ∧
      ¬ (slashedFlagAt e.before.state v = some true)).map (Internal.keyCredit v)).sum

/-- Non-attestation credits to the key on C's branch since the split.

Whistleblower and sync credits are excluded.

The credits are the proposer's, deposits applied and consolidations.

The reserve counts one rounding band per credited key. -/
def credC {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards ∨ s = .consolidations))
    (fun s => decide (s = .consolidations ∨ s = .deposits)) v high tail)

/-- Whistleblower credits to the key on C's branch since the split.

A whistleblower credit lands in the block of the proposer's own slot.

The reserve counts one rounding band per credited key.

A slot step records only debits for a slashing. -/
def whistC {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  (Internal.creditScan (fun s => decide (s = .slashings)) (fun _ => false) v high tail)

/-- The entries of X's queue of pending consolidations that name a target in `T`.

They are the ones that apply by `high + 1`.

This counts the entries rather than summing their amounts. -/
def dueAt (X : BeaconState preset fork) (high : ℕ) (T : Finset ValidatorIndex) : ℕ :=
  if electra : .pectra ≤ fork then
    ((((X.pendingConsolidations electra).data.toList.filter fun c =>
        decide (c.targetIndex ∈ T)).filterMap fun c =>
      X.validators.data[c.sourceIndex.toNat]?).filter fun v =>
        !v.slashed && decide (v.withdrawableEpoch.toNat ≤ high + 1)).length
  else 0

/-- The debit that one balance event takes from the key at position `i`. -/
def keyDebit (i : ℕ) (e : BalanceEvent preset) : ℕ :=
  actualBalanceAt e.before i - actualBalanceAt e.after i

/-- The sync-seat movement of the key over the replayed events of one run.

It is the key's credits and debits of the sync aggregates.

They are a seat's debit, a seat's reward, and the proposer's share of it.

The caller adds it over the two runs from the split, since both branches credit and debit seats. -/
def syncF (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  ((events.filter (·.source = .sync)).map (Internal.keyCredit v)).sum +
    ((events.filter (·.source = .sync)).map (Internal.keyDebit v)).sum

/-- One increment for a key slashed on R's branch after the finalized epoch.

The effective-balance drop from R's initial slashing penalty is at most one increment.

R's slashing budget allots at least one increment to each such key. -/
def slashR (t : PinTerms preset) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then preset.EFFECTIVE_BALANCE_INCREMENT.toNat else 0

/-- The gross credits to the key in the block steps of a run, from rewards, slashings and sync.

A block step counts the credits of its events from those sources, whatever the step takes back. -/
def grossScan (v high : ℕ) {x y : ForkedBeaconState preset} (tail : Run config checks x y) :
    ℕ :=
  (Internal.creditScan (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
    false) v
    high tail)

/-- The gross credits of a run, after one more step. -/
theorem grossScan_snoc (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (step : Step config checks m y) :
    Internal.grossScan v high (pre.snoc step) = if (getCurrentEpoch m.state).toNat ≤ high + 1 then
      Internal.grossScan v high pre + Internal.stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) v step
      else Internal.grossScan v high pre := by
  unfold Internal.grossScan
  exact Internal.creditScan_snoc _ _ v high pre step

private theorem grossScan_slot_pos (i high : ℕ) {x m n : ForkedBeaconState preset}
    (pre : Run config checks x m) (ok : advanceSlotAcross config checks m = .ok n)
    (pos : 0 < Internal.grossScan i high (pre.snoc (Step.slot ok))) : 0 < Internal.grossScan i high
      pre := by
  rw [Internal.grossScan_snoc] at pos
  split at pos
  · simpa [Internal.stepCredit] using pos
  · exact pos

/-- The gross credits add across consecutive runs. -/
theorem grossScan_append (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    Internal.grossScan v high (pre.append post) = Internal.grossScan v high pre + Internal.grossScan
      v high post := by
  unfold Internal.grossScan
  exact Internal.creditScan_append _ _ v high pre post

/-- The rounding slack of a key with any C-side credit, once for each key.

The credits are the gross credits of its block steps, and an applied deposit.

A proposer reward, a whistleblower reward and a sync reward are block credits.

Consolidation credits count separately, with a band for each queue entry.

The credit budget includes one upward rounding band per credited key. -/
def bandC {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  if 0 < Internal.grossScan v high tail +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail) then
    preset.upwardBand else 0

/-- A sum over the members of a list that pass one of two apart tests is the two sums. -/
theorem sum_filter_or {α : Type} (L : List α) (p q : α → Bool)
    (apart : ∀ a, ¬ (p a = true ∧ q a = true)) (f : α → ℕ) :
    ((L.filter fun a => p a || q a).map f).sum =
      ((L.filter p).map f).sum + ((L.filter q).map f).sum := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    by_cases hp : p a = true
    · have hq : q a = false := by
        cases h : q a
        · rfl
        · exact absurd ⟨hp, h⟩ (apart a)
      simp [hp, hq, ih]; omega
    · by_cases hq : q a = true
      · simp [hp, hq, ih]; omega
      · simp [hp, hq, ih]

/-- The credits of a run that a scan reads add over two apart sets of sources.

The block sources of the scan and the slot sources are each the union of two apart sources. -/
theorem creditScan_or (blockP slotP b₁ b₂ s₁ s₂ : BalanceSource → Bool)
    (hb : ∀ s, blockP s = (b₁ s || b₂ s)) (hs : ∀ s, slotP s = (s₁ s || s₂ s))
    (apartB : ∀ s, ¬ (b₁ s = true ∧ b₂ s = true)) (apartS : ∀ s, ¬ (s₁ s = true ∧ s₂ s = true))
    (v high : ℕ) {x y : ForkedBeaconState preset} (tail : Run config checks x y) :
    (Internal.creditScan blockP slotP v high tail) =
      (Internal.creditScan b₁ s₁ v high tail) + (Internal.creditScan b₂ s₂ v high tail) := by
  obtain rfl : blockP = fun s => b₁ s || b₂ s := funext hb
  obtain rfl : slotP = fun s => s₁ s || s₂ s := funext hs
  induction tail with
  | nil => rfl
  | @snoc middle last pre step ih =>
    have split : Internal.stepCredit (fun s => b₁ s || b₂ s) (fun s => s₁ s || s₂ s) v step =
        Internal.stepCredit b₁ s₁ v step + Internal.stepCredit b₂ s₂ v step := by
      cases step with
      | slot ok =>
        simp only [Internal.stepCredit]
        exact Internal.sum_filter_or _ (fun e : BalanceEvent preset => s₁ e.source)
          (fun e => s₂ e.source) (fun e => apartS e.source) _
      | block engine signed due ok =>
        simp only [Internal.stepCredit]
        exact Internal.sum_filter_or _ (fun e : BalanceEvent preset => b₁ e.source)
          (fun e => b₂ e.source) (fun e => apartB e.source) _
    rw [Internal.creditScan_snoc, Internal.creditScan_snoc, Internal.creditScan_snoc, split]
    split_ifs <;> omega

/-- The credits of a key on C's branch are its proposer credits and the deposits it is credited. -/
theorem credN_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    Internal.credN tail high v = Internal.propN tail high v +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high tail) :=
  Internal.creditScan_or _ _ (fun s => decide (s = .rewards)) (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits)) (fun s => by cases s <;> decide)
    (fun s => by cases s <;> decide)
    (fun s h => by simp at h) (fun s h => by simp at h) v high tail

/-- Adding consolidation credits completes the key's proposer and deposit credit total. -/
theorem credC_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    Internal.credC tail high v = Internal.credN tail high v +
      (Internal.creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v high tail) :=
  Internal.creditScan_or _ _ (fun s => decide (s = .rewards)) (fun s => decide (s =
    .consolidations))
    (fun s => decide (s = .deposits)) (fun s => decide (s = .consolidations))
    (fun s => by cases s <;> decide) (fun s => by cases s <;> decide)
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide))
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide)) v high tail

/-- The combined total adds consolidation credits to proposer credits. -/
theorem propC_split {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) :
    Internal.propC tail high v = Internal.propN tail high v +
      (Internal.creditScan (fun s => decide (s = .consolidations))
        (fun s => decide (s = .consolidations)) v high tail) :=
  Internal.creditScan_or _ _ (fun s => decide (s = .rewards)) (fun s => decide (s =
    .consolidations))
    (fun _ => false) (fun s => decide (s = .consolidations))
    (fun s => by cases s <;> decide) (fun s => by cases s <;> decide)
    (fun s h => by simp at h; exact absurd (h.1.symm.trans h.2) (by decide))
    (fun s h => by simp at h) v high tail

/-- The proposer credits of two runs, one after the other, add. -/
theorem propN_append {x m y : ForkedBeaconState preset} (pre : Run config checks x m)
    (post : Run config checks m y) (high v : ℕ) :
    Internal.propN (pre.append post) high v = Internal.propN pre high v + Internal.propN post high v
      :=
  Internal.creditScan_append _ _ v high pre post

/-- The gain of `C` credited gwei over `depth` epochs, at the reward rate `P`.

The credits count in whole increments rounded up, and each epoch's gain is rounded down. -/
def gainOn (preset : Preset) (depth P C : ℕ) : ℕ :=
  depth * ((((C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) / WEIGHT_DENOMINATOR.toNat)

/-- The rounding slack of a key whose balance on R's branch took a sync debit that `high` omits.

It is one increment and the downward band less one.

R's branch budget includes a rounding step for each such key. -/
def bandR (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  if 0 < ((events.filter (·.source = .sync)).map (Internal.keyDebit v)).sum then
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0

/-- The sync credits to the key over the replayed events of one run. -/
def syncCr (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  (events.map (Internal.syncCredit v)).sum

/-- The sync debits of the key over the replayed events of one run. -/
def syncD (events : List (BalanceEvent preset)) (v : ℕ) : ℕ :=
  (events.map (Internal.syncDebit v)).sum

/-- A whistleblower's share of an amount at eleven tenths of three, rounded up.

It is `⌈33·x/(10·WRQ)⌉`, with the whistleblower quotient of the fork. -/
def wShare (preset : Preset) (fork : Fork) (x : ℕ) : ℕ :=
  (33 * x + 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
    (10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- The band of each due consolidation entry of the state `X` that targets the key. -/
def bandX (X : BeaconState preset fork) (high v : ℕ) : ℕ :=
  preset.upwardBand * Internal.dueAt X high {UInt64.ofNat v}

/-- The initial slashing penalty of a key slashed on R's branch after the split, at the cap. -/
def slashW (t : PinTerms preset) (i : ℕ) : ℕ :=
  if t.slashedRB i = true then
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
      (EthLib.Consensus.parameters preset .fusaka).MIN_SLASHING_PENALTY_QUOTIENT.toNat
  else 0

/-- The extra leak caused by sync debits on R's run from the finalized block.

It subtracts leak at the reserve's ceiling from leak at the run's highest effective balance.

The extra leak is zero if the key is withdrawable by R's next epoch.

Such a key is swept by R, so the leak is not charged. -/
def inducedR (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) : ℕ :=
  if t.withdrawnRB i = true then 0
  else
    t.depthFin * (t.leakAt ((tail.balancePath.map fun z => effectiveAt z i).foldl max 0) i -
      t.leakAt (t.ebUp i) i)

/-- A key that R holds withdrawable by the next epoch has no induced leak. -/
theorem inducedR_of_withdrawn (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) (withdrawn : t.withdrawnRB i = true) :
    Internal.inducedR t tail i = 0 := by
  simp [Internal.inducedR, withdrawn]

/-- A key that R does not hold withdrawable is charged the leak at its largest balance. -/
theorem inducedR_of_not_withdrawn (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (i : ℕ) (kept : t.withdrawnRB i = false) :
    Internal.inducedR t tail i =
      t.depthFin * (t.leakAt ((tail.balancePath.map fun z => effectiveAt z i).foldl max 0) i -
        t.leakAt (t.ebUp i) i) := by
  simp [Internal.inducedR, kept]

/-- The flows that can raise a key's balance on C above R's base, besides its epoch rewards.

They are its credits on C's branch and its sync debits on R's branch and on the shared segment.

They also include the initial penalty of a slashing on R's branch.

The credits `cred` count the key's deposits by default.

For a previous-only key, the caller excludes deposits. -/
def flowCredit (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  cred + Internal.whistC tailC high i + Internal.syncCr eventsC i + Internal.syncD events i +
    Internal.syncD eventsF i +
    Internal.slashW t i

/-- The gain of a key's flows over the window, at eleven tenths in whole increments.

It is one floor of all the flows; the closure splits it by kind in aggregate.

Its rate is floored once, after the increments, as the gain of the credits is.

A gain-carrying run starts at the split, so the gain runs over at most the shorter window. -/
def flowGain (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  min t.depth t.depthFin * (11 * Internal.flowCredit t tailC high eventsC events eventsF i cred /
    (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * t.perIncrement *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat)

/-- The flow gain of a key whose rise is on its kept arm, or that R's registry does not hold.

On the other arm the rise is the key's whole headroom, which holds its gains already.

A key that R's registry does not hold is charged here only in the low regime.

At a high rate the reserve charges it up to the cap. -/
def flowK (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  if t.keptArm i = true ∨ (i ∉ t.positions ∧ t.gainHigh = false) then
    Internal.flowGain t tailC high eventsC events eventsF i cred
  else 0

/-- One unit of gain for a key with any flow.

A flow can raise the key's effective balance by one more increment than its rewards alone. -/
def unitK (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  if 0 < Internal.flowCredit t tailC high eventsC events eventsF i cred then t.unitGain else 0

/-- The terms of a key's rise that the third window adds.

They are its sync debits on the shared segment, its flow gain and its unit.

They also include the leak that its sync debits on R's branch induce. -/
def keyExtra (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (tailC : Run config checks x' y') (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i : ℕ)
    (cred : ℕ := Internal.credC tailC high i) : ℕ :=
  Internal.syncD eventsF i + Internal.flowK t tailC high eventsC events eventsF i cred +
    Internal.unitK t tailC high eventsC events eventsF i cred + Internal.inducedR t tail i

/-- A quantity of the sync events, summed over all events with the others at zero. -/
theorem sum_map_sync (events : List (BalanceEvent preset))
    (k : BalanceEvent preset → ℕ) :
    (events.map fun e => if e.source = .sync then k e else 0).sum =
      ((events.filter (·.source = .sync)).map k).sum := by
  induction events with
  | nil => rfl
  | cons e rest ih =>
    by_cases sync : e.source = .sync
    · simp [sync, ih]
    · simp [sync, ih]

/-- The sync debits of a key over a list of events are the debits of its sync events. -/
theorem sum_syncDebit_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    (events.map (Internal.syncDebit v)).sum =
      ((events.filter (·.source = .sync)).map (Internal.keyDebit v)).sum :=
  Internal.sum_map_sync events (Internal.keyDebit v)

/-- The rounding band of a key is the band if the key has a sync debit, and zero otherwise. -/
theorem bandR_eq (events : List (BalanceEvent preset)) (v : ℕ) :
    Internal.bandR events v = if 0 < (events.map (Internal.syncDebit v)).sum then
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 else 0 := by
  unfold Internal.bandR
  rw [← Internal.sum_syncDebit_eq]

/-- A key's credit in an event is at most the event's credit limit. -/
private theorem keyCredit_le_creditLimit (i : ℕ) (e : BalanceEvent preset)
    (bounded : e.credits ≤ e.creditLimit) : Internal.keyCredit i e ≤ e.creditLimit := by
  refine le_trans ?_ bounded
  unfold Internal.keyCredit
  by_cases within : i < e.after.state.balances.data.size
  · exact Finset.single_le_sum (f := fun j =>
      actualBalanceAt e.after j - actualBalanceAt e.before j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr within)
  · have missing : actualBalanceAt e.after i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt within)]
    omega

/-- The stages of an epoch replay record no slashing event with a credit limit. -/
private theorem epochReplayAction_slashing_credit {fork : Fork} (k : EpochStage)
    {pre post : BalanceReplay preset fork}
    (held : ∀ e ∈ pre.2, e.source = .slashings → e.creditLimit = 0)
    (ok : epochReplayAction (config := config) (checks := checks) k pre = .ok post) :
    ∀ e ∈ post.2, e.source = .slashings → e.creditLimit = 0 := by
  have carried : ∀ {a : BeaconState preset fork → Except TransitionError (BeaconState preset fork)},
      carryBalance a pre = .ok post → ∀ e ∈ post.2, e.source = .slashings → e.creditLimit = 0 := by
    intro a ok'
    simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok'
    obtain ⟨_, _, rfl⟩ := ok'
    exact held
  have unchanged : (pure pre : Except TransitionError (BalanceReplay preset fork)) = .ok post →
      ∀ e ∈ post.2, e.source = .slashings → e.creditLimit = 0 := by
    intro ok'
    simp only [pure, Except.pure, Except.ok.injEq] at ok'
    subst ok'
    exact held
  cases k
  case justification =>
    simp only [epochReplayAction] at ok
    exact carried ok
  case inactivity =>
    simp only [epochReplayAction] at ok
    split at ok
    · exact carried ok
    · exact unchanged ok
  case rewards =>
    simp only [epochReplayAction] at ok
    refine replayRewards_induction (config := config)
      (fun p => ∀ e ∈ p.2, e.source = .slashings → e.creditLimit = 0) ?_ ?_ held ok
    · intro pre' post' index reward held' ok'
      obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok'
      rw [events]
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held' e old source
      · obtain rfl := List.mem_singleton.mp new
        exact absurd source (by simp)
    · intro src pre' post' index penalty pen held' ok'
      obtain ⟨_, _, _, _, events⟩ := recordBalance_single ok'
      rw [events]
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held' e old source
      · obtain rfl := List.mem_singleton.mp new
        have same : src = .slashings := source
        rcases pen with h | h <;> rw [h] at same <;> cases same
  case registry =>
    simp only [epochReplayAction] at ok
    exact carried ok
  case slashings =>
    simp only [epochReplayAction, recordBalance, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨⟨credit, debit⟩, limited, after, computed, rfl⟩ := ok
    simp only [Prod.mk.injEq] at limited
    obtain ⟨_, _, zero, _⟩ := limited
    intro e member source
    rcases List.mem_append.mp member with old | new
    · exact held e old source
    · obtain rfl := List.mem_singleton.mp new
      exact zero.symm
  case eth1Reset =>
    simp only [epochReplayAction] at ok
    split at ok
    · exact carried ok
    · exact unchanged ok
  case pendingDeposits | pendingConsolidations =>
    simp only [epochReplayAction] at ok
    split at ok
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
      obtain ⟨_, _, rfl⟩ := ok
      intro e member source
      rcases List.mem_append.mp member with old | new
      · exact held e old source
      · obtain rfl := List.mem_singleton.mp new
        exact absurd source (by simp)
    · exact unchanged ok
  all_goals
    simp only [epochReplayAction] at ok
    exact unchanged ok

/-- A slot step records no slashing event with a credit limit. -/
private theorem slot_slashing_credit {m n : ForkedBeaconState preset}
    {ok : advanceSlotAcross config checks m = .ok n} (early : n.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (replayed : (Step.slot ok).balanceEvents = .ok events) :
    ∀ e ∈ events, e.source = .slashings → e.creditLimit = 0 := by
  intro e member source
  obtain ⟨advanced, cached, crossings, -, -, -, crossingOk, split⟩ :=
    Step.balanceEvents_slot ok early replayed
  have notCrossing : e ∉ crossings := fun inside => by
    have crossing := upgradeBalanceReplay_crossing crossingOk e inside
    rw [crossing] at source
    cases source
  rcases split with ⟨-, rfl⟩ | ⟨middle, updated, recorded, recordOk, -, -, -, shape, -⟩
  · exact absurd member notCrossing
  · rw [shape] at member
    rcases List.mem_append.mp member with inside | inside
    · exact EpochTrace.induction_on
        (fun _ p => ∀ e ∈ p.2, e.source = .slashings → e.creditLimit = 0)
        (epochBalanceReplay_trace recordOk) (fun e member => by simp at member)
        (fun k _ a b ok held => epochReplayAction_slashing_credit k held ok) e inside source
    · exact absurd inside notCrossing

/-- A block event credits a key only through proposer, whistleblower or sync rewards.

A deposit event of a block credits nothing from Electra. -/
private theorem block_event_credit {g : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨fork, s⟩) (genesis : Genesis config checks g)
    (early : fork < .glamsterdam) (electra : .pectra ≤ fork) (i : ℕ)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ∀ e ∈ events, Internal.keyCredit i e ≤
      (if e.source = .rewards ∨ e.source = .consolidations then Internal.keyCredit i e else 0) +
        (if e.source = .slashings then Internal.keyCredit i e else 0) + Internal.syncCredit i e :=
          by
  intro e member
  obtain ⟨fk, positive⟩ := Step.balanceEvents_credit_sources
    (Step.block engine signed due ok) early (run_justified_separated shared genesis).1
    replayed e member
  have limit := keyCredit_le_creditLimit i e (bounded e member)
  by_cases rc : e.source = .rewards ∨ e.source = .consolidations
  · simp only [rc, ↓reduceIte]
    omega
  by_cases sl : e.source = .slashings
  · simp [sl]
  by_cases sy : e.source = .sync
  · simp [sy, Internal.syncCredit, Internal.keyCredit]
  have zero : e.creditLimit = 0 := by
    by_contra pos
    rcases positive (Nat.pos_of_ne_zero pos) with h | h | h | h | h
    · exact rc (.inl h)
    · exact sy h
    · exact sl h
    · exact pos (funding_block_events (config := config) (checks := checks) early engine
        signed.message (Step.balanceEvents_block early replayed) e member h
        (Nat.le_trans electra fk))
    · exact rc (.inr h)
  simp only [rc, sl, ↓reduceIte]
  omega

/-- Outside epoch rewards, a slot event credits only deposits, consolidations or sync rewards. -/
private theorem slot_event_credit {g m n : ForkedBeaconState preset}
    {ok : advanceSlotAcross config checks m = .ok n}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (early : n.fork < .glamsterdam) (i : ℕ) {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ∀ e ∈ events, e.source ≠ .rewards → Internal.keyCredit i e ≤
      (if e.source = .consolidations ∨ e.source = .deposits then Internal.keyCredit i e else 0) +
        Internal.syncCredit i e := by
  intro e member notRewards
  obtain ⟨-, positive⟩ := Step.balanceEvents_credit_sources (Step.slot ok) early
    (run_justified_separated shared genesis).1 replayed e member
  have limit := keyCredit_le_creditLimit i e (bounded e member)
  by_cases cd : e.source = .consolidations ∨ e.source = .deposits
  · simp [cd]
  by_cases sy : e.source = .sync
  · simp [sy, Internal.syncCredit, Internal.keyCredit]
  have zero : e.creditLimit = 0 := by
    by_contra pos
    rcases positive (Nat.pos_of_ne_zero pos) with h | h | h | h | h
    · exact notRewards h
    · exact sy h
    · exact pos (slot_slashing_credit early replayed e member h)
    · exact cd (.inr h)
    · exact cd (.inl h)
  simp only [cd, ↓reduceIte]
  omega

/-- A bound for each selected event gives the bound for the sums of the credits that it splits. -/
private theorem sum_credits_split (events : List (BalanceEvent preset))
    (f g : BalanceEvent preset → ℕ) (r p q : BalanceSource → Bool)
    (each : ∀ e ∈ events, r e.source = true →
      f e ≤ (if p e.source = true then f e else 0) + (if q e.source = true then f e else 0) +
        g e) :
    ((events.filter (r ·.source)).map f).sum ≤ ((events.filter (p ·.source)).map f).sum +
      ((events.filter (q ·.source)).map f).sum + (events.map g).sum := by
  have ite (p : BalanceSource → Bool) : ((events.filter (p ·.source)).map f).sum =
      (events.map fun e => if p e.source = true then f e else 0).sum := by
    rw [List.sum_map_ite (fun e : BalanceEvent preset => p e.source = true) f (fun _ => 0)]
    simp
  rw [ite, ite, ite, ← List.sum_map_add, ← List.sum_map_add]
  refine List.sum_le_sum fun e member => ?_
  by_cases hr : r e.source = true
  · simp only [hr, ↓reduceIte]
    exact each e member hr
  · simp only [hr]
    exact Nat.zero_le _

/-- A filter that selects no event sums to zero. -/
private theorem sum_filter_none (events : List (BalanceEvent preset))
    (f : BalanceEvent preset → ℕ) :
    ((events.filter fun _ => false).map f).sum = 0 := by
  induction events with
  | nil => rfl
  | cons e rest ih => simp

/-- Proposer, whistleblower and sync rewards bound a key's block credits. -/
private theorem block_credit_split {g : ForkedBeaconState preset} {fork : Fork}
    {s t : BeaconState preset fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {due : upgradeDue config ⟨fork, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨fork, s⟩) (genesis : Genesis config checks g)
    (early : fork < .glamsterdam) (electra : .pectra ≤ fork) (i : ℕ)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    (events.map (Internal.keyCredit i)).sum ≤
      ((events.filter fun x => decide (x.source = .rewards ∨ x.source = .consolidations)).map
        (Internal.keyCredit i)).sum +
      ((events.filter fun x => decide (x.source = .slashings)).map (Internal.keyCredit i)).sum +
      (events.map (Internal.syncCredit i)).sum := by
  have each := block_event_credit shared genesis early electra i replayed bounded
  simpa using sum_credits_split events (Internal.keyCredit i) (Internal.syncCredit i) (fun _ =>
    true)
    (fun s => decide (s = .rewards ∨ s = .consolidations)) (fun s => decide (s = .slashings))
    (fun e m _ => by simpa using each e m)

/-- The slot credits of a step to a key, other than rewards, fit consolidations, deposits, sync. -/
private theorem slot_credit_split {g m n : ForkedBeaconState preset}
    {ok : advanceSlotAcross config checks m = .ok n}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (early : n.fork < .glamsterdam) (i : ℕ) {events : List (BalanceEvent preset)}
    (replayed : (Step.slot ok).balanceEvents = .ok events)
    (bounded : ∀ e ∈ events, e.credits ≤ e.creditLimit) :
    ((events.filter fun x => decide (x.source ≠ .rewards)).map (Internal.keyCredit i)).sum ≤
      ((events.filter fun x => decide (x.source = .consolidations ∨ x.source = .deposits)).map
        (Internal.keyCredit i)).sum +
      ((events.filter fun _ => false).map (Internal.keyCredit i)).sum + (events.map
        (Internal.syncCredit i)).sum := by
  have each := slot_event_credit shared genesis early i replayed bounded
  exact sum_credits_split events (Internal.keyCredit i) (Internal.syncCredit i)
    (fun s => decide (s ≠ .rewards)) (fun s => decide (s = .consolidations ∨ s = .deposits))
    (fun _ => false) (fun e m notRewards => by simpa using each e m (by simpa using notRewards))

/-- The events of a step are within their credit limits. -/
private theorem step_events_bounded {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam)
    {events : List (BalanceEvent preset)} (ok : step.balanceEvents = .ok events) :
    ∀ e ∈ events, e.credits ≤ e.creditLimit := by
  have run := DirectSafety.Apriori.Internal.single_balanceEvents step ok
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared (Run.nil.snoc step)
    genesis early (getCurrentEpoch n.state).toNat
  rw [run] at foundOk
  cases foundOk
  exact fun e member => (bounded e member).1

/-- Proposer, whistleblower and sync rewards bound a key's block credits. -/
private theorem block_credit_le_sources {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (notSlot : ∀ ok, step ≠ Step.slot ok)
    (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork) (i : ℕ)
    {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    Internal.stepCredit (fun _ => true) (fun _ => true) i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      Internal.stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (Internal.syncCredit i)).sum := by
  have bounded := step_events_bounded shared genesis step early replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_split shared genesis early electra i replayed bounded
    simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some, List.filter_true]
      at split ⊢
    exact split
  | slot ok => exact absurd rfl (notSlot ok)

/-- The credits of a block step to a key are at most its gross credits.

A block step has no consolidation event, and its other sources credit nothing.

The step counts all its credits on the left.

On the right it counts only those of rewards, slashings and sync. -/
theorem block_credit_le_gross {g : ForkedBeaconState preset} {f : Fork}
    {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (genesis : Genesis config checks g)
    (early : f < .glamsterdam) (electra : .pectra ≤ f) (i : ℕ) :
    Internal.stepCredit (fun _ => true) (fun _ => true) i (Step.block engine signed due ok) ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
        false) i
        (Step.block engine signed due ok) := by
  obtain ⟨events, replayed⟩ := (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩).balanceEvents_ok early
  have bounded := step_events_bounded shared genesis (Step.block engine signed due ok) early
    replayed
  have noCons := Internal.blockReplay_noConsolidations electra early engine s signed.message
    (Step.balanceEvents_block early replayed)
  have split : (events.map (Internal.keyCredit i)).sum ≤ ((events.filter fun e => decide
      (e.source = .rewards ∨ e.source = .slashings ∨ e.source = .sync)).map (Internal.keyCredit
        i)).sum := by
    simpa using sum_credits_split events (Internal.keyCredit i) (fun _ => 0) (fun _ => true)
      (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false)
      fun e member _ => by
        have each := block_event_credit shared genesis early electra i replayed bounded e member
        by_cases kept : e.source = .rewards ∨ e.source = .slashings ∨ e.source = .sync
        · simp [kept]
        · simp only [not_or] at kept
          simp [kept.1, kept.2.1, kept.2.2, noCons e member, Internal.syncCredit] at each ⊢
          omega
  simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some]
  simpa using split

/-- A block step raises the balance of a key by at most its gross credits. -/
theorem block_balance_le_gross {g : ForkedBeaconState preset} {f : Fork}
    {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (genesis : Genesis config checks g)
    (early : f < .glamsterdam) (electra : .pectra ≤ f) (i : ℕ) :
    actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i + Internal.stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        (Step.block engine signed due ok) := by
  obtain ⟨events, replayed⟩ := (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩).balanceEvents_ok early
  have base := Internal.step_balance_le_events (Step.block engine signed due ok :
    Step config checks ⟨f, s⟩ ⟨f, t⟩) early i replayed
  have credit := Internal.block_credit_le_gross (due := due) (ok := ok) shared genesis early electra
    i
  simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
    List.filter_true] at credit ⊢
  omega

/-- The replay bounds credits by source, using net credits for a block step. -/
theorem step_credit_le_sources {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork)
    (i : ℕ) {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    Internal.stepNet i step + Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards))
      i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      Internal.stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (Internal.syncCredit i)).sum := by
  have bounded := step_events_bounded shared genesis step early replayed
  have base := Internal.step_balance_le_events step early i replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_le_sources shared genesis (Step.block engine signed due ok)
      (by intro ok' h; cases h) early electra i replayed
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none, List.filter_true] at base split ⊢
    omega
  | slot ok =>
    have split := slot_credit_split shared genesis early i replayed bounded
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at split ⊢
    omega

/-- The gross credits of a step, with its slot credits other than rewards, are within the sources.

The sources include proposer and whistleblower rewards, deposits, consolidations and sync rewards.

A block step's net rise is within its gross credits.

Its slot credits other than rewards are at most those of consolidations and deposits. -/
private theorem step_gross_le_sources {g m n : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (step : Step config checks m n) (early : n.fork < .glamsterdam) (electra : .pectra ≤ m.fork)
    (i : ℕ) {events : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok events) :
    Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ =>
      false) i
        step + Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      Internal.stepCredit (fun s => decide (s = .rewards ∨ s = .consolidations))
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step +
      Internal.stepCredit (fun s => decide (s = .slashings)) (fun _ => false) i step +
      (events.map (Internal.syncCredit i)).sum ∧
    Internal.stepNet i step ≤ Internal.stepCredit
      (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i step ∧
    Internal.stepCredit (fun _ => false) (fun s => decide (s ≠ .rewards)) i step ≤
      Internal.stepCredit (fun _ => false)
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i step := by
  have bounded := step_events_bounded shared genesis step early replayed
  cases step with
  | block engine signed due ok =>
    have split := block_credit_split shared genesis early electra i replayed bounded
    have gross := Internal.block_balance_le_gross (engine := engine) (signed := signed) (due := due)
      (ok := ok) shared genesis early electra i
    have part : ((events.filter fun x => decide
        (x.source = .rewards ∨ x.source = .slashings ∨ x.source = .sync)).map (Internal.keyCredit
          i)).sum ≤
        (events.map (Internal.keyCredit i)).sum :=
      (((List.filter_sublist).map _).sum_le_sum fun _ _ => Nat.zero_le _)
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at gross part split ⊢
    omega
  | slot ok =>
    have split := slot_credit_split shared genesis early i replayed bounded
    have zero := (Internal.slot_syncDebit_zero electra ok early replayed i).2
    simp only [Internal.stepNet, Internal.stepCredit, replayed, Except.toOption, Option.getD_some,
      sum_filter_none] at split ⊢
    omega

/-- The replay bounds credits by source, using gross credits for block steps.

A block step's net rise is within its gross credits, so the net credits of the run are too.

Its slot credits other than epoch rewards are at most those of consolidations and deposits. -/
theorem credits_le_sources {g x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (tail : Run config checks x y) (early : y.fork < .glamsterdam) (electra : .pectra ≤ x.fork)
    (i high : ℕ) {events : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events) :
    Internal.grossScan i high tail + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
      .rewards)) i high
      tail) ≤ Internal.credC tail high i + Internal.whistC tail high i + (events.map
        (Internal.syncCredit i)).sum ∧
    Internal.netScan i high tail ≤ Internal.grossScan i high tail ∧
    (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high tail) ≤
      (Internal.creditScan (fun _ => false)
        (fun s => decide (s = .consolidations ∨ s = .deposits)) i high tail) := by
  induction tail generalizing events with
  | nil =>
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp [Internal.credC, Internal.whistC, Internal.grossScan, Internal.netScan_nil,
      Internal.creditScan_nil]
  | @snoc middle last pre step ih =>
    simp only [Run.balanceEvents, bind_ok_iff] at replayed
    obtain ⟨prior, priorOk, rest⟩ := replayed
    obtain ⟨previous, previousNet, previousSlot⟩ :=
      ih (Nat.lt_of_le_of_lt step.chainStep.fork_le early) priorOk
    by_cases selected : (getCurrentEpoch middle.state).toNat ≤ high + 1
    · simp only [selected, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨added, addedOk, rfl⟩ := rest
      obtain ⟨one, oneNet, oneSlot⟩ := step_gross_le_sources (shared.append pre) genesis step early
        (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) i addedOk
      unfold Internal.credC Internal.whistC Internal.grossScan at previous ⊢
      unfold Internal.grossScan at previousNet
      simp only [Internal.netScan_snoc, Internal.creditScan_snoc, selected, ↓reduceIte,
        List.map_append,
        List.sum_append]
      exact ⟨by omega, by omega, by omega⟩
    · simp only [selected, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
      obtain rfl := rest
      unfold Internal.credC Internal.whistC Internal.grossScan at previous ⊢
      unfold Internal.grossScan at previousNet
      simp only [Internal.netScan_snoc, Internal.creditScan_snoc, selected, ↓reduceIte]
      exact ⟨previous, previousNet, previousSlot⟩

/-- The credits of a switch step, whole, and of the runs around it are at most the sources.

The credits before the step are read net, and then gross. -/
theorem flip_credits_le_sources {g x s s' y : ForkedBeaconState preset}
    (shared : Run config checks g x) (genesis : Genesis config checks g)
    (pre : Run config checks x s) (step : Step config checks s s') (post : Run config checks s' y)
    (notSlot : ∀ ok, step ≠ Step.slot ok) (early : y.fork < .glamsterdam)
    (electra : .pectra ≤ x.fork) (i high : ℕ) (inside : (getCurrentEpoch s.state).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)}
    (replayed : ((pre.snoc step).append post).balanceEvents high = .ok events) :
    (Internal.netScan i high pre + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
      .rewards)) i high
        pre) + Internal.stepCredit (fun _ => true) (fun _ => true) i step +
      (Internal.netScan i high post + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
        .rewards)) i high
        post)) ≤ Internal.credC ((pre.snoc step).append post) high i +
      Internal.whistC ((pre.snoc step).append post) high i + (events.map (Internal.syncCredit
        i)).sum) ∧
    (Internal.grossScan i high pre + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
      .rewards)) i high
        pre) + Internal.stepCredit (fun _ => true) (fun _ => true) i step +
      (Internal.netScan i high post + (Internal.creditScan (fun _ => false) (fun s => decide (s ≠
        .rewards)) i high
        post)) ≤ Internal.credC ((pre.snoc step).append post) high i +
      Internal.whistC ((pre.snoc step).append post) high i + (events.map (Internal.syncCredit
        i)).sum) := by
  have s'Early : s'.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
  have sEarly : s.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le s'Early
  obtain ⟨e1, replayed1⟩ := pre.balanceEvents_ok sEarly high
  obtain ⟨es, replayedS⟩ := step.balanceEvents_ok s'Early
  obtain ⟨e2, replayed2⟩ := post.balanceEvents_ok early high
  have snoc : (pre.snoc step).balanceEvents high = .ok (e1 ++ es) := by
    simp [Run.balanceEvents, replayed1, replayedS, inside]
    rfl
  have whole := DirectSafety.Apriori.Internal.balanceEvents_append (pre.snoc step) post high snoc
    replayed2
  rw [whole] at replayed
  obtain rfl := Except.ok.inj replayed
  have first := Internal.credits_le_sources shared genesis pre sEarly electra i high replayed1
  have last := Internal.credits_le_sources (shared.append (pre.snoc step)) genesis post early
    (Nat.le_trans electra (fork_le_of_chainSteps (pre.snoc step).chainSteps)) i high replayed2
  have middle := block_credit_le_sources (shared.append pre) genesis step notSlot s'Early
    (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps)) i replayedS
  unfold Internal.credC Internal.whistC
  rw [Internal.creditScan_append, Internal.creditScan_append, Internal.creditScan_snoc,
    Internal.creditScan_snoc]
  simp only [inside, ↓reduceIte]
  unfold Internal.credC Internal.whistC at first last
  simp only [List.map_append, List.sum_append] at first last ⊢
  exact ⟨by omega, by omega⟩

/-- The key's effective balance when its exit starts on a run, or 0.

It is the amount of the key's departure charge, which reads the effective balance at the exit call.

A key has a charge only if its exit was not assigned at the run's start.

Only a charge whose exit epoch is at most the run's last epoch counts. -/
def exitQ {x y : ForkedBeaconState preset} (tail : Run config checks x y) (v : ℕ) : ℕ :=
  ((tail.departureCharges.find? fun c =>
      c.index == v && decide (c.epoch ≤ (getCurrentEpoch y.state).toNat)).map (·.amount)).getD 0

/-- Whether a run has the key's departure charge, and the epoch rewards of the steps from it on.

The step with the charge counts too, since the key's epoch pass in it follows its exit.

Only steps starting at or before epoch `high + 1` contribute rewards. -/
def riseScan (v high : ℕ) {x : ForkedBeaconState preset} :
    {y : ForkedBeaconState preset} → Run config checks x y → Bool × ℕ
  | _, .nil => (false, 0)
  | _, .snoc (middle := m) pre step =>
    let before := Internal.riseScan v high pre
    (before.1 || step.departureCharges.any (·.index == v),
      if (before.1 = true ∨ step.departureCharges.any (·.index == v) = true) ∧
          (getCurrentEpoch m.state).toNat ≤ high + 1 then
        before.2 + Internal.epochRewards v step
      else before.2)

/-- The key's rise on a run after its exit starts there.

It is one upward band for the rise of the effective balance beyond the key's epoch rewards.

It adds those rewards over the slot steps that come after the step with its departure charge.

It is 0 for a key whose exit does not start on the run. -/
def riseQ {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (high v : ℕ) : ℕ :=
  if (Internal.riseScan v high tail).1 = true then preset.upwardBand + (Internal.riseScan v high
    tail).2 else 0

/-! ### The keys that a run credits -/

/-- Net block credits to a key add across consecutive runs. -/
theorem netScan_append (v high : ℕ) {x m y : ForkedBeaconState preset}
    (pre : Run config checks x m) (post : Run config checks m y) :
    Internal.netScan v high (pre.append post) = Internal.netScan v high pre + Internal.netScan v
      high post := by
  induction post with
  | nil => rfl
  | snoc post step ih =>
    change Internal.netScan v high ((pre.append post).snoc step) = _
    rw [Internal.netScan_snoc, Internal.netScan_snoc, ih]
    split <;> omega

/-- A key keeps its public key at its position along a run. -/
private theorem key_persists {x y : ForkedBeaconState preset} (run : Run config checks x y)
    {i : ℕ} {w : Validator} (found : x.state.validators.data[i]? = some w) :
    ∃ w', y.state.validators.data[i]? = some w' ∧ w'.pubkey = w.pubkey :=
  validators_getElem?_of_validatorKeys_prefix
    (validatorKeys_prefix_and_distinct_of_chainSteps run.chainSteps).1 found

/-- A sync aggregate changes the balance of a position only if its key is in the committee.

The position is then the one of a validator that holds a seat, which the committee keeps.

Otherwise the position is the proposer's, and its balance rises. -/
private theorem sync_moved_seat {f : Fork} {c t : BeaconState preset f} (altair : .altair ≤ f)
    {aggregate : SyncAggregate preset}
    (synced : processSyncAggregate config checks c altair aggregate = .ok t)
    (matched : BalancesMatch t) {i : ℕ}
    (moved : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≠
      actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i) :
    (∃ w, t.validators.data[i]? = some w ∧
      w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList) ∨
    ∃ proposer, getBeaconProposerIndex c = .ok proposer ∧ proposer.toNat = i ∧
      actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i <
        actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i := by
  obtain ⟨vals, comm⟩ := BlockLedger.processSyncAggregate_kept synced
  have sizes := sameSizes_processSyncAggregate synced
  have matchedC : BalancesMatch c := by
    unfold BalancesMatch at matched ⊢
    rw [← sizes.1, ← sizes.2]
    exact matched
  have inside : i < c.balances.data.size := by
    by_contra outside
    have missing : actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i = 0 := by
      simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside)]
    have outT : t.balances.data[i]? = none :=
      Array.getElem?_eq_none (by have := sizes.2; omega)
    have missingT : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i = 0 := by
      simp [actualBalanceAt, outT]
    omega
  have insideV : i < c.validators.data.size := by
    unfold BalancesMatch at matchedC
    omega
  obtain ⟨w, found⟩ : ∃ w, c.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem insideV⟩
  have foundT : t.validators.data[i]? = some w := by rw [vals]; exact found
  by_cases seat : w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList
  · exact .inl ⟨w, foundT, seat⟩
  refine .inr ?_
  have unseated : w.pubkey ∉ (c.currentSyncCommittee altair).value.pubkeys.toList := by
    rw [← congrFun comm altair]
    exact seat
  obtain ⟨reward, proposerReward, members, chosen, -, -, membersOk, signed, balances⟩ :=
    processSyncAggregate_balance synced
  have seatless : ∀ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.1.toNat ≠ i := signers_elsewhere_of_unseated membersOk found unseated
  obtain ⟨b, held⟩ : ∃ b, c.balances.data[i]? = some b :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨final, atFinal, value⟩ := balances i b held
  have low := (syncRewards_bounds (reward := reward.toNat)
    (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).2
    (fun member inside _ => seatless member inside)
  rw [← value] at low
  simp only [actualBalanceAt, held, atFinal, Option.map_some, Option.getD_some] at moved ⊢
  by_cases signer : ∃ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
      member.2 = true ∧ chosen.toNat = i
  · obtain ⟨member, inside, signedBit, same⟩ := signer
    exact ⟨chosen, signed ⟨member, inside, signedBit⟩, same, by omega⟩
  · exfalso
    have high := (syncRewards_bounds (reward := reward.toNat)
      (proposerReward := proposerReward.toNat) (index := i) (chosen := chosen) _ b.toNat).1
      (fun member inside bit => ⟨seatless member inside,
        fun same => signer ⟨member, inside, bit, same⟩⟩)
    rw [← value] at high
    omega

/-- A sync aggregate lowers the balance of a position only if its key is in the committee.

The position is then the one of a validator that holds a seat, which the committee keeps. -/
private theorem sync_debit_seat {f : Fork} {c t : BeaconState preset f} (altair : .altair ≤ f)
    {aggregate : SyncAggregate preset}
    (synced : processSyncAggregate config checks c altair aggregate = .ok t)
    (matched : BalancesMatch t) {i : ℕ}
    (lowered : actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i <
      actualBalanceAt (⟨f, c⟩ : ForkedBeaconState preset) i) :
    ∃ w, t.validators.data[i]? = some w ∧
      w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList := by
  rcases sync_moved_seat altair synced matched (Nat.ne_of_lt lowered) with seat | ⟨_, _, _, risen⟩
  · exact seat
  · omega

/-- The events of a block's passes credit no key but the proposer, from the sources that matter.

None of them has a sync or consolidation source.

A rewards or slashings event credits only the proposer. -/
private def PassCredits (proposer : ℕ) (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source ≠ .sync ∧ e.source ≠ .consolidations ∧
    ((e.source = .rewards ∨ e.source = .slashings) →
      ∀ i, proposer ≠ i → Internal.keyCredit i e = 0)

/-- A carried pass records nothing. -/
private theorem PassCredits.carry {f : Fork} {proposer : ℕ}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (held : PassCredits proposer pre.2)
    (ok : carryBalance action pre = .ok post) : PassCredits proposer post.2 := by
  rw [(Internal.carryBalance_cases ok).2]
  exact held

/-- A recorded pass adds an event.

A rewards or slashings event credits only the proposer. -/
private theorem PassCredits.record {f : Fork} {proposer : ℕ} {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    {pre post : BalanceReplay preset f} (held : PassCredits proposer pre.2)
    (ok : recordBalance source limits action pre = .ok post)
    (notSync : source ≠ .sync) (notConsolidation : source ≠ .consolidations)
    (lowered : (source = .rewards ∨ source = .slashings) → ∀ t, action pre.1 = .ok t →
      ∀ i, proposer ≠ i →
        actualBalanceAt (⟨f, t⟩ : ForkedBeaconState preset) i ≤
          actualBalanceAt (⟨f, pre.1⟩ : ForkedBeaconState preset) i) :
    PassCredits proposer post.2 := by
  obtain ⟨_, _, _, computed, events⟩ := recordBalance_single ok
  rw [events]
  intro e member
  rcases List.mem_append.mp member with old | new
  · exact held e old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨notSync, notConsolidation, fun source i other =>
      Nat.sub_eq_zero_of_le (lowered source post.1 computed i other)⟩

/-- A pass that does not lower a balance, and keeps the sizes, does not raise it. -/
private theorem actualBalanceAt_le_of_down {f : Fork} {s u : BeaconState preset f}
    (sizes : SameSizes s u) {i : ℕ} (down : BalanceDown i s u) :
    actualBalanceAt (⟨f, u⟩ : ForkedBeaconState preset) i ≤
      actualBalanceAt (⟨f, s⟩ : ForkedBeaconState preset) i := by
  by_cases inside : i < s.balances.data.size
  · obtain ⟨b, held⟩ : ∃ b, s.balances.data[i]? = some b :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨later, found, le⟩ := down b held
    simp only [actualBalanceAt, held, found, Option.map_some, Option.getD_some]
    exact UInt64.le_iff_toNat_le.mp le
  · have outS : s.balances.data[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt inside)
    have outU : u.balances.data[i]? = none :=
      Array.getElem?_eq_none (by have := sizes.2; omega)
    simp [actualBalanceAt, outS, outU]

/-- The replay of a block ends with its sync pass, after passes that credit only its proposer.

The proposer of the block is the one that the state before the sync pass reads.

Earlier passes record neither sync nor consolidation events.

The mixes must span more than the seed lookahead plus two epochs. -/
private theorem blockReplay_proposer_credits {fork : Fork} {a t : BeaconState preset fork}
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (electra : .pectra ≤ fork) (early : fork < .glamsterdam)
    {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine a block =
      .ok (t, events)) :
    ∃ (c : BeaconState preset fork) (rest : List (BalanceEvent preset)) (altair : .altair ≤ fork)
      (aggregate : SyncAggregate preset) (credit debit : ℕ),
      events = rest ++ [⟨.sync, ⟨fork, c⟩, ⟨fork, t⟩, credit, debit⟩] ∧
      getBeaconProposerIndex c = .ok block.proposerIndex ∧
      processSyncAggregate config checks c altair aggregate = .ok t ∧
      PassCredits block.proposerIndex.toNat rest ∧
      getBeaconProposerIndex a = .ok block.proposerIndex := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) electra
  have before : fork < .hegota := Nat.lt_trans early (by decide)
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt early
  have normalized := replay
  unfold blockBalanceReplay at normalized
  simp only [altair, bellatrix, electra, ↓reduceDIte] at normalized
  simp only [← bind_assoc] at normalized
  simp only [bind_assoc] at normalized
  simp only [bind_ok_iff, ensure_ok_iff] at normalized
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, x1, x2, x3,
    x4, proposed, proposedOk, slashed, slashedOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, requested, requestedOk, withdrawn, withdrawnOk,
    consolidated, consolidatedOk, syncOk⟩ := normalized
  -- The proposer of the block is read at the state before its operations.
  have headerOk : processBlockHeader a block = .ok headed.1 :=
    (Internal.carryBalance_cases headedOk).1
  have input : OperationsInput config checks engine a block voted.1 :=
    ⟨a, headed.1, executed.1, revealed.1, by simp [notGloas, pure, Except.pure], headerOk,
      by
        obtain ⟨_, _, _, action, _⟩ := recordBalance_single executedOk
        simpa only [bellatrix, ↓reduceDIte] using action,
      (Internal.carryBalance_cases revealedOk).1,
      by simpa only [before, ↓reduceDIte] using (Internal.carryBalance_cases votedOk).1⟩
  have read := (operationsInput_proposer apart input).1
  -- The operations apply the actions of the replay in order, so they keep that proposer.
  have operated : processOperations config checks voted.1 block.body a.latestBlockHeader.slot =
      .ok consolidated.1 := by
    have pOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ proposedOk
    have sOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ slashedOk
    have aOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ attestedOk
    have dOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ depositedOk
    have cOk := DirectSafety.Apriori.Internal.recordFold_plain _ _ _ _ _ consolidatedOk
    simp only [Array.foldlM_toList] at pOk sOk aOk dOk cOk
    unfold processOperations
    simp only [notGloas, electra, ↓reduceDIte, bind_ok_iff, ensure_ok_iff, processExecutionRequests]
    exact ⟨x1, x2, x3, x4, proposed.1, pOk, slashed.1, sOk, attested.1, aOk, deposited.1, dOk,
      exited.1, (Internal.carryBalance_cases exitedOk).1, changed.1,
      (Internal.carryBalance_cases changedOk).1, requested.1,
      (Internal.carryBalance_cases requestedOk).1, withdrawn.1,
      (Internal.carryBalance_cases withdrawnOk).1, cOk⟩
  have link := (processOperations_proposer apart operated).1.trans read
  -- The passes before the operations record no credit but the proposer's.
  have base : PassCredits block.proposerIndex.toNat ([] : List (BalanceEvent preset)) :=
    fun e member => by simp at member
  have start : PassCredits block.proposerIndex.toNat voted.2 :=
    (((base.carry headedOk).record executedOk (by decide) (by decide)
      fun h => absurd h (by decide)).carry revealedOk).carry votedOk
  have step : ∀ {source : BalanceSource}
      {limits : BeaconState preset fork → Except TransitionError (Nat × Nat)}
      {action : BeaconState preset fork → Except TransitionError (BeaconState preset fork)}
      (pre post : BalanceReplay preset fork), (source = .rewards ∨ source = .slashings) →
      (getBeaconProposerIndex pre.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat pre.2) →
      recordBalance source limits action pre = .ok post →
      (∀ s u, action s = .ok u → getBeaconProposerIndex s = .ok block.proposerIndex →
        SameSizes s u ∧ (∀ i, block.proposerIndex.toNat ≠ i → BalanceDown i s u) ∧
          getBeaconProposerIndex u = .ok block.proposerIndex) →
      getBeaconProposerIndex post.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat post.2 := by
    intro source limits action pre post src ⟨seen, held⟩ ok props
    obtain ⟨_, _, _, actionOk, _⟩ := recordBalance_single ok
    obtain ⟨-, -, kept⟩ := props _ _ actionOk seen
    refine ⟨kept, held.record ok ?_ ?_ fun _ u computed i other => ?_⟩
    · rcases src with rfl | rfl <;> decide
    · rcases src with rfl | rfl <;> decide
    · obtain ⟨sizes, down, -⟩ := props _ _ computed seen
      exact actualBalanceAt_le_of_down sizes (down i other)
  have away : block.proposerIndex.toNat ≠ block.proposerIndex.toNat + 1 := by omega
  have proposedR := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      getBeaconProposerIndex p.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat p.2)
    (fun pre _ post held ok => step pre post (Or.inr rfl) held ok fun s u c r =>
      ⟨sameSizes_processProposerSlashing c,
        fun i other => (processProposerSlashing_balanceDown apart c r other).1,
        ((processProposerSlashing_balanceDown apart c r away).2).trans r⟩)
    ⟨read, start⟩ proposedOk
  have slashedR := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      getBeaconProposerIndex p.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat p.2)
    (fun pre _ post held ok => step pre post (Or.inr rfl) held ok fun s u c r =>
      ⟨sameSizes_processAttesterSlashing c,
        fun i other => (processAttesterSlashing_balanceDown apart c r other).1,
        ((processAttesterSlashing_balanceDown apart c r away).2).trans r⟩)
    proposedR slashedOk
  have attestedR := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      getBeaconProposerIndex p.1 = .ok block.proposerIndex ∧
        PassCredits block.proposerIndex.toNat p.2)
    (fun pre _ post held ok => step pre post (Or.inl rfl) held ok fun s u c r =>
      ⟨sameSizes_processAttestation c,
        fun i other => (processAttestation_balanceDown apart c r other).1,
        ((processAttestation_balanceDown apart c r away).2).trans r⟩)
    slashedR attestedOk
  -- The remaining passes before the sync pass record no rewards or slashings.
  have depositedC := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      PassCredits block.proposerIndex.toNat p.2)
    (fun _ _ _ held ok => held.record ok (by decide) (by decide) fun h => absurd h (by decide))
    attestedR.2 depositedOk
  have requestedC := ((((depositedC.carry exitedOk).carry changedOk).carry requestedOk).carry
    withdrawnOk)
  have consolidatedC := foldlM_ok_invariant (fun p : BalanceReplay preset fork =>
      PassCredits block.proposerIndex.toNat p.2)
    (fun _ _ _ held ok => held.record ok (by decide) (by decide) fun h => absurd h (by decide))
    requestedC consolidatedOk
  obtain ⟨credit, debit, _, synced, events⟩ := recordBalance_single syncOk
  exact ⟨consolidated.1, consolidated.2, altair, _, credit, debit, events, link, synced,
    consolidatedC, processBlockHeader_proposer headerOk⟩

/-- A key that an event of a block step credits is its proposer, or a seat holder for a sync event.

The mixes must span more than the seed lookahead plus two epochs. -/
theorem block_gross_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam)
    {events : List (BalanceEvent preset)}
    (replayed : (Step.block engine signed due ok).balanceEvents = .ok events) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ (∀ k ∈ K, ∃ p, getBeaconProposerIndex s = .ok p ∧ p.toNat = k) ∧
      ∀ e ∈ events, ∀ i, 0 < Internal.keyCredit i e →
      i ∈ K ∨ (e.source = .sync ∧ ∃ altair : .altair ≤ f, ∃ w, t.validators.data[i]? = some w ∧
        w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList) := by
  have electra : .pectra ≤ f := Nat.le_trans (by decide) fulu
  obtain ⟨c, rest, altair, aggregate, credit, debit, split, read, synced, passes, header⟩ :=
    blockReplay_proposer_credits apart electra early (Step.balanceEvents_block early replayed)
  have bounded := step_events_bounded shared genesis (Step.block engine signed due ok) early
    replayed
  have matchedT : BalancesMatch t :=
    (frame_processBlock (applySignedBlock_ok ok).2.1).balancesMatch
      (run_justified_separated shared genesis).1.balancesMatch
  refine ⟨{signed.message.proposerIndex.toNat}, by simp,
    fun k hk => ⟨_, header, (Finset.mem_singleton.mp hk).symm⟩, fun e member i positive => ?_⟩
  have member' := member
  rw [split] at member'
  rcases List.mem_append.mp member' with inRest | inSync
  · obtain ⟨notSync, notConsolidation, only⟩ := passes e inRest
    refine .inl (Finset.mem_singleton.mpr ?_)
    by_contra other
    by_cases credited : e.source = .rewards ∨ e.source = .slashings
    · have := only credited i fun same => other same.symm
      omega
    · have each := block_event_credit shared genesis early electra i replayed bounded e member
      have noRewards : ¬ (e.source = .rewards ∨ e.source = .consolidations) := by
        rintro (h | h)
        · exact credited (.inl h)
        · exact notConsolidation h
      have noSync : Internal.syncCredit i e = 0 := by simp [Internal.syncCredit, notSync]
      have noSlash : ¬ e.source = .slashings := fun h => credited (.inr h)
      simp only [noRewards, noSlash, noSync, ↓reduceIte] at each
      omega
  · obtain rfl := List.mem_singleton.mp inSync
    simp only [Internal.keyCredit] at positive
    rcases sync_moved_seat (i := i) altair synced matchedT (by omega) with h | ⟨_, found, same, -⟩
    · exact .inr ⟨rfl, altair, h⟩
    · exact .inl (Finset.mem_singleton.mpr (by rw [read] at found; cases found; exact same.symm))

/-- A key that rewards, slashings or sync credit in a block step is a proposer or a seat holder. -/
theorem block_step_gross_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {f : Fork} {s t : BeaconState preset f} {engine : ExecutionEngine preset f}
    {signed : SignedBeaconBlock preset f} {due : upgradeDue config ⟨f, s⟩ = false}
    {ok : applySignedBlock config checks engine s signed true = .ok t}
    (shared : Run config checks g ⟨f, s⟩) (fulu : .fusaka ≤ f) (early : f < .glamsterdam) :
    ∃ K : Finset ℕ, K.card ≤ 1 ∧ (∀ k ∈ K, ∃ p, getBeaconProposerIndex s = .ok p ∧ p.toNat = k) ∧
      ∀ i, 0 < Internal.stepCredit
        (fun s => decide (s = .rewards ∨ s = .slashings ∨ s = .sync)) (fun _ => false) i
        (Step.block engine signed due ok) →
      i ∈ K ∨ ∃ altair : .altair ≤ f, ∃ w, t.validators.data[i]? = some w ∧
        w.pubkey ∈ (t.currentSyncCommittee altair).value.pubkeys.toList := by
  cases replayed : (Step.block engine signed due ok).balanceEvents with
  | error _ =>
    exact ⟨∅, by simp, by simp, fun i pos => by simp [Internal.stepCredit, replayed,
      Except.toOption] at pos⟩
  | ok events =>
    obtain ⟨K, card, proposers, keys⟩ := Internal.block_gross_keys genesis apart shared fulu early
      replayed
    refine ⟨K, card, proposers, fun i pos => ?_⟩
    simp only [Internal.stepCredit, replayed, Except.toOption, Option.getD_some] at pos
    by_contra none
    refine absurd (List.sum_eq_zero fun x member => ?_) (Nat.pos_iff_ne_zero.mp pos)
    obtain ⟨e, inFilter, rfl⟩ := List.mem_map.mp member
    obtain ⟨inEvents, source⟩ := List.mem_filter.mp inFilter
    refine Nat.eq_zero_of_not_pos fun positive => none ?_
    rcases keys e inEvents i positive with inK | ⟨-, altair, seat⟩
    · exact .inl inK
    · exact .inr ⟨altair, seat⟩

/-- A list of at most one element has equal members. -/
private theorem list_eq_of_length_le_one {α : Type} {L : List α} (short : L.length ≤ 1) {a b : α}
    (ha : a ∈ L) (hb : b ∈ L) : a = b := by
  cases L with
  | nil => simp at ha
  | cons c rest =>
    cases rest with
    | nil =>
      rw [List.mem_singleton] at ha hb
      rw [ha, hb]
    | cons d rest => exact absurd short (by simp)

/-- The scan of a run reads the credit of each step that the run contains.

The run must end within the horizon, so that every step of it is selected. -/
private theorem stepCredit_le_creditScan (blockP slotP : BalanceSource → Bool) (v high : ℕ)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    (within : (getCurrentEpoch y.state).toNat ≤ high + 1)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tail.Contains step) :
    Internal.stepCredit blockP slotP v step ≤ (Internal.creditScan blockP slotP v high tail) := by
  obtain ⟨pre, post, same⟩ := tail.contains_split step member
  subst same
  have selected : (getCurrentEpoch a.state).toNat ≤ high + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      (Relation.ReflTransGen.head step.chainStep post.chainSteps))) within
  rw [Internal.creditScan_append, Internal.creditScan_snoc]
  simp only [selected, ↓reduceIte]
  omega

/-- A key that a deposit credits on C's run has a positive deposit scan.

A deposit event of a block raises no balance, so a deposit that credits a key is an epoch's.

The scan counts the deposits of a slot step, and the run ends within the horizon. -/
theorem depPre_pos_scan (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (i : ℕ) (pos : 0 < Internal.depPre eventsC i) :
    0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC) := by
  classical
  obtain ⟨e, member, dep, credited⟩ : ∃ e ∈ eventsC, e.source = .deposits ∧ 0 < Internal.keyCredit i
    e := by
    by_contra none
    have none' : ∀ e ∈ eventsC, e.source = .deposits → Internal.keyCredit i e ≤ 0 := fun e member
      dep =>
      Nat.le_of_not_lt fun positive => none ⟨e, member, dep, positive⟩
    have zero : Internal.depPre eventsC i = 0 := by
      unfold Internal.depPre
      refine List.sum_eq_zero fun x mem => ?_
      obtain ⟨e, filtered, rfl⟩ := List.mem_map.mp mem
      obtain ⟨inEvents, selected⟩ := List.mem_filter.mp filtered
      exact Nat.le_zero.mp (none' e inEvents (of_decide_eq_true selected).1)
    omega
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  rcases (Internal.run_located tailC electra h.early highC replayedC).1 e member dep with
    unconditional | ⟨u, w, ok, es, contains, replayedEs, inEs, -⟩
  · exfalso
    have := unconditional i
    unfold Internal.keyCredit at credited
    omega
  · have step : Internal.keyCredit i e ≤ Internal.stepCredit (fun _ => false) (fun s => decide (s =
    .deposits)) i
        (Step.slot ok : Step config checks u w) := by
      simp only [Internal.stepCredit, replayedEs, Except.toOption, Option.getD_some]
      exact List.le_sum_of_mem (List.mem_map.mpr
        ⟨e, List.mem_filter.mpr ⟨inEs, by simpa using dep⟩, rfl⟩)
    have scan := stepCredit_le_creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC
      tailC endEpochC (Step.slot ok) contains
    omega

/-- The keys that one step credits by a pending-deposit pass.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits, in one slot step.

So the keys are at most that many for each epoch that the step leaves. -/
private theorem step_deposit_keys {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (step : Step config checks x y)
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∃ D : Finset ℕ, D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      ∀ i, 0 < Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i step → i ∈ D
        := by
  classical
  cases step with
  | block engine signed due ok =>
    refine ⟨∅, by simp, fun i here => ?_⟩
    exfalso
    have zero : Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
        (Step.block engine signed due ok : Step config checks _ _) = 0 := by
      show ((((Step.block (config := config) (checks := checks) engine signed due
        ok).balanceEvents.toOption.getD []).filter ((fun _ => false) ·.source)).map
          (Internal.keyCredit i)).sum = 0
      rw [List.filter_eq_nil_iff.mpr (fun a _ => by simp)]
      rfl
    omega
  | slot across =>
    obtain ⟨events, eventsOk⟩ :=
      (Step.slot across : Step config checks x y).balanceEvents_ok early
    -- A slot step credits a key by deposits only if one of its deposit events does.
    have quiet : ∀ i, (∀ e ∈ events, e.source = .deposits → Internal.keyCredit i e = 0) →
        Internal.stepCredit (fun _ => false) (fun s => decide (s = .deposits)) i
          (Step.slot across : Step config checks x y) = 0 := fun i none' => by
      show (((((Step.slot (config := config) (checks := checks)
        across).balanceEvents.toOption.getD []).filter
          ((fun s => decide (s = .deposits)) ·.source))).map (Internal.keyCredit i)).sum = 0
      simp only [eventsOk, Except.toOption, Option.getD_some]
      exact List.sum_eq_zero fun _ member => by
        obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
        obtain ⟨mem, test⟩ := List.mem_filter.mp inside
        exact none' e mem (by simpa using test)
    by_cases any : ∃ e ∈ events, e.source = .deposits
    · obtain ⟨sites, ends, single⟩ :=
        DirectSafety.Apriori.Internal.Step.slot_deposit_site shared genesis across early delay
          eventsOk
      have epochNext := ends any
      obtain ⟨e0, mem0, dep0⟩ := any
      obtain ⟨electra, a, b, matched, -, -, deposited, before0, after0⟩ := sites e0 mem0 dep0
      obtain ⟨-, -, rises⟩ := pending_deposit_rises a b matched electra deposited
      have oneEpoch : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat = 1 := by
        omega
      refine ⟨(Finset.range b.balances.data.size).filter fun i =>
          actualBalanceAt (⟨x.fork, a⟩ : ForkedBeaconState preset) i <
            actualBalanceAt (⟨x.fork, b⟩ : ForkedBeaconState preset) i, ?_, fun i here => ?_⟩
      · rw [oneEpoch, Nat.mul_one]
        exact rises
      · refine Finset.mem_filter.mpr ?_
        have mono : ∃ e ∈ events, e.source = .deposits ∧ 0 < Internal.keyCredit i e := by
          by_contra none
          have none' : ∀ e ∈ events, e.source = .deposits → Internal.keyCredit i e = 0 :=
            fun e mem dep => by
              by_contra ne
              exact none ⟨e, mem, dep, Nat.pos_of_ne_zero ne⟩
          have := quiet i none'
          omega
        obtain ⟨e, mem, dep, positive⟩ := mono
        -- A slot step records one deposit event, so it is the one that the site names.
        have same : e = e0 := list_eq_of_length_le_one single
          (List.mem_filter.mpr ⟨mem, by simpa using dep⟩)
          (List.mem_filter.mpr ⟨mem0, by simpa using dep0⟩)
        subst same
        unfold Internal.keyCredit at positive
        rw [before0, after0] at positive
        refine ⟨?_, ?_⟩
        · by_contra outside
          have outside' : ¬ i < b.balances.data.size := fun h =>
            outside (Finset.mem_range.mpr h)
          have missing : actualBalanceAt (⟨x.fork, b⟩ : ForkedBeaconState preset) i = 0 := by
            simp [actualBalanceAt, Array.getElem?_eq_none (Nat.le_of_not_lt outside')]
          omega
        · omega
    · refine ⟨∅, by simp, fun i here => ?_⟩
      exfalso
      have := quiet i fun e mem dep => absurd ⟨e, mem, dep⟩ any
      omega

/-- The keys credited in the block steps of a run inside one period of sync committees.

A key credited by a block is a proposer, at most one for each block.

Otherwise it holds a seat of the committee that the run starts with. -/
theorem credited_piece {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y)
    (fulu : .fusaka ≤ x.fork) (altair : .altair ≤ x.fork) (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ)
    (same : (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) :
    ∃ B D : Finset ℕ, B.card ≤ r.blockCount ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < Internal.grossScan i high r →
      i ∈ B ∨ ∃ w, y.state.validators.data[i]? = some w ∧
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList) ∧
      (∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r) →
        i ∈ D) ∧
      (∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (Internal.syncDebit
        i)).sum →
        ∃ w, y.state.validators.data[i]? = some w ∧
          w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList) ∧
      ∀ i ∈ B, ∃ (u : ForkedBeaconState preset) (_ : Run config checks x u) (p : ValidatorIndex),
        u.fork < .glamsterdam ∧ getBeaconProposerIndex u.state = .ok p ∧ p.toNat = i := by
  classical
  induction r with
  | nil =>
    refine ⟨∅, ∅, by simp, by simp, fun i pos => (Nat.lt_irrefl 0 pos).elim,
      fun i pos => (Nat.lt_irrefl 0 pos).elim, ?_, by simp⟩
    intro events replayed i pos
    simp only [Run.balanceEvents, pure, Except.pure, Except.ok.injEq] at replayed
    subst replayed
    simp at pos
  | @snoc u l pre step ih =>
    have uEarly : u.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
    have uSame : (getCurrentEpoch u.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
      have above := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) up
      have under := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
      omega
    obtain ⟨B, D, cardB, cardD, hB, hDep, hS, hP⟩ := ih uEarly uSame
    obtain ⟨Ds, cardDs, hDs⟩ := step_deposit_keys genesis (shared.append pre) step early delay
    have cardUnion : (D ∪ Ds).card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat) := by
      have joined := Nat.mul_le_mul_left preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
        (show (getCurrentEpoch u.state).toNat - (getCurrentEpoch x.state).toNat +
          ((getCurrentEpoch l.state).toNat - (getCurrentEpoch u.state).toNat) ≤
            (getCurrentEpoch l.state).toNat - (getCurrentEpoch x.state).toNat by omega)
      rw [Nat.mul_add] at joined
      exact (Finset.card_union_le _ _).trans (Nat.le_trans (Nat.add_le_add cardD cardDs) joined)
    have depMem : ∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
      high
        (pre.snoc step)) → i ∈ D ∪ Ds := by
      intro i pos
      rw [Internal.creditScan_snoc] at pos
      split at pos
      · by_cases prior : 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits))
        i
            high pre)
        · exact Finset.mem_union_left _ (hDep i prior)
        · exact Finset.mem_union_right _ (hDs i (by omega))
      · exact Finset.mem_union_left _ (hDep i pos)
    have carry : ∀ (i : ℕ) (w : Validator), u.state.validators.data[i]? = some w →
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList →
          ∃ w', l.state.validators.data[i]? = some w' ∧
            w'.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
      intro i w found mem
      obtain ⟨w', found', same'⟩ := key_persists (Run.nil.snoc step) found
      exact ⟨w', found', same' ▸ mem⟩
    cases step with
    | slot ok =>
      have fulu' : .fusaka ≤ u.fork := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      refine ⟨B, D ∪ Ds, cardB, cardUnion, fun i pos => ?_, depMem, ?_, hP⟩
      have prior := grossScan_slot_pos i high pre ok pos
      rcases hB i prior with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (carry i w found mem)
      intro events replayed i pos
      simp only [Run.balanceEvents, bind_ok_iff] at replayed
      obtain ⟨prior, priorOk, rest⟩ := replayed
      split at rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨added, addedOk, rfl⟩ := rest
        have zero := (Internal.slot_syncDebit_zero
          (Nat.le_trans (show Fork.pectra ≤ Fork.fusaka by decide) fulu') ok early addedOk i).1
        simp only [List.map_append, List.sum_append, zero, Nat.add_zero] at pos
        obtain ⟨w, found, mem⟩ := hS prior priorOk i pos
        exact carry i w found mem
      · simp only [pure, Except.pure, Except.ok.injEq] at rest
        subst rest
        obtain ⟨w, found, mem⟩ := hS _ priorOk i pos
        exact carry i w found mem
    | @block f s t engine signed due ok =>
      have fulu' : .fusaka ≤ f := Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps)
      obtain ⟨K, cardK, hKp, hK⟩ := Internal.block_step_gross_keys (engine := engine) (signed :=
        signed)
        (due := due) (ok := ok) genesis apart (shared.append pre) fulu' uEarly
      refine ⟨B ∪ K, D ∪ Ds, ?_, cardUnion, fun i pos => ?_, depMem, ?_, fun i hi => ?_⟩
      · exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB cardK)
      · rw [Internal.grossScan_snoc] at pos
        rcases Nat.eq_zero_or_pos (Internal.grossScan i high pre) with zero | prior
        · rcases hK i (by split at pos <;> omega) with member | ⟨altair', w, hv, mem⟩
          · exact .inl (Finset.mem_union_right _ member)
          · have committee := (Run.snoc pre (Step.block engine signed due ok)
                ).currentSyncCommittee_eq_of_same_period early same altair' altair
            exact .inr ⟨w, hv, by rw [← committee]; exact mem⟩
        · rcases hB i prior with member | ⟨w, found, mem⟩
          · exact .inl (Finset.mem_union_left _ member)
          · exact .inr (carry i w found mem)
      · intro events replayed i pos
        simp only [Run.balanceEvents, bind_ok_iff] at replayed
        obtain ⟨prior, priorOk, rest⟩ := replayed
        split at rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
          obtain ⟨added, addedOk, rfl⟩ := rest
          simp only [List.map_append, List.sum_append] at pos
          by_cases first : 0 < (prior.map (Internal.syncDebit i)).sum
          · obtain ⟨w, found, mem⟩ := hS prior priorOk i first
            exact carry i w found mem
          · have here : 0 < (added.map (Internal.syncDebit i)).sum := by omega
            have altair' : .altair ≤ f := Nat.le_trans (by decide) fulu'
            obtain ⟨c, rest', aggregate, credit, debit, rfl, silent, -, synced⟩ :=
              Internal.blockReplay_sync_split (show f < .glamsterdam from uEarly) altair'
                (Step.balanceEvents_block uEarly addedOk)
            simp only [List.map_append, List.sum_append, silent, Internal.syncDebit, ↓reduceIte,
              List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.zero_add,
              Nat.add_zero] at here
            have matchedT : BalancesMatch t :=
              (frame_processBlock (applySignedBlock_ok ok).2.1).balancesMatch
                (run_justified_separated (shared.append pre) genesis).1.balancesMatch
            obtain ⟨w, hv, mem⟩ := sync_debit_seat (i := i) altair' synced matchedT (by omega)
            have committee := (Run.snoc pre (Step.block engine signed due ok)
                ).currentSyncCommittee_eq_of_same_period early same altair' altair
            refine ⟨w, hv, ?_⟩
            rw [← committee]
            exact mem
        · simp only [pure, Except.pure, Except.ok.injEq] at rest
          subst rest
          obtain ⟨w, found, mem⟩ := hS _ priorOk i pos
          exact carry i w found mem
      · -- a proposer of an earlier block, or the proposer of this one
        rcases Finset.mem_union.mp hi with earlier | here
        · exact hP i earlier
        · obtain ⟨p, found, same⟩ := hKp i here
          exact ⟨⟨f, s⟩, pre, p, uEarly, found, same⟩

/-- The positions that hold a key of a committee of a list are at most the keys of the list.

The registry has distinct keys, and each committee has at most `SYNC_COMMITTEE_SIZE` keys. -/
private theorem listed_positions_card (state : BeaconState preset fork)
    (distinct : PubkeysDistinct state) (Ls : List (List Cryptography.Bls.BLSPubkey))
    (each : ∀ L ∈ Ls, L.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat) :
    ((Finset.range state.validators.data.size).filter fun i =>
        ∃ w, state.validators.data[i]? = some w ∧ ∃ L ∈ Ls, w.pubkey ∈ L).card ≤
      preset.SYNC_COMMITTEE_SIZE.toNat * Ls.length := by
  classical
  have mapped : ((Finset.range state.validators.data.size).filter fun i =>
      ∃ w, state.validators.data[i]? = some w ∧ ∃ L ∈ Ls, w.pubkey ∈ L).card ≤
        Ls.flatten.toFinset.card := by
    refine Finset.card_le_card_of_injOn (keyAt state) (fun i member => ?_)
      (fun i mi j mj eq => ?_)
    · obtain ⟨w, found, L, hL, mem⟩ := (Finset.mem_filter.mp member).2
      simp only [keyAt, found, Option.map_some, Option.getD_some]
      exact List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨L, hL, mem⟩)
    · obtain ⟨w, found, -⟩ := (Finset.mem_filter.mp mi).2
      obtain ⟨w', found', -⟩ := (Finset.mem_filter.mp mj).2
      simp only [keyAt, found, found', Option.map_some, Option.getD_some] at eq
      exact distinct.index_eq found found' eq
  have total : Ls.flatten.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat * Ls.length := by
    rw [List.length_flatten]
    have := List.sum_le_length_nsmul (Ls.map List.length) preset.SYNC_COMMITTEE_SIZE.toNat
      (fun a ha => by
        obtain ⟨L, hL, rfl⟩ := List.mem_map.mp ha
        exact each L hL)
    simpa [List.length_map, smul_eq_mul, Nat.mul_comm] using this
  exact mapped.trans ((List.toFinset_card_le _).trans total)

/-- The positions that hold a key of a committee are at most the size of the committee. -/
private theorem seat_positions {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g) {x y : ForkedBeaconState preset}
    (shared : Run config checks g x) (r : Run config checks x y) (altair : .altair ≤ x.fork) :
    ∃ S : Finset ℕ, S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat ∧ ∀ (i : ℕ) (w : Validator),
      y.state.validators.data[i]? = some w →
        w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList → i ∈ S := by
  classical
  have distinct := (shared.append r).pubkeysDistinct genesis
  let L := (x.state.currentSyncCommittee altair).value.pubkeys.toList
  refine ⟨(Finset.range y.state.validators.data.size).filter fun i =>
      ∃ w, y.state.validators.data[i]? = some w ∧ w.pubkey ∈ L, ?_, ?_⟩
  · have listed := listed_positions_card y.state distinct [L] (by simp [L])
    rw [List.length_singleton, Nat.mul_one] at listed
    refine le_trans (Finset.card_le_card ?_) listed
    intro i member
    obtain ⟨inside, w, found, mem⟩ := Finset.mem_filter.mp member
    exact Finset.mem_filter.mpr ⟨inside, w, found, L, List.mem_singleton_self L, mem⟩
  · intro i w found mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
      w, found, mem⟩

/-- The keys credited in the block steps of a run, counted by the periods that it touches.

The keys that a sync aggregate debits hold a seat of one committee for each period of the run.

Each committee is the current one at a state of the run, in the period of its index. -/
theorem credited_pieces_seated {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {y : ForkedBeaconState preset}
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ) :
    ∀ (n : ℕ) {x : ForkedBeaconState preset}, Run config checks g x →
      ∀ (r : Run config checks x y), .fusaka ≤ x.fork →
    (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + n →
    ∃ (Ls : ℕ → List Cryptography.Bls.BLSPubkey) (B S D : Finset ℕ), B.card ≤ r.blockCount ∧
      S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < Internal.grossScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r) →
        i ∈ D) ∧
      (∀ i, 0 < Internal.grossScan i high r → i ∈ B ∨
        ∃ w j, y.state.validators.data[i]? = some w ∧ j ≤ n ∧ w.pubkey ∈ Ls j) ∧
      (∀ i ∈ B, ∃ (u : ForkedBeaconState preset) (_ : Run config checks x u) (p : ValidatorIndex),
        u.fork < .glamsterdam ∧ getBeaconProposerIndex u.state = .ok p ∧ p.toNat = i) ∧
      (∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (Internal.syncDebit
        i)).sum →
        i ∈ S ∧ ∃ w j, y.state.validators.data[i]? = some w ∧ j ≤ n ∧ w.pubkey ∈ Ls j) ∧
      ∀ j ≤ n, ∃ (z : ForkedBeaconState preset) (r1 : Run config checks x z)
        (r2 : Run config checks z y) (alt : .altair ≤ z.fork), r1.append r2 = r ∧
        (getCurrentEpoch z.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + j ∧
        Ls j = (z.state.currentSyncCommittee alt).value.pubkeys.toList := by
  classical
  intro n
  induction n with
  | zero =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨B, D, cardB, cardD, hB, hDep, hD, hP⟩ := Internal.credited_piece genesis apart shared r
      fulu
      altair early delay high (by simpa using count)
    obtain ⟨S, cardS, hS⟩ := seat_positions genesis shared r altair
    refine ⟨fun _ => (x.state.currentSyncCommittee altair).value.pubkeys.toList, B, S, D, cardB,
      by simpa using cardS, cardD, fun i pos => ?_, hDep,
      fun i pos => (hB i pos).imp id fun ⟨w, found, mem⟩ => ⟨w, 0, found, Nat.le_refl _, mem⟩, hP,
      ?_, ?_⟩
    · rcases hB i pos with member | ⟨w, found, mem⟩
      · exact .inl member
      · exact .inr (hS i w found mem)
    · intro events replayed i pos
      obtain ⟨w, found, mem⟩ := hD events replayed i pos
      exact ⟨hS i w found mem, w, 0, found, Nat.le_refl _, mem⟩
    · intro j hj
      obtain rfl : j = 0 := by omega
      exact ⟨x, Run.nil, r, altair, Run.nil_append r, (Nat.add_zero _).symm, rfl⟩
  | succ n ih =>
    intro x shared r fulu count
    have electra : .pectra ≤ x.fork := Nat.le_trans (by decide) fulu
    have altair : .altair ≤ x.fork := Nat.le_trans (by decide) electra
    obtain ⟨m, v, pre, step, post, split, hm, hv⟩ := Run.split_at_flip r
      (fun z => (getCurrentEpoch x.state).toNat /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
        (getCurrentEpoch z.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      (Nat.lt_irrefl _) (by omega)
    have low := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have up := step.chainStep.epoch_le_succ
    have mSame : (getCurrentEpoch m.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
      have under := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
      omega
    have vNext : (getCurrentEpoch v.state).toNat /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
          (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 := by
      have above := Nat.div_le_div_right
        (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) up
      rw [Nat.succ_div] at above
      split at above <;> omega
    have mEarly : m.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (Nat.le_trans step.chainStep.fork_le
        (fork_le_of_chainSteps post.chainSteps)) early
    have vFulu : .fusaka ≤ v.fork :=
      Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
    obtain ⟨B₁, D₁, cardB₁, cardD₁, hB₁, hDep₁, hD₁, hP₁⟩ := Internal.credited_piece genesis apart
      shared pre
      fulu
      altair mEarly delay high (by simpa using mSame)
    obtain ⟨S₁, cardS₁, hS₁⟩ := seat_positions genesis shared pre altair
    obtain ⟨Ls₂, B₂, S₂, D₂, cardB₂, cardS₂, cardD₂, hB₂, hDep₂, hG₂, hP₂, hD₂, hz₂⟩ := ih (x := v)
      (shared.append (pre.snoc step)) post vFulu
      (by omega)
    -- The step leaves an epoch, so it is a slot step: a block step keeps its epoch.
    have slotStep : ∃ ok, step = Step.slot ok := by
      cases step with
      | slot ok => exact ⟨ok, rfl⟩
      | @block f before after engine signed due ok =>
        exfalso
        have same := processBlock_slot (applySignedBlock_ok ok).2.1
        have e : (getCurrentEpoch after).toNat = (getCurrentEpoch before).toNat := by
          simp only [getCurrentEpoch, same]
        have hm' : ¬ (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
              (getCurrentEpoch before).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := hm
        have hv' : (getCurrentEpoch x.state).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat <
              (getCurrentEpoch after).toNat /
                max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := hv
        rw [e] at hv'
        exact hm' hv'
    obtain ⟨ok, rfl⟩ := slotStep
    subst split
    have vEarly : v.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) early
    obtain ⟨Ds, cardDs, hDs⟩ := step_deposit_keys genesis (shared.append pre) (Step.slot ok)
      vEarly delay
    have stepUp := UInt64.le_iff_toNat_le.mp
      (Step.slot ok : Step config checks m v).chainStep.currentEpoch_le
    have postUp := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    refine ⟨fun j => if j = 0 then (x.state.currentSyncCommittee altair).value.pubkeys.toList
        else Ls₂ (j - 1), B₁ ∪ B₂, S₁ ∪ S₂, D₁ ∪ Ds ∪ D₂, ?_, ?_, ?_, fun i pos => ?_,
      fun i pos => ?_, fun i pos => ?_, fun i hi => ?_, ?_, ?_⟩
    · rw [Run.blockCount_append]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add cardB₁ cardB₂)
    · refine (Finset.card_union_le _ _).trans ?_
      calc _ ≤ preset.SYNC_COMMITTEE_SIZE.toNat +
            preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) := Nat.add_le_add cardS₁ cardS₂
        _ = _ := by ring
    · have joined := Nat.mul_le_mul_left preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat
        (show ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
          ((getCurrentEpoch v.state).toNat - (getCurrentEpoch m.state).toNat) +
            ((getCurrentEpoch y.state).toNat - (getCurrentEpoch v.state).toNat) ≤
              (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat by omega)
      rw [Nat.mul_add, Nat.mul_add] at joined
      exact (Finset.card_union_le _ _).trans (Nat.le_trans (Nat.add_le_add
        ((Finset.card_union_le _ _).trans (Nat.add_le_add cardD₁ cardDs)) cardD₂) joined)
    · rw [Internal.grossScan_append] at pos
      by_cases first : 0 < Internal.grossScan i high (pre.snoc (Step.slot ok))
      · have prior := grossScan_slot_pos i high pre ok first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · exact .inr (Finset.mem_union_left _ (hS₁ i w found mem))
      · have later : 0 < Internal.grossScan i high post := by omega
        rcases hB₂ i later with member | member
        · exact .inl (Finset.mem_union_right _ member)
        · exact .inr (Finset.mem_union_right _ member)
    · rw [Internal.creditScan_append] at pos
      by_cases first : 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
        high
          (pre.snoc (Step.slot ok)))
      · rw [Internal.creditScan_snoc] at first
        split at first
        · by_cases prior : 0 < (Internal.creditScan (fun _ => false)
              (fun s => decide (s = .deposits)) i high pre)
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hDep₁ i prior))
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hDs i (by omega)))
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hDep₁ i first))
      · exact Finset.mem_union_right _ (hDep₂ i (by omega))
    · -- a credit in the first part is a proposer or a seat holder, and a seat persists
      rw [Internal.grossScan_append] at pos
      by_cases first : 0 < Internal.grossScan i high (pre.snoc (Step.slot ok))
      · have prior := grossScan_slot_pos i high pre ok first
        rcases hB₁ i prior with member | ⟨w, found, mem⟩
        · exact .inl (Finset.mem_union_left _ member)
        · have kept := (validatorKeys_prefix_and_distinct_of_chainSteps
            (Relation.ReflTransGen.head (Step.slot ok : Step config checks m v).chainStep
              post.chainSteps)).1
          obtain ⟨w', found', same⟩ := validators_getElem?_of_validatorKeys_prefix kept found
          exact .inr ⟨w', 0, found', Nat.zero_le _, by simpa [same] using mem⟩
      · rcases hG₂ i (by omega) with member | ⟨w, j, found, hj, mem⟩
        · exact .inl (Finset.mem_union_right _ member)
        · exact .inr ⟨w, j + 1, found, by omega, by simpa using mem⟩
    · rcases Finset.mem_union.mp hi with first | later
      · exact hP₁ i first
      · obtain ⟨u, q, p, early', found, same⟩ := hP₂ i later
        exact ⟨u, (pre.snoc (Step.slot ok)).append q, p, early', found, same⟩
    · intro events replayed i pos
      obtain ⟨e1, ok1⟩ := (pre.snoc (Step.slot ok)).balanceEvents_ok vEarly high
      obtain ⟨e2, ok2⟩ := post.balanceEvents_ok early high
      rw [DirectSafety.Apriori.Internal.balanceEvents_append _ _ high ok1 ok2] at replayed
      have joined := Except.ok.inj replayed
      subst joined
      simp only [List.map_append, List.sum_append] at pos
      by_cases first : 0 < ((e1.map (Internal.syncDebit i))).sum
      · have seated : ∃ w, m.state.validators.data[i]? = some w ∧
            w.pubkey ∈ (x.state.currentSyncCommittee altair).value.pubkeys.toList := by
          simp only [Run.balanceEvents, bind_ok_iff] at ok1
          obtain ⟨prior, priorOk, rest⟩ := ok1
          split at rest
          · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
            obtain ⟨added, addedOk, rfl⟩ := rest
            have zero := (Internal.slot_syncDebit_zero
              (Nat.le_trans (show Fork.pectra ≤ Fork.fusaka by decide)
                (Nat.le_trans fulu (fork_le_of_chainSteps pre.chainSteps))) ok vEarly addedOk i).1
            simp only [List.map_append, List.sum_append, zero, Nat.add_zero] at first
            exact hD₁ prior priorOk i first
          · simp only [pure, Except.pure, Except.ok.injEq] at rest
            subst rest
            exact hD₁ _ priorOk i first
        obtain ⟨w, found, mem⟩ := seated
        refine ⟨Finset.mem_union_left _ (hS₁ i w found mem), ?_⟩
        have kept := (validatorKeys_prefix_and_distinct_of_chainSteps
          (Relation.ReflTransGen.head (Step.slot ok : Step config checks m v).chainStep
            post.chainSteps)).1
        obtain ⟨w', found', same⟩ := validators_getElem?_of_validatorKeys_prefix kept found
        exact ⟨w', 0, found', Nat.zero_le _, by simpa [same] using mem⟩
      · obtain ⟨inS, w, j, found, hj, mem⟩ := hD₂ e2 ok2 i (by omega)
        exact ⟨Finset.mem_union_right _ inS, w, j + 1, found, by omega, by simpa using mem⟩
    · intro j hj
      by_cases j0 : j = 0
      · subst j0
        exact ⟨x, Run.nil, (pre.snoc (Step.slot ok)).append post, altair, Run.nil_append _,
          (Nat.add_zero _).symm, by simp⟩
      · obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := hz₂ (j - 1) (by omega)
        refine ⟨z, (pre.snoc (Step.slot ok)).append r1, r2, alt, ?_, ?_, ?_⟩
        · rw [← Run.append_assoc, cut]
        · omega
        · simpa [j0] using hL

/-- The keys credited in the block steps of a run, counted by the periods that it touches. -/
theorem credited_pieces {g : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {y : ForkedBeaconState preset}
    (early : y.fork < .glamsterdam)
    (delay : 0 < config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) (high : ℕ) :
    ∀ (n : ℕ) {x : ForkedBeaconState preset}, Run config checks g x →
      ∀ (r : Run config checks x y), .fusaka ≤ x.fork →
    (getCurrentEpoch y.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch x.state).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + n →
    ∃ B S D : Finset ℕ, B.card ≤ r.blockCount ∧
      S.card ≤ preset.SYNC_COMMITTEE_SIZE.toNat * (n + 1) ∧
      D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
        ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) ∧
      (∀ i, 0 < Internal.grossScan i high r → i ∈ B ∨ i ∈ S) ∧
      (∀ i, 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high r) →
        i ∈ D) ∧
      ∀ events, r.balanceEvents high = .ok events → ∀ i, 0 < (events.map (Internal.syncDebit i)).sum
        →
        i ∈ S := by
  intro n x shared r fulu count
  obtain ⟨_, B, S, D, cardB, cardS, cardD, hBS, hDep, -, -, hSD, _⟩ :=
    Internal.credited_pieces_seated genesis apart early delay high n shared r fulu count
  exact ⟨B, S, D, cardB, cardS, cardD, hBS, hDep,
    fun events replayed i pos => (hSD events replayed i pos).1⟩

/-- A key of an earlier registry has the same position in a later registry.

The later registry has distinct keys, and the earlier keys are a prefix of the later ones. -/
private theorem position_in_prefix {f f' : Fork} {x : BeaconState preset f}
    {t : BeaconState preset f'} (kept : validatorKeys x <+: validatorKeys t)
    (distinct : PubkeysDistinct t) {pk : Cryptography.Bls.BLSPubkey}
    (mem : pk ∈ validatorKeys x) {i : ℕ} {w : Validator}
    (found : t.validators.data[i]? = some w) (same : w.pubkey = pk) :
    ∃ v, x.validators.data[i]? = some v ∧ v.pubkey = pk := by
  simp only [validatorKeys] at mem
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp mem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hv
  have foundX : x.validators.data[j]? = some v := by simpa using hj
  obtain ⟨cur, foundT, same'⟩ := validators_getElem?_of_validatorKeys_prefix kept foundX
  have index := distinct.index_eq found foundT (same.trans same'.symm)
  subst index
  exact ⟨v, foundX, rfl⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The keys that a sync aggregate debits on the two branches fit the committees of their periods.

The keys of C's run from the finalized block are counted in its committees.

The keys of R's run from the split hold a seat of its committees.

Its first two committees are the current and next ones at the split, which C's run holds too.

So each key counts once, and the later committees of R's run count after C's.

The next committee at the start of a run is the current one at its end, if it crosses a period. -/
theorem seat_union_card (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (high highC : ℕ)
    {events eventsF eventsC : List (BalanceEvent preset)}
    (replayed : tail.balanceEvents high = .ok events)
    (replayedF : fromFin.balanceEvents highC = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (altairF : .altair ≤ fork) (AV AK : Finset ℕ)
    (debitsC : ∀ i ∈ AV, 0 < ((eventsF ++ eventsC).map (Internal.syncDebit i)).sum ∨
      (0 < Internal.grossScan i highC (fromFin.append tailC) ∧
        ∀ (u : ForkedBeaconState preset) (_ : Run config checks ⟨fork, fin⟩ u) (p : ValidatorIndex),
          u.fork < .glamsterdam → getBeaconProposerIndex u.state = .ok p → p.toNat ≠ i) ∨
      ∃ w, split.validators.data[i]? = some w ∧
        w.pubkey ∈ (split.currentSyncCommittee altairF).value.pubkeys.toList)
    (debitsR : ∀ i ∈ AK, 0 < (events.map (Internal.syncDebit i)).sum) :
    (AV ∪ AK).card ≤ preset.SYNC_COMMITTEE_SIZE.toNat *
      (((getCurrentEpoch pulled).toNat + 1) /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 1 +
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) /
        max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  have apart := h.parameters.lookahead
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have pulledCounted := UInt64.le_iff_toNat_le.mp h.later
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  simp only at finSplit
  generalize hP : max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat = P at *
  -- the periods of the two runs
  have divFS := Nat.div_le_div_right (c := P) finSplit
  have divSP := Nat.div_le_div_right (c := P) splitPulled
  have divPC := Nat.div_le_div_right (c := P) pulledCounted
  have divCN := Nat.div_le_div_right (c := P) near
  have divSC : (getCurrentEpoch split).toNat / P ≤ (getCurrentEpoch counted).toNat / P :=
    Nat.div_le_div_right (Nat.le_trans splitPulled pulledCounted)
  have divRS : (getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P ≤
      ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P + 1 := by
    rcases Nat.le_total (getCurrentEpoch pulled).toNat (getCurrentEpoch split).toNat with
      order | order
    · have := Nat.div_le_div_right (c := P) order
      have nonneg :=
        Nat.zero_le (((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P)
      omega
    · obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le order
      rw [hd, Nat.add_sub_cancel_left]
      have := Nat.add_div_le_div_add_div_add_one (getCurrentEpoch split).toNat d P
      have nonneg := Nat.zero_le (d / P)
      omega
  have divDepth : ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P ≤
      ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) / P :=
    Nat.div_le_div_right (by omega)
  have periodsR : (getCurrentEpoch pulled).toNat / P =
      (getCurrentEpoch split).toNat / P +
        ((getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P) := by omega
  have periodsC : (getCurrentEpoch counted).toNat / P =
      (getCurrentEpoch fin).toNat / P +
        ((getCurrentEpoch counted).toNat / P - (getCurrentEpoch fin).toNat / P) := by omega
  obtain ⟨LsR, BR, SR, DR, -, -, -, -, -, -, -, debitR, familyR⟩ :=
    Internal.credited_pieces_seated h.genesis apart (y := ⟨fork, pulled⟩) h.early
      (Internal.Setting.delay h) high
      ((getCurrentEpoch pulled).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      (toFin.append fromFin) tail h.fulu (by rw [hP]; exact periodsR)
  obtain ⟨LsC, BC, SC, DC, -, -, -, -, -, grossC, propC, debitC, familyC⟩ :=
    Internal.credited_pieces_seated h.genesis apart (y := ⟨fork, counted⟩) h.early
      (Internal.Setting.delay h) highC
      ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
        (getCurrentEpoch fin).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
      toFin (fromFin.append tailC) h.fulu (by rw [hP]; exact periodsC)
  simp only [hP] at familyR familyC debitR debitC grossC
  have replayedRC : (fromFin.append tailC).balanceEvents highC = .ok (eventsF ++ eventsC) :=
    DirectSafety.Apriori.Internal.balanceEvents_append fromFin tailC highC replayedF replayedC
  have arith : ((getCurrentEpoch counted).toNat / P - (getCurrentEpoch fin).toNat / P + 1) +
      ((getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P - 1) ≤
      ((getCurrentEpoch pulled).toNat + 1) / P - (getCurrentEpoch fin).toNat / P + 1 +
        ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) / P := by
    generalize (getCurrentEpoch counted).toNat / P = A at divCN ⊢
    generalize ((getCurrentEpoch pulled).toNat + 1) / P = B at divCN ⊢
    generalize (getCurrentEpoch fin).toNat / P = F
    generalize (getCurrentEpoch pulled).toNat / P = E at divRS ⊢
    generalize (getCurrentEpoch split).toNat / P = T at divRS ⊢
    generalize ((getCurrentEpoch pulled).toNat - (getCurrentEpoch split).toNat) / P = D1
      at divRS divDepth
    generalize ((getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat) / P = D2
      at divDepth ⊢
    omega
  generalize hnR : (getCurrentEpoch pulled).toNat / P - (getCurrentEpoch split).toNat / P = nR
    at *
  generalize hnC : (getCurrentEpoch counted).toNat / P - (getCurrentEpoch fin).toNat / P = nC
    at *
  -- the current and next committees at the split
  have keysSplit := (toFin.append fromFin).syncCommittee_keys h.genesis altairF
  generalize hLcur : (split.currentSyncCommittee altairF).value.pubkeys.toList = Lcur at *
  generalize hLnext : (split.nextSyncCommittee altairF).value.pubkeys.toList = Lnext at *
  have sizeOf : ∀ {f : Fork} (alt : .altair ≤ f) (b : BeaconState preset f),
      (b.currentSyncCommittee alt).value.pubkeys.toList.length =
        preset.SYNC_COMMITTEE_SIZE.toNat := fun _ _ => Vector.length_toList
  -- R's first two committees are the current and next ones at the split
  have firstR : LsR 0 = Lcur := by
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyR 0 (Nat.zero_le _)
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLcur]
    exact r1.currentSyncCommittee_eq_of_same_period earlyZ (by rw [hP]; simpa using per) alt
      altairF
  have secondR : 1 ≤ nR → LsR 1 = Lnext := fun one => by
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyR 1 one
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLnext]
    exact r1.currentSyncCommittee_eq_nextSyncCommittee_of_next_period earlyZ
      h.facts.syncPeriod (by rw [hP]; simpa using per) alt altairF
  -- C's committees hold them too
  have firstC : ∃ j ≤ nC, LsC j = Lcur := by
    refine ⟨(getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P, by omega, ?_⟩
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyC
      ((getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P) (by omega)
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLcur]
    rcases Run.prefix_total r1 r2 fromFin tailC cut rfl with ⟨r, -⟩ | ⟨r, -⟩
    · exact (r.currentSyncCommittee_eq_of_same_period h.early
        (by rw [hP]; simp only; omega) altairF alt).symm
    · exact r.currentSyncCommittee_eq_of_same_period earlyZ
        (by rw [hP]; simp only; omega) alt altairF
  have secondC : 1 ≤ nR → ∃ j ≤ nC, LsC j = Lnext := fun one => by
    refine ⟨(getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P + 1,
      by omega, ?_⟩
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyC
      ((getCurrentEpoch split).toNat / P - (getCurrentEpoch fin).toNat / P + 1) (by omega)
    have earlyZ : z.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
    rw [hL, ← hLnext]
    rcases Run.prefix_total r1 r2 fromFin tailC cut rfl with ⟨r, -⟩ | ⟨r, -⟩
    · exfalso
      have order := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r.chainSteps)
      simp only at order
      have := Nat.div_le_div_right (c := P) order
      omega
    · exact r.currentSyncCommittee_eq_nextSyncCommittee_of_next_period earlyZ
        h.facts.syncPeriod (by rw [hP]; simp only; omega) alt altairF
  -- the positions that hold a key of the committees of each run
  have distinctR : PubkeysDistinct pulled :=
    ((toFin.append fromFin).append tail).pubkeysDistinct h.genesis
  have distinctC : PubkeysDistinct counted :=
    (toFin.append (fromFin.append tailC)).pubkeysDistinct h.genesis
  have eachC : ∀ L ∈ (List.range (nC + 1)).map LsC, L.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat :=
    fun L member => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
      obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyC j (by
        have := List.mem_range.mp hj
        omega)
      rw [hL]
      exact (sizeOf alt z.state).le
  have eachR : ∀ L ∈ (List.range' 2 (nR - 1)).map LsR,
      L.length ≤ preset.SYNC_COMMITTEE_SIZE.toNat := fun L member => by
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp member
    obtain ⟨z, r1, r2, alt, cut, per, hL⟩ := familyR j (by
      have := List.mem_range'_1.mp hj
      omega)
    rw [hL]
    exact (sizeOf alt z.state).le
  have cardC := listed_positions_card counted distinctC _ eachC
  have cardR := listed_positions_card pulled distinctR _ eachR
  rw [List.length_map, List.length_range] at cardC
  rw [List.length_map, List.length_range'] at cardR
  have keptR := (validatorKeys_prefix_and_distinct_of_chainSteps tail.chainSteps).1
  have keptC := (validatorKeys_prefix_and_distinct_of_chainSteps tailC.chainSteps).1
  have union_le := le_trans (Finset.card_union_le _ _) (Nat.add_le_add cardC cardR)
  refine le_trans (Finset.card_le_card ?_) (le_trans union_le ?_)
  · intro i member
    rcases Finset.mem_union.mp member with inV | inK
    · -- a key debited or credited on C's run holds a seat, unless it is a proposer
      obtain ⟨w, j, found, hj, mem⟩ : ∃ (w : Validator) (j : ℕ),
          counted.validators.data[i]? = some w ∧ j ≤ nC ∧ w.pubkey ∈ LsC j := by
        rcases debitsC i inV with spent | ⟨seen, notProposer⟩ | ⟨ws, foundS, memS⟩
        · obtain ⟨-, w, j, found, hj, mem⟩ := debitC (eventsF ++ eventsC) replayedRC i spent
          exact ⟨w, j, found, hj, mem⟩
        · rcases grossC i seen with proposed | ⟨w, j, found, hj, mem⟩
          · obtain ⟨u, q, p, early', found, same⟩ := propC i proposed
            exact absurd same (notProposer u q p early' found)
          · exact ⟨w, j, found, hj, mem⟩
        · -- a seat of the split's current committee, which C's committees hold
          obtain ⟨jc, hjc, e⟩ := firstC
          obtain ⟨c, foundC, sameC⟩ := validators_getElem?_of_validatorKeys_prefix keptC foundS
          exact ⟨c, jc, foundC, hjc, by rw [sameC, e]; exact memS⟩
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, w, found, LsC j,
          List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, mem⟩)
    · obtain ⟨-, w, j, found, hj, mem⟩ := debitR events replayed i (debitsR i inK)
      by_cases late : 2 ≤ j
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, w, found, LsR j,
            List.mem_map.mpr ⟨j, List.mem_range'_1.mpr (by omega), rfl⟩, mem⟩)
      · -- a seat of the first two committees: the key is at its position in the split
        have inSplit : w.pubkey ∈ validatorKeys split ∧
            ∃ L ∈ (List.range (nC + 1)).map LsC, w.pubkey ∈ L := by
          rcases Nat.lt_or_ge j 1 with zero | one
          · have j0 : j = 0 := by omega
            subst j0
            rw [firstR] at mem
            obtain ⟨L, hL, hLmem⟩ : ∃ L ∈ (List.range (nC + 1)).map LsC, L = Lcur := by
              obtain ⟨jc, hjc, e⟩ := firstC
              exact ⟨LsC jc, List.mem_map.mpr ⟨jc, List.mem_range.mpr (by omega), rfl⟩, e⟩
            exact ⟨keysSplit.1 w.pubkey mem, L, hL,
              by rw [hLmem]; exact mem⟩
          · have j1 : j = 1 := by omega
            subst j1
            have oneR : 1 ≤ nR := hj
            rw [secondR oneR] at mem
            obtain ⟨L, hL, hLmem⟩ : ∃ L ∈ (List.range (nC + 1)).map LsC, L = Lnext := by
              obtain ⟨jc, hjc, e⟩ := secondC oneR
              exact ⟨LsC jc, List.mem_map.mpr ⟨jc, List.mem_range.mpr (by omega), rfl⟩, e⟩
            exact ⟨keysSplit.2 w.pubkey mem, L, hL,
              by rw [hLmem]; exact mem⟩
        obtain ⟨inKeys, L, hL, hLmem⟩ := inSplit
        obtain ⟨v, foundS, sameS⟩ := position_in_prefix keptR distinctR inKeys found rfl
        obtain ⟨c, foundC, sameC⟩ := validators_getElem?_of_validatorKeys_prefix keptC foundS
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp foundC).1, c, foundC, L, hL,
            by rw [sameC, sameS]; exact hLmem⟩)
  · rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ arith

/-- The keys that a run from the split credits or debits through a sync seat.

They are at most its proposers, its seat holders and its deposit recipients.

A key counts if a block step of the run nets it a rise, or an epoch pass applies a deposit to it.

A block step has one proposer, and an epoch has at most one block for each slot.

The seat holders are those of one sync committee for each period that the run touches.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits.

A key that a sync aggregate debits holds a seat of the committee of its period. -/
private theorem banded_keys_le (h : Setting config checks g split fin pulled anc counted V)
    {x : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, x⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (keys : Finset ℕ) (banded : ∀ i ∈ keys, 0 < Internal.grossScan i high tail +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail) +
        (events.map (Internal.syncDebit i)).sum) :
    keys.card ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have apart := h.parameters.lookahead
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have slots := h.twoSlots
  have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by omega
  have low : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch x).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tail.chainSteps)
  have periodLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
  have periods : (getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
          (getCurrentEpoch split).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by omega
  obtain ⟨B, S, D, cardB, cardS, cardD, hBS, hD, hSD⟩ := Internal.credited_pieces h.genesis apart
    (y := ⟨fork, x⟩) h.early (Internal.Setting.delay h) high
    ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tail h.fulu periods
  have cardD' : D.card ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) := cardD
  have subset : keys ⊆ B ∪ S ∪ D := fun i member => by
    have pos := banded i member
    by_cases net : 0 < Internal.grossScan i high tail
    · rcases hBS i net with inB | inS
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ inB)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ inS)
    · by_cases dep : 0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i
      high
          tail)
      · exact Finset.mem_union_right _ (hD i dep)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hSD events replayed i (by omega)))
  -- The blocks of the run are at most one for each slot of its epochs.
  have blocks : tail.blockCount ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat := by
    have count : tail.blockCount ≤
        ((getCurrentEpoch x).toNat + 1 - (getCurrentEpoch split).toNat) *
          preset.SLOTS_PER_EPOCH.toNat := tail.blockCount_le_epochs positive
    have same : (getCurrentEpoch x).toNat + 1 - (getCurrentEpoch split).toNat =
        (getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1 := by omega
    rw [same] at count
    exact count
  have total := (Finset.card_le_card subset).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  have expand : ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
      (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) =
        ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat *
            ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat) +
              preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by ring
  omega

/-- The keys that a run from the split credits.

They are at most its proposers, its seat holders and its deposit recipients. -/
theorem credited_keys_le (h : Setting config checks g split fin pulled anc counted V)
    {x : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, x⟩) (high : ℕ) :
    ((Finset.range x.validators.data.size).filter fun i =>
        0 < Internal.grossScan i high tail +
          (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i high tail)).card
            ≤
      ((getCurrentEpoch x).toNat - (getCurrentEpoch split).toNat + 1) *
          (preset.SLOTS_PER_EPOCH.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
        preset.SYNC_COMMITTEE_SIZE.toNat *
          ((getCurrentEpoch x).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
            (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
              1) := by
  obtain ⟨events, replayed⟩ := tail.balanceEvents_ok h.early high
  exact banded_keys_le h tail high replayed _ fun i member => by
    have pos := (Finset.mem_filter.mp member).2
    omega

end Internal

/-! ## The classes of keys and their costs -/

section Costs

variable (pulled counted : BeaconState preset fork) (V : Finset ValidatorIndex)

namespace Internal

/-- The keys active at C. -/
def countedActiveVoters := activeVoters counted

/-- The keys active at R. -/
def pulledActiveVoters := activeVoters pulled

/-- The keys counted in C's quorum. -/
def countedQuorum := quorumVoters counted

/-- The keys that the costs sum over: counted at C, or active at C or R. -/
def costKeys := countedQuorum counted ∪ countedActiveVoters counted ∪ pulledActiveVoters pulled

/-- The balance of a key at C. -/
def countedBalance (v : ValidatorIndex) : ℕ :=
  balanceAt counted v.toNat

/-- The balance of a key at R. -/
def pulledBalance (v : ValidatorIndex) : ℕ :=
  balanceAt pulled v.toNat

/-- The fall from R to C of the keys of `V` active at C. -/
def voterFallCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ V ∧ v ∈ countedActiveVoters counted then
    (pulledBalance pulled v : ℤ) - countedBalance counted v
  else 0

/-- The stake at R of the keys of `V` not active at C. -/
def inactiveVoterCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ V ∧ v ∉ countedActiveVoters counted then (pulledBalance pulled v : ℤ) else 0

/-- The rise from R to C of the keys outside `V` active at C and R and counted in C's quorum. -/
def stayingRiseCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ countedActiveVoters counted ∧ v ∈ pulledActiveVoters pulled ∧
      v ∈ countedQuorum counted ∧ v ∉ V then
    (countedBalance counted v : ℤ) - pulledBalance pulled v
  else 0

/-- The stake at C of the keys outside `V` counted in C's quorum but not active at C. -/
def previousOnlyCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ countedQuorum counted ∧ v ∉ countedActiveVoters counted ∧ v ∉ V then
    (countedBalance counted v : ℤ)
  else 0

/-- The stake at C of the keys active and counted at C but not active at R. -/
def joinedCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ countedActiveVoters counted ∧ v ∈ countedQuorum counted ∧
      v ∉ pulledActiveVoters pulled then
    (countedBalance counted v : ℤ)
  else 0

/-- The keys active at C and outside its quorum (slashed at C): minus twice their stake at C.

It also subtracts their stake at R if they are active there. -/
def outsideQuorumCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ countedActiveVoters counted ∧ v ∉ countedQuorum counted then
    -(2 * (countedBalance counted v : ℤ)) -
      (if v ∈ pulledActiveVoters pulled then (pulledBalance pulled v : ℤ) else 0)
  else 0

/-- Minus the stake at R of the keys outside `V` active at R, not at C and outside C's quorum. -/
def departedCost : ℤ := ∑ v ∈ costKeys pulled counted,
  if v ∈ pulledActiveVoters pulled ∧ v ∉ countedActiveVoters counted ∧
      v ∉ countedQuorum counted ∧ v ∉ V then
    -(pulledBalance pulled v : ℤ)
  else 0

/-- The keys of `V` not active at C. -/
def countedInactiveVoters : Finset ValidatorIndex := V.filter (· ∉ countedActiveVoters counted)

/-- The keys outside `V` active at C and R and counted in C's quorum. -/
def stayingKeys : Finset ValidatorIndex :=
  (countedActiveVoters counted).filter fun v =>
    v ∈ pulledActiveVoters pulled ∧ v ∈ countedQuorum counted ∧ v ∉ V

/-- The keys outside `V` counted in C's quorum but not active at C. -/
def previousOnlyKeys : Finset ValidatorIndex :=
  (countedQuorum counted).filter fun v => v ∉ countedActiveVoters counted ∧ v ∉ V

/-- The keys active and counted at C but not active at R. -/
def joinedKeys : Finset ValidatorIndex :=
  (countedActiveVoters counted).filter fun v =>
    v ∈ countedQuorum counted ∧ v ∉ pulledActiveVoters pulled

/-- The keys of R's registry unslashed at the split and slashed at C. -/
def newlySlashed (split : BeaconState preset fork) : Finset ValidatorIndex :=
  ((Finset.range pulled.validators.data.size).image UInt64.ofNat).filter fun v =>
    slashedFlagAt counted v.toNat = some true ∧ slashedFlagAt split v.toNat = some false

/-- Keys created beyond the split's registry and slashed at C. -/
def createdSlashed (split : BeaconState preset fork) : Finset ValidatorIndex :=
  ((Finset.range counted.validators.data.size).image UInt64.ofNat).filter fun v =>
    split.validators.data.size ≤ v.toNat ∧ slashedFlagAt counted v.toNat = some true

end Internal

end Costs

namespace Internal

/-! ## Sums over validator indices, read at positions -/

/-- A position that holds a validator and meets a test is among the positions that meet it. -/
theorem mem_positions_filter (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) {i : ℕ} {w : Validator}
    (found : state.validators.data[i]? = some w) {p : ℕ → Prop} [DecidablePred p] (test : p i) :
    i ∈ (pinTerms config state ancestor finalizedState).positions.filter p :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, test⟩

/-- A flag read from the validator at a position can hold only where the position holds one.

The flag is the `any` of the validator, or its `map` read with a default of `false`. -/
theorem validator_of_flag {state : BeaconState preset fork} {i : ℕ} {f : Validator → Bool}
    (flag : (state.validators.data[i]?).any f = true ∨
      ((state.validators.data[i]?).map f).getD false = true) :
    ∃ w, state.validators.data[i]? = some w := by
  cases found : state.validators.data[i]? with
  | none =>
    rw [found] at flag
    simp at flag
  | some w => exact ⟨w, rfl⟩

/-- A voter active at the epoch of a state holds a validator there that is active at that epoch. -/
theorem active_of_activeVoters (early : fork < .glamsterdam)
    {s : BeaconState preset fork} {v : ValidatorIndex} (member : v ∈ activeVoters s) :
    ∃ w, s.validators.data[v.toNat]? = some w ∧
      isActiveValidator w (getCurrentEpoch s) = true := by
  have listed : v ∈ getActiveValidatorIndices s (getCurrentEpoch s) := by
    simpa [activeVoters] using member
  exact (mem_getActiveValidatorIndices (s.validators.bound early)).mp listed

end Internal

end PinDrift
end EthLib.Consensus.Models.Network
