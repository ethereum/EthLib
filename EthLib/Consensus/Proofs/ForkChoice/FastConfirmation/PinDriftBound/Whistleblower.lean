module

import EthLib.Base.Proofs.Nat
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.Transition.BalanceDrift
public import EthLib.Consensus.Proofs.Transition.FfgJustification
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.SlashedExit
import EthLib.Consensus.Proofs.Transition.SlashedPersistence
import EthLib.Consensus.Proofs.Transition.EpochReads
import EthLib.Consensus.Proofs.Transition.PendingConsolidations
import EthLib.Consensus.Proofs.Transition.Committees
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Penalties
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Contracts.Ledger
import EthLib.Consensus.Proofs.Transition.EpochPending
import EthLib.Consensus.Proofs.Transition.Operations
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Reserved.Operations
import EthLib.Consensus.Proofs.Transition.Block
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Whistleblower
import EthLib.Consensus.Proofs.DirectSafety.BalanceSources
import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.Trace
import Mathlib.Data.Nat.Notation
import EthLib.Consensus.Proofs.Transition.EpochUpdates
import EthLib.Consensus.Proofs.Transition.ForkBoundary
import EthLib.Consensus.Proofs.Transition.StateTransition
import EthLib.Consensus.Proofs.Transition.BalanceCappedWithdrawals
import EthLib.Consensus.Proofs.Transition.BranchLedger
import EthLib.Consensus.Proofs.DirectSafety.IntervalFunding
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Assembly
import EthLib.Consensus.Proofs.Transition.BalanceNotRaised
import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle
import EthLib.Consensus.Proofs.Transition.ValidatorCaps
public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Bound
import EthLib.Consensus.Proofs.Transition.Totality.Supply
import EthLib.Consensus.Proofs.Transition.EffectiveFall
import EthLib.Consensus.Proofs.DirectSafety.Evidence
import EthLib.Consensus.Proofs.DirectSafety.Fields
import EthLib.Consensus.Proofs.Transition.ValidatorKeys
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.DirectSafety.DepartureQueue
import EthLib.Consensus.Proofs.Transition.ActivationExitOrder
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import EthLib.Consensus.Proofs.DirectSafety.IntervalBounds
import EthLib.Consensus.Proofs.Transition.BlockCredits
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Ceiling
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Issuance
import EthLib.Consensus.Proofs.DirectSafety.Apriori.Branch
import EthLib.Consensus.Proofs.Transition.EpochRewards
import EthLib.Consensus.Proofs.Transition.RewardDeltas
import EthLib.Consensus.Proofs.Transition.FfgStake
import EthLib.Consensus.Proofs.Time
import EthLib.Consensus.Proofs.Participation
import Mathlib.Algebra.Order.Floor.Div
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.HeaderSupplies

/-! The pin reserve: whistleblower envelopes, rows and flow funding bounds. -/

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety PinKeys
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- The whistleblower credits of a set of keys over a run fit the limits of its slashing events. -/
private theorem whistC_sum_le_limits {g m y : ForkedBeaconState preset}
    (shared : Run config checks g m) (genesis : Genesis config checks g)
    (tail : Run config checks m y) (early : y.fork < .glamsterdam) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.whistC tail high v.toNat ≤
      (events.map fun e => if e.source = .slashings then e.creditLimit else 0).sum := by
  obtain ⟨found, foundOk, bounded⟩ := Run.balanceEvents_bounded shared tail genesis early high
  rw [replayed] at foundOk
  cases foundOk
  simpa [Internal.whistC] using Internal.creditScan_sum_le S UInt64.toNat (fun s => decide (s =
    .slashings))
    (fun _ => false) high (fun e => e.creditLimit) tail replayed fun e member _ =>
      Internal.sum_keyCredit_le_creditLimit S e (bounded e member).1

/-- The positions of the keys slashed on C's branch after the split.

They are unslashed at the split and slashed at C. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slashedOnC (split counted : BeaconState
  preset fork) : Finset ℕ :=
  (Finset.range counted.validators.data.size).filter fun i =>
    (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i]?.map (·.slashed)).getD false = true

/-- The bound on the effective balance of a key of R's registry that R's call reads.

It is the key's effective balance, its rise and one increment, if R's branch slashes it.

It is also at least the key's effective balance at the finalized state.

A prefix state of the finalized epoch can reach that balance.

R's branch budget supplies that bound and an increment to cover the slashing penalty.

A key that `exitedSlashable`, `late` or `pendingR` charges is read at its balance and rise, or `bF`.

It is also read at its effective balance at the finalized state.

It is read without `ebUp`, which can exceed them.

Otherwise it is also at least the key's bound `ebUp`. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleEnv (t : PinTerms preset)
  (pulled anc fin : BeaconState preset fork) (i : ℕ) :
    ℕ :=
  if t.slashedRB i = true then
    max (balanceAt pulled i + t.rise i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (balanceAt fin i)
  else if PinTerms.exitedSlashable anc pulled i = true ∨
      (t.tight = false ∧ (t.lateB i = true ∨ t.pendingRB i = true)) then
    max (balanceAt pulled i + t.rise i) (max (t.bF i) (balanceAt fin i))
  else max (max (t.ebUp i) (balanceAt pulled i + t.rise i)) (t.bF i)

/-- A balance within the finalized effective balance is within `whistleEnv`, plus any slack.

The first two branches of `whistleEnv` hold the finalized effective balance.

The third holds `ebUp`, which is at least that. -/
private theorem short_end (h : Setting config checks g split fin pulled anc counted V) (i : ℕ)
    {X : ℕ} (hfin : X ≤ balanceAt fin i) (slack : ℕ) :
    X ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i + slack := by
  have up : balanceAt fin i ≤ (pinTerms config pulled anc fin).ebUp i :=
    Internal.effective_fin_le_ebUp h i
  unfold Internal.whistleEnv
  split_ifs <;> omega

/-- A state of C's run in the epoch of a state `c` has its effective balance within `whistleEnv`.

The run from `c` to it stays in one epoch.

So a key of the registry at `c` keeps its effective balance there.

If the balance at `c` is within the finalized bound, it stays within that bound plus the slack.

The finalized state is the case `c = fin`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.short_in_fin (h : Setting config
  checks g split fin pulled anc counted V)
    {c : BeaconState preset fork}
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {a b : ForkedBeaconState preset} (step : Step config checks a b)
    (member : tailC.Contains step) (i : ℕ) (inside : i < c.validators.data.size)
    (left : effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i ≤ balanceAt fin i) (slack : ℕ)
    (sameEpoch : (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch c).toNat) :
    effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i + slack
      := by
  obtain ⟨pre, post, -⟩ := tailC.contains_split step member
  have early : a.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
  have forward : (getCurrentEpoch c).toNat ≤ (getCurrentEpoch a.state).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps (fromC.append pre).chainSteps)
  have same : getCurrentEpoch a.state = getCurrentEpoch c :=
    UInt64.toNat_inj.mp (by omega)
  have kept := (fromC.append pre).effectiveKept_of_same_epoch early same i inside
  exact short_end h i (by rw [kept]; exact left) slack

/-- The credits that raise the effective balance of a key of R's registry on C's branch.

They are the key's credits at eleven tenths, rounded up, with the bands of credits and seat debits.

The credits hold the key's own whistleblower credits.

Its unit of gain and the leak that its sync debits induce on R's run come on top, unscaled.

The seat debits are those of the two runs that R shares with C.

A key that exited before the finalized state also holds its credits on the shared segment.

A sync credit there has the band of its rounding. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleSlackBase (t : PinTerms preset)
  {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (rrun : Run config checks x' y') (highC high : ℕ)
    (eventsC eventsF events : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  (11 * (Internal.propN tail highC i + Internal.depPre eventsC i + Internal.whistC tail highC i +
    Internal.syncCr eventsC i +
    Internal.consAmt eventsC i + Internal.syncD eventsF i + Internal.syncD events i) + 9) / 10 +
      Internal.bandC tail highC i +
    Internal.bandX fin highC i + Internal.bandR (eventsF ++ events) i +
    Internal.unitK t tail highC eventsC events eventsF i + Internal.inducedR t rrun i +
  if t.exitBeforeFin i = true then
    (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX fin
      high i +
      (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0)
  else 0

/-- The credits of `whistleSlackBase`, and a second unit of gain for a key that R slashes.

The second unit pays the joint floor that R's slashing penalty can tip. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleSlack (t : PinTerms preset) {x y
  : ForkedBeaconState preset}
    (tail : Run config checks x y) {x' y' : ForkedBeaconState preset}
    (rrun : Run config checks x' y') (highC high : ℕ)
    (eventsC eventsF events : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  Internal.whistleSlackBase t tail rrun highC high eventsC eventsF events fin i +
    (if 0 < Internal.slashW t i then t.unitGain else 0)

/-- What a created key's charge adds to the effective balance of the key at an earlier exit.

It is the band, the gains at the largest rate and the key's credits on C's branch. -/
private def whistleExtra (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : ℕ) (eventsC : List (BalanceEvent preset)) (i : ℕ) :
    ℕ :=
  preset.upwardBand + t.depth * t.gainRateMax +
    (Internal.credC tail high i + Internal.whistC tail high i + Internal.syncCr eventsC i)

/-- The bound on the effective balance at its slashing of a key of the split's registry.

A key that is not active at C and has a departure charge on C's branch is also read at its charge.

That reading is the charge, the key's rise after it, and the slack.

A charge in the split's own epoch reads the balance before the credits of `pre`.

So the key's proposer, whistleblower and sync credits over `pre` are read too.

The slashing starts the key's exit, or finds the exit that an earlier charge started. -/
private def whistleRead (t : PinTerms preset) (pulled anc counted : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {x' y' : ForkedBeaconState preset} (rrun : Run config checks x' y')
    {x'' y'' : ForkedBeaconState preset} (pre : Run config checks x'' y'') (highC high : ℕ)
    (eventsC eventsF events eventsP : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) : ℕ :=
  if ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      (tail.departureCharges.any fun c => c.index == i) = true then
    min (Internal.whistleEnv t pulled anc fin i +
        Internal.whistleSlack t tail rrun highC high eventsC eventsF events fin i)
      (Internal.chargeAmt tail i + Internal.riseQ tail highC i + (Internal.propN pre highC i +
        Internal.whistC pre highC i +
        Internal.syncCr eventsP i) + Internal.whistleSlack t tail rrun highC high eventsC eventsF
          events fin i)
  else
    Internal.whistleEnv t pulled anc fin i + Internal.whistleSlack t tail rrun highC high eventsC
      eventsF events fin i

/-- The bound on the effective balance at its slashing of a key created after the split.

The key is active at C.

At a high gain rate it is the largest cap.

Otherwise it is the key's credits, their gains over the window, and a band. -/
private def createdCeil (t : PinTerms preset) {x y : ForkedBeaconState preset}
    (tail : Run config checks x y) (high : ℕ) (eventsC : List (BalanceEvent preset)) (i : ℕ) :
    ℕ :=
  let credits := Internal.credC tail high i + Internal.whistC tail high i + Internal.syncCr eventsC
    i
  let rate := t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
  if t.gainHigh = true then preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
  else
    credits + t.depth * (11 * credits / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * rate /
      WEIGHT_DENOMINATOR.toNat) + t.depth * (rate / WEIGHT_DENOMINATOR.toNat + 2) +
        preset.downwardBand

/-- The gain of a created key's credits and base stake is at most the gain of its flows and a unit.

The key's base stake is credits, so it sits in the flows `Z`.

The flow of `Cr` and the slack `S - e0` compound at eleven tenths.

The floor holds the base gain `D * q` and `D`.

A key whose rate is low has `11 * D * q ≤ e0`, so its base gain is within a tenth of its stake.

The floors then lose one increment against the floor of the flows, which the unit pays. -/
private theorem created_gain_arith (I WD F P D e0 S Cr Z β : ℕ)
    (key : 11 * D * (P * F) < WD * I) (start : e0 ≤ S + β) (flows : Cr + S ≤ Z)
    (small : 11 * (β + D) < 10 * I) :
    D * (11 * (Cr + (S - e0) + D * (e0 / I * P * F / WD) + D) / (10 * I) * P * F / WD) +
        (D * (e0 / I * P * F / WD) + D) ≤
      D * (11 * Z / (10 * I) * P * F / WD) + D * (P * F / WD + 2) := by
  have hWD : 0 < WD := Nat.pos_of_ne_zero fun zero => by
    rw [zero] at key
    omega
  simp only [Nat.mul_assoc]
  obtain ⟨a, ha⟩ : ∃ a, a = P * F := ⟨_, rfl⟩
  rw [← ha] at key ⊢
  obtain ⟨N2, hN2⟩ : ∃ N2, N2 = e0 / I := ⟨_, rfl⟩
  rw [← hN2]
  obtain ⟨q, hq⟩ : ∃ q, q = N2 * a / WD := ⟨_, rfl⟩
  rw [← hq]
  -- the base gain is at most a eleventh of the stake
  have baseGain : 11 * (D * q) ≤ e0 := by
    have floor : q * WD ≤ N2 * a := by rw [hq]; exact Nat.div_mul_le_self _ _
    have step : 11 * D * q * WD ≤ WD * I * N2 := by
      calc 11 * D * q * WD = 11 * D * (q * WD) := by ring
        _ ≤ 11 * D * (N2 * a) := Nat.mul_le_mul_left _ floor
        _ = N2 * (11 * D * a) := by ring
        _ ≤ N2 * (WD * I) := Nat.mul_le_mul_left _ key.le
        _ = WD * I * N2 := by ring
    have cancel : 11 * D * q ≤ I * N2 := by
      refine Nat.le_of_mul_le_mul_right (c := WD) ?_ hWD
      calc 11 * D * q * WD ≤ WD * I * N2 := step
        _ = I * N2 * WD := by ring
    have rounded : I * N2 ≤ e0 := by rw [hN2]; exact Nat.mul_div_le _ _
    calc 11 * (D * q) = 11 * D * q := by ring
      _ ≤ e0 := Nat.le_trans cancel rounded
  obtain ⟨X, hX⟩ : ∃ X, X = Cr + (S - e0) + D * q + D := ⟨_, rfl⟩
  rw [← hX]
  have total : 11 * X + 10 * e0 ≤ 11 * Z + 11 * (β + D) := by omega
  -- the floors of the stake and of the credits add to one floor
  obtain ⟨N1, hN1⟩ : ∃ N1, N1 = 11 * X / (10 * I) := ⟨_, rfl⟩
  obtain ⟨N3, hN3⟩ : ∃ N3, N3 = 11 * Z / (10 * I) := ⟨_, rfl⟩
  rw [← hN1, ← hN3]
  have joint : N1 + N2 ≤ N3 + 1 := by
    have n2 : N2 = 10 * e0 / (10 * I) := by
      rw [hN2, Nat.mul_div_mul_left _ _ (by norm_num : 0 < 10)]
    have add := Nat.div_add_div_le_add_div (x := 11 * X) (y := 10 * e0) (z := 10 * I)
    have mono := Nat.div_le_div_right (c := 10 * I) total
    have more := Nat.add_div_le_div_add_div_add_one (11 * Z) (11 * (β + D)) (10 * I)
    have none : 11 * (β + D) / (10 * I) = 0 := Nat.div_eq_of_lt small
    omega
  have gains : N1 * a / WD + N2 * a / WD ≤ N3 * a / WD + a / WD + 1 := by
    have add := Nat.div_add_div_le_add_div (x := N1 * a) (y := N2 * a) (z := WD)
    have mono : (N1 + N2) * a / WD ≤ (N3 + 1) * a / WD :=
      Nat.div_le_div_right (Nat.mul_le_mul_right _ joint)
    have more := Nat.add_div_le_div_add_div_add_one (N3 * a) a WD
    rw [Nat.add_mul] at mono
    rw [Nat.add_mul, Nat.one_mul] at mono
    omega
  have scaled := Nat.mul_le_mul_left D gains
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one] at scaled
  rw [← hq] at scaled
  rw [Nat.mul_add D (a / WD) 2]
  omega

/-- The deposits and consolidations that a run credits to a key are among its non-reward credits. -/
private theorem scan_deposits_consolidations_le (v high : ℕ) {x y : ForkedBeaconState preset}
    (run : Run config checks x y) :
    (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v high run) +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v high run) ≤
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v high run) := by
  have named := Internal.creditScan_or (fun _ => false) (fun s => decide (s ≠ .rewards))
    (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits ∨ s = .consolidations))
    (fun s => decide (s ≠ .rewards ∧ s ≠ .deposits ∧ s ≠ .consolidations))
    (fun _ => rfl) (fun s => by cases s <;> decide) (fun _ => by simp)
    (fun s => by cases s <;> decide) v high run
  have pair := Internal.creditScan_or (fun _ => false)
    (fun s => decide (s = .deposits ∨ s = .consolidations)) (fun _ => false) (fun _ => false)
    (fun s => decide (s = .deposits)) (fun s => decide (s = .consolidations))
    (fun _ => rfl) (fun s => by cases s <;> decide) (fun _ => by simp)
    (fun s => by cases s <;> decide) v high run
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key created on C's branch is at most its credits and their gains.

The run from the split reaches a state `z` where the key holds the activation reserve, and then C.

The bound holds at every state of C's run after `z`, and at C.

The key's base stake is credits, so one floor of the flows pays its gain.

The rate premise is that of the low regime: `key` reads it at the depth of the call. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_ceiling (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (key : 11 * (min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
      (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
        WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    let Z := Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
      Internal.syncCr eventsC v.toNat
    ∃ (z : ForkedBeaconState preset) (pre : Run config checks ⟨fork, split⟩ z)
      (post : Run config checks z ⟨fork, counted⟩), tailC = pre.append post ∧ 0 < Z ∧
      (∀ p ∈ pre.balancePath, ∀ w : Validator, p.state.validators.data[v.toNat]? = some w →
        w.activationEpoch ≠ FAR_FUTURE_EPOCH →
        (getCurrentEpoch p.state).toNat + 1 < w.activationEpoch.toNat) ∧
      ∀ p ∈ post.balancePath, effectiveAt p v.toNat ≤ Z +
        (min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          (11 * Z / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
            (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
        (min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
          (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) +
        preset.downwardBand := by
  classical
  intro Z
  obtain ⟨z, pre, post, splitEq, zEarly, zFork, zCounted, inside, funded, hysteresis, reserve,
    walk, -, ahead⟩ := Internal.created_start h tailC highC endEpochC
      activated absent
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have flows : Internal.grossScan v.toNat highC tailC +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC tailC) ≤
        Z :=
    (Internal.credits_le_sources shared h.genesis tailC h.early electra v.toNat highC replayedC).1
  have incPos := h.bands.1
  have alignedMax := (Internal.cap_values_aligned h.aligned).2
  have fuluZ : .fusaka ≤ z.fork := Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)
  have electraZ : .pectra ≤ z.fork := Nat.le_trans (by decide) fuluZ
  obtain ⟨P', hP', rate⟩ := Internal.key_rate_pre h tailC h.near
  obtain rfl : P = P' := hP.trans hP'.symm
  have inRun : ∀ p ∈ post.balancePath, p ∈ tailC.balancePath := fun p member => by
    obtain ⟨front, last⟩ := Run.balancePath_last pre
    obtain ⟨rest, head⟩ := Run.balancePath_head post
    rw [head] at member
    rw [splitEq, Run.balancePath_append, last, head]
    rcases List.mem_cons.mp member with rfl | later <;> simp [*]
  have backZ : (⟨fork, counted⟩ : ForkedBeaconState preset).fork ≤ z.fork := by
    have := fork_le_of_chainSteps pre.chainSteps
    exact this
  have capCeil : ∀ p ∈ post.balancePath, PinTerms.capAt p v.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := fun p member => by
    obtain ⟨r1, -, -⟩ := Internal.balancePath_endpoint post
      (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) backZ member
    exact Internal.capAt_le_capMax h.caps (Nat.le_trans electraZ (fork_le_of_chainSteps
      r1.chainSteps))
      v.toNat
  have splitZ := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) := ⟨_, rfl⟩
  rw [← hD] at key ⊢
  obtain ⟨e0, he0⟩ : ∃ e0, e0 = effectiveAt z v.toNat := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, S = actualBalanceAt z v.toNat := ⟨_, rfl⟩
  obtain ⟨Cr, hCr⟩ : ∃ Cr, Cr = Internal.netScan v.toNat highC post +
    (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC post) :=
    ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W, W = S - e0 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, rfl⟩
  have alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [he0]
    exact FloorTrace.effective_aligned (shared.append pre) h.genesis h.aligned v.toNat
  have core := Internal.c_ceiling_abstract post h.early fuluZ v.toNat inside highC P
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat alignedMax
    (Internal.effectiveAt_le_capMax (shared.append pre) h.genesis h.caps zEarly v.toNat)
    capCeil
    (fun p member total perIncrement totalOk perOk =>
      rate p (inRun p member) total perIncrement totalOk perOk)
    endEpochC incPos D Cr Cr e0 C S W (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq
    alignedE0 hC (by simp only at splitZ ⊢; omega) (by rw [hS]; exact Nat.min_le_left _ _)
    (by omega) (le_of_eq hCr.symm) key (by omega)
  obtain ⟨gc, rfl, -, bound, -⟩ := core
  -- the credits, the base stake and the gains of the key
  have beforeZ : S ≤ Internal.grossScan v.toNat highC pre +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC pre) +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations)) v.toNat highC
        pre) := by
    rw [hS]
    exact walk
  have splitScans := scan_deposits_consolidations_le v.toNat highC pre
  subst splitEq
  rw [Internal.grossScan_append, Internal.creditScan_append (fun _ => false) (fun s => decide (s ≠
    .rewards))
    v.toNat highC pre post] at flows
  obtain ⟨e2, ok2⟩ := post.balanceEvents_ok h.early highC
  have netLe := (Internal.credits_le_sources (shared.append pre) h.genesis post h.early electraZ
    v.toNat
    highC ok2).2.1
  have credited : Cr + S ≤ Z := by omega
  -- the key's rate is low against an increment, so the depth is small
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  have quarter := h.facts.quarterBand
  have four : 4 ≤ P := by
    rw [hP]
    exact Internal.four_le_perIncrement h
  have small : 11 * (preset.downwardBand + D) < 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [weights, denominator] at key
    have scaled := Nat.mul_le_mul_left D (show 4 * 54 ≤ P * 54 by omega)
    have regroup : 11 * D * (P * 54) = 11 * (D * (P * 54)) := by ring
    omega
  have arith := created_gain_arith preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P D e0 S Cr Z
    preset.downwardBand key (by rw [he0, hS]; exact hysteresis) credited small
  rw [← hq, ← hW] at arith
  refine ⟨z, pre, post, rfl, ?_, ahead, fun p member => ?_⟩
  · have := Internal.maxEffectiveBalance_pos h
    omega
  obtain ⟨r1, r2, cut⟩ := Internal.balancePath_endpoint post
    (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) backZ member
  have prefixPath : ∀ z' ∈ r1.balancePath, z' ∈ post.balancePath := fun z' mem => by
    have joined : post.balancePath = r1.balancePath ++ r2.balancePath.tail := by
      rw [← Run.balancePath_append]
      exact congrArg Run.balancePath cut.symm
    rw [joined]
    exact List.mem_append_left _ mem
  have pEarly : p.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  have ceiling := Internal.Run.effective_ceiling_of_balance_ceiling r1 pEarly fuluZ v.toNat
    inside
    (S + Cr + (D * (11 * (Cr + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) *
      P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) +
        (D * q + D)))
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat alignedMax
    (Internal.effectiveAt_le_capMax (shared.append pre) h.genesis h.caps zEarly v.toNat)
    (fun z' mem => bound z' (prefixPath z' mem)) (fun z' mem => capCeil z' (prefixPath z' mem))
  obtain ⟨-, same, third, ordered⟩ := ceiling
  by_cases crossed : (getCurrentEpoch z.state).toNat < (getCurrentEpoch p.state).toNat
  · have := third crossed
    omega
  · have stays := same (by omega)
    omega

/-- Off the high gain rate, the full window's weighted gain is below an increment. -/
private theorem wide_of_lowGain (h : Setting config checks g split fin pulled anc counted V)
    (lowGain : (pinTerms config pulled anc fin).gainHigh = false) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have low : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
    have notHigh : (!decide (11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRateMax + 1) ≤
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat)) = false := lowGain
    simpa using notHigh
  have gainMax : (pinTerms config pulled anc fin).gainRateMax =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := rfl
  exact Internal.rate_per_increment preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum
    (pinTerms config pulled anc fin).perIncrement
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat (pinTerms config pulled anc fin).depth
    h.bands.1 (by decide) (Internal.cap_values_aligned h.aligned).2 (by rw [← gainMax]; exact low)

/-- Off the high gain rate, the depth of the window is small against the rate.

The product of depth and rate is below an eleventh of an increment. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_of_lowGain (h : Setting config
  checks g split fin pulled anc counted V)
    (lowGain : (pinTerms config pulled anc fin).gainHigh = false) :
    11 * (min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  exact Nat.lt_of_le_of_lt
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 (Nat.min_le_left _ _)))
    (wide_of_lowGain h lowGain)

/-- The kept arm's test bounds the gain at the full depth. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.keptArm_eq (i : ℕ)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).gainRate i + 1) ≤
      (pinTerms config pulled anc fin).ebUp i := by
  simp only [pinTerms, Bool.and_eq_true, decide_eq_true_eq] at kept
  exact kept.2

/-- The kept arm bounds the gain per increment up to the full depth. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.key_of_kept (h : Setting config
  checks g split fin pulled anc counted V)
    (i D : ℕ) (depth : D ≤ (pinTerms config pulled anc fin).depth)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    11 * D * ((pinTerms config pulled anc fin).perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  exact Internal.rate_per_increment _ _ _ _ _ _ h.bands.1 (by decide) (Internal.ebUp_aligned h i)
    (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 depth)) (Internal.keptArm_eq i
        kept))

/-- The effective balance at slashing of a key created after the split and active at C.

At a high gain rate the bound uses the largest cap.

At a low rate it uses the branch's credits, their gains over the window and a rounding band. -/
private theorem created_active (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {a b : ForkedBeaconState preset} (step : Step config checks a b) (member : tailC.Contains step)
    (i : ℕ) (created : ¬ i < split.validators.data.size)
    (active : isActiveAt counted (getCurrentEpoch counted) i = true)
    (flag : (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
      (b.state.validators.data[i]?.map (·.slashed)).getD false) = true) :
    effectiveAt a i ≤ createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨pre', post', cut', aEarly, -⟩ :=
    DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
  by_cases high : (pinTerms config pulled anc fin).gainHigh = true
  · simp only [createdCeil, high, ↓reduceIte]
    exact Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre') h.genesis h.caps
      aEarly i
  have lowGain : (pinTerms config pulled anc fin).gainHigh = false := by simpa using high
  -- the key as a validator index
  obtain ⟨w, found, -⟩ := isActiveAt_eq_true_iff.mp active
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have below := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  obtain ⟨v, hvi⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  subst hvi
  have member_active : v ∈ activeVoters counted :=
    List.mem_toFinset.mpr (mem_getActiveValidatorIndices_of_isActiveAt active)
  have activated := Internal.activated_of_activeVoters h.early member_active
  have absent : split.validators.data.size ≤ v.toNat := Nat.le_of_not_lt created
  have key := Internal.key_of_lowGain h lowGain
  obtain ⟨z, pre, post, cut, positive, ahead, bound⟩ := Internal.created_ceiling h tailC highC
      endEpochC
    replayedC activated absent (pinTerms config pulled anc fin).perIncrement rfl key
  -- the state `a` is a state of the run, so it is before `z` or after it
  have inPath : a ∈ tailC.balancePath := by
    rw [cut', Run.balancePath_append]
    refine List.mem_append_left _ ?_
    simp only [Run.balancePath, List.mem_append]
    exact .inr (List.mem_of_mem_head? (Step.balancePath_ends step).1)
  have ends : a ∈ pre.balancePath ∨ a ∈ post.balancePath := by
    rw [cut, Run.balancePath_append] at inPath
    rcases List.mem_append.mp inPath with first | later
    · exact .inl first
    · exact .inr (List.mem_of_mem_tail later)
  rcases ends with before | after
  · -- a key that the step slashes was activated by the epoch of `a`, which `z` comes after
    have bEarly : b.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps post'.chainSteps) h.early
    have finite : getCurrentEpoch a.state < FAR_FUTURE_EPOCH :=
      UInt64.lt_iff_toNat_lt.mpr (by
        have := getCurrentEpoch_succ_lt_farFuture h.twoSlots a.state
        omega)
    obtain ⟨u, found, far, reached⟩ := Step.slashed_activated step
      (Nat.le_trans electra (fork_le_of_chainSteps pre'.chainSteps)) bEarly h.caps.activation
      h.caps.compounding (Internal.Setting.delay h) finite v.toNat
      (((shared.append fromFin).append pre').exit_activated h.genesis v.toNat) flag
    have := ahead a before u found far
    have := UInt64.le_iff_toNat_le.mp reached
    omega
  have ceiling := bound a after
  have minLe : min (pinTerms config pulled anc fin).depth
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) ≤
        (pinTerms config pulled anc fin).depth := Nat.min_le_left _ _
  simp only [createdCeil, lowGain, Bool.false_eq_true, ↓reduceIte]
  rw [Nat.mul_assoc (11 * _ / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))] at ceiling
  exact ceiling.trans (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ minLe) _) (Nat.mul_le_mul_right _ minLe)) le_rfl)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The whistleblower credits of any set of keys on C's branch are at most the reward base.

The base is the slashing reward of each key slashed on that branch, read at its balance then.

A key of the split's registry is read at the bound `registry` gives for it.

If it is not active at C and has a charge there, it is also read at `registryCharge`.

`registry` is asked for each key that is unslashed at the split, at each step of C's branch.

A key slashed before the split has no term, since its credit on C's branch is zero.

A key of R's registry that is also slashed on R's branch is a term of the first sum.

A consumer that pays those terms by another budget splits that sum by the key's slashing on R.

A new key active at C is bounded by the largest cap or by its credits, gains and rounding band.

If it has exited by C, it is read at its charge and credits.

A charge in the split's own epoch also reads the credits of `pre`, the run from that epoch's start.

The bound for a charged key accounts for how that prefix joins the run. -/
private theorem whistle_core (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {eventsP : List (BalanceEvent preset)}
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    (registryCharge : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
            (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    (S : Finset ValidatorIndex) :
    ∑ v ∈ S, Internal.whistC tailC highC v.toNat ≤
      (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
            (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      (∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true),
        min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      (∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true),
        min (Internal.chargeAmt tailC i +
            whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have limit := whistC_sum_le_limits (shared.append fromFin) h.genesis tailC h.early highC
    replayedC S
  obtain ⟨E, hE⟩ : ∃ E : ℕ → ℕ, ∀ i, E i =
      if (split.validators.data[i]?.map (·.slashed)).getD false = false then
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
            (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨cr, hcr⟩ : ∃ cr : ℕ → ℕ, ∀ i, cr i =
      if isActiveAt counted (getCurrentEpoch counted) i = true then
        min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
      else min (Internal.chargeAmt tailC i +
          whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := ⟨_, fun _ => rfl⟩
  -- the keys of R's registry are read at `registry`, or at the largest cap if slashed at the split
  have regE : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i ≤ E i := by
    intro a b step member i inside flag
    rw [hE i]
    obtain ⟨pre, -, -, aEarly, -⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
    have capped := Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre)
      h.genesis
      h.caps aEarly i
    by_cases unslashed : (split.validators.data[i]?.map (·.slashed)).getD false = false
    · simp only [unslashed]
      refine le_min ?_ capped
      simp only [whistleRead]
      split
      · rename_i cond
        exact le_min (registry step member i inside unslashed flag)
          (registryCharge step member i inside unslashed flag cond.2)
      · exact registry step member i inside unslashed flag
    · simp only [unslashed]
      exact capped
  -- the created keys are read at `createdCeil` while active at C, and at their charge after
  have createdE : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, split.validators.data.size ≤ i →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        effectiveAt a i / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤ cr i := by
    intro a b step member i created flag
    rw [hcr i]
    obtain ⟨pre, -, -, aEarly, -⟩ :=
      DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
    have capped := Internal.effectiveAt_le_capMax ((shared.append fromFin).append pre)
      h.genesis
      h.caps aEarly i
    by_cases act : isActiveAt counted (getCurrentEpoch counted) i = true
    · simp only [act]
      exact Nat.div_le_div_right (le_min (created_active h tailC highC endEpochC replayedC step
        member i (Nat.not_lt.mpr created) act flag) capped)
    · simp only [act]
      exact Nat.div_le_div_right (le_min (Internal.created_charge h fromFin tailC
        (whistleExtra (pinTerms config pulled anc fin) tailC highC eventsC)
        (fun step member i created old foundA assigned =>
          Internal.earlier_charge h tailC highC endEpochC replayedC step member i created old foundA
            assigned) step member i created flag) capped)
  have charged := Internal.slashing_charge h fromFin tailC highC endEpochC replayedC E cr regE
    createdE
  refine limit.trans (charged.trans (le_of_eq ?_))
  -- the sum over the slashed keys splits into the three kinds of key
  change ∑ i ∈ Internal.slashedOnC split counted, _ = _
  rw [← Finset.sum_filter_add_sum_filter_not (Internal.slashedOnC split counted)
    (fun i => i < split.validators.data.size)]
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)]
  rw [← add_assoc]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
    have unslashed := (Finset.mem_filter.mp inSlashed).2.1
    simp only [inside, ↓reduceIte, hE i, unslashed]
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inNew, act⟩ := Finset.mem_filter.mp member
    have outside := (Finset.mem_filter.mp inNew).2
    simp [outside, hcr i, act]
  · refine Finset.sum_congr rfl fun i member => ?_
    obtain ⟨inNew, act⟩ := Finset.mem_filter.mp member
    have outside := (Finset.mem_filter.mp inNew).2
    simp [outside, hcr i, act]

/-- The sum of a function of the positions over the images of the positions of a set is its sum. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.sum_image_ofNat (T : Finset ℕ)
  (small : ∀ i ∈ T, i < 2 ^ 64) (f : ℕ → ℕ) :
    ∑ v ∈ T.image UInt64.ofNat, f v.toNat = ∑ i ∈ T, f i := by
  rw [Finset.sum_image fun a ha b hb same => by
    rw [← UInt64.toNat_ofNat_of_lt' (small a ha), ← UInt64.toNat_ofNat_of_lt' (small b hb), same]]
  exact Finset.sum_congr rfl fun i member => by rw [UInt64.toNat_ofNat_of_lt' (small i member)]

/-- A slashed flag at a position of the registry is the flag that `slashedOnC` reads. -/
private theorem slashedFlagAt_eq_some {s : BeaconState preset fork} {i : ℕ} {b : Bool} :
    slashedFlagAt s i = some b ↔
      i < s.validators.data.size ∧ (s.validators.data[i]?.map (·.slashed)).getD false = b := by
  constructor
  · intro flag
    have inside : i < s.validators.data.size := by
      by_contra out
      simp [slashedFlagAt, Array.getElem?_eq_none (Nat.le_of_not_lt out)] at flag
    refine ⟨inside, ?_⟩
    unfold slashedFlagAt at flag
    rw [flag]
    rfl
  · rintro ⟨inside, flag⟩
    simp only [slashedFlagAt, Array.getElem?_eq_getElem inside, Option.map_some] at flag ⊢
    simpa using flag

/-- The keys of `SC` are the keys of `slashedOnC` inside the split's registry, read at positions. -/
private theorem sum_SC_positions (h : Setting config checks g split fin pulled anc counted V)
    (f : ℕ → ℕ) :
    ∑ v ∈ Internal.SC pulled counted split, f v.toNat =
      ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size), f
          i := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  have limit := BeaconState.validators_size_lt_of_lt_glamsterdam h.early pulled
  rw [← Finset.sum_image (f := f) (g := UInt64.toNat) fun a _ b _ same => UInt64.toNat_inj.mp same]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  constructor
  · intro mem
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp mem
    obtain ⟨-, hcs, hss⟩ := Finset.mem_filter.mp hv
    obtain ⟨hsplit, flagS⟩ := slashedFlagAt_eq_some.mp hss
    obtain ⟨hcount, flagC⟩ := slashedFlagAt_eq_some.mp hcs
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcount, flagS, flagC⟩, hsplit⟩
  · intro mem
    obtain ⟨hmem, hin⟩ := Finset.mem_filter.mp mem
    obtain ⟨hrange, hsl, hcs⟩ := Finset.mem_filter.mp hmem
    have below := (Nat.lt_of_lt_of_le hin grows).trans limit
    refine Finset.mem_image.mpr ⟨UInt64.ofNat i, ?_, UInt64.toNat_ofNat_of_lt' below⟩
    rw [Internal.SC, Finset.mem_filter, UInt64.toNat_ofNat_of_lt' below]
    exact ⟨Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (by omega), rfl⟩,
      slashedFlagAt_eq_some.mpr ⟨Finset.mem_range.mp hrange, hcs⟩,
      slashedFlagAt_eq_some.mpr ⟨hin, hsl⟩⟩

/-- The keys of `CS` are the keys of `slashedOnC` beyond the split's registry, read at positions. -/
private theorem sum_CS_positions (h : Setting config checks g split fin pulled anc counted V)
    (f : ℕ → ℕ) :
    ∑ v ∈ Internal.CS counted split, f v.toNat =
      ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
          f i := by
  classical
  rw [← Finset.sum_image (f := f) (g := UInt64.toNat) fun a _ b _ same => UInt64.toNat_inj.mp same]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  constructor
  · intro mem
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp mem
    obtain ⟨-, hge, hcs⟩ := Finset.mem_filter.mp hv
    obtain ⟨hcount, flagC⟩ := slashedFlagAt_eq_some.mp hcs
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcount, ?_, flagC⟩,
      Nat.not_lt.mpr hge⟩
    simp [Array.getElem?_eq_none hge]
  · intro mem
    obtain ⟨hmem, hout⟩ := Finset.mem_filter.mp mem
    obtain ⟨hrange, hsl, hcs⟩ := Finset.mem_filter.mp hmem
    have below := (Finset.mem_range.mp hrange).trans
      (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
    refine Finset.mem_image.mpr ⟨UInt64.ofNat i, ?_, UInt64.toNat_ofNat_of_lt' below⟩
    rw [Internal.CS, Finset.mem_filter, UInt64.toNat_ofNat_of_lt' below]
    exact ⟨Finset.mem_image.mpr ⟨i, hrange, rfl⟩, Nat.not_lt.mp hout,
      slashedFlagAt_eq_some.mpr ⟨Finset.mem_range.mp hrange, hcs⟩⟩

/-- The keys of `SC` that satisfy a test at their positions are those positions of `slashedOnC`. -/
private theorem sum_SC_filter_positions (h : Setting config checks g split fin pulled anc counted V)
    (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) :
    ∑ v ∈ Internal.SC pulled counted split with p v.toNat, f v.toNat =
      ∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter p,
        f i :=
  (Finset.sum_filter _ _).trans ((sum_SC_positions h (fun i => if p i then f i else 0)).trans
    (Finset.sum_filter _ _).symm)

/-- A key that C slashes after the split, and that R neither slashes nor exits, keeps its exit late.

The exit guard of its run from the finalized block holds along the run.

Its exit at C is after R's cutoff less the delay.

The exit is assigned on C's run, so it is a departure charge there, after the split.

Or it is assigned by the split, and then it is kept, and so it is R's exit.

R's exit is then after the cutoff.

The key cannot already be withdrawable by the finalized epoch. -/
private theorem slashedC_retained (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (i : ValidatorIndex)
    (slashedC : i.toNat ∈ Internal.slashedOnC split counted)
    (inside : i.toNat < split.validators.data.size)
    (notR : ¬ (pinTerms config pulled anc fin).slashedRB i.toNat = true)
    (notExit : ¬ PinTerms.exitedSlashable anc pulled i.toNat = true) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) := by
  classical
  obtain ⟨hLt, hSplit, hCount⟩ : i.toNat < counted.validators.data.size ∧
      (split.validators.data[i.toNat]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i.toNat]?.map (·.slashed)).getD false = true := by
    simpa [Internal.slashedOnC] using slashedC
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨vS, foundS⟩ : ∃ v, split.validators.data[i.toNat]? = some v :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨wC, foundC⟩ : ∃ w, counted.validators.data[i.toNat]? = some w :=
    ⟨_, Array.getElem?_eq_getElem hLt⟩
  have unslashedS : vS.slashed = false := by simpa [foundS] using hSplit
  have slashedAtC : wC.slashed = true := by simpa [foundC] using hCount
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  simp only at finSplit
  have shallow := h.shallow
  have slashC := tailC.newly_slashed_withdrawableEpoch h.caps.activation h.caps.compounding
    h.early (Internal.Setting.delay h) i.toNat vS wC foundS foundC unslashedS slashedAtC
  have late : (getCurrentEpoch pulled).toNat + 1 <
      wC.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
    by_cases unset : vS.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨c, mem, -, epoch⟩ := Internal.Run.charge_of_exit tailC electra h.early i.toNat
        (fun v found => by
          rw [foundS] at found
          cases found
          exact unset) wC foundC slashC.1
      have start := Run.departureCharges_epoch_ge_start tailC electra h.early c mem
      simp only at start
      omega
    · obtain ⟨wL, foundL, kept⟩ := tailC.registryLifecycle.validators i.toNat vS foundS
      obtain rfl : wL = wC := Option.some.inj (foundL.symm.trans foundC)
      have exitC := congrArg UInt64.toNat (kept.exitEpoch unset)
      obtain ⟨wR, foundR, keptR⟩ := tail.registryLifecycle.validators i.toNat vS foundS
      have exitR := congrArg UInt64.toNat (keptR.exitEpoch unset)
      by_cases far : (getCurrentEpoch pulled).toNat + 1 < wR.exitEpoch.toNat
      · omega
      have unslashedR : wR.slashed = false := by
        by_contra marked
        exact notR (Internal.slashedRB_of_newly_slashed h foundS foundR unslashedS (by simpa using
          marked))
      exfalso
      refine Internal.sc3a_unwithdrawn h foundS foundR foundC unslashedS slashedAtC unslashedR ?_
      by_contra waiting
      have reached : wR.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
      have lt := Nat.lt_of_not_le waiting
      apply notExit
      simp [PinTerms.exitedSlashable, foundR, unslashedR, reached, lt]
  intro m n before step after cut w found
  exact Internal.retained_of_exit h fromFin tailC _ (Nat.le_refl _) i foundC late before step after
    cut w
    found

/-- The withdrawal test includes keys withdrawable by R's next epoch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.withdrawnRB_of_le (config : Config)
  (pulled anc fin : BeaconState preset fork)
    {i : ℕ} {w : Validator} (found : pulled.validators.data[i]? = some w)
    (le : w.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    (pinTerms config pulled anc fin).withdrawnRB i = true := by
  simp only [pinTerms]
  simp [found, le]

/-- Deposits to a key unslashed before each credit count toward its pre-slashing deposits. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.deposits_le_depPre (L : List
  (BalanceEvent preset)) (i : ℕ)
    (clean : ∀ e ∈ L, e.source = .deposits →
      Internal.keyCredit i e = 0 ∨ ¬ slashedFlagAt e.before.state i = some true) :
    ((L.filter fun e => e.source = .deposits).map (Internal.keyCredit i)).sum ≤ Internal.depPre L i
      := by
  induction L with
  | nil => simp [Internal.depPre]
  | cons e rest ih =>
    have tail := ih fun x member => clean x (List.mem_cons_of_mem _ member)
    unfold Internal.depPre at tail ⊢
    by_cases dep : e.source = .deposits
    · rcases clean e List.mem_cons_self dep with zero | unslashed
      · by_cases slashed : slashedFlagAt e.before.state i = some true <;>
          simp [dep, zero, slashed] <;> omega
      · simp [dep, unslashed]
        omega
    · simp [dep]
      omega

/-- Each deposit of a run's replay that credits a key finds it unslashed.

The run ends with the key unslashed.

A deposit event of a block credits no balance.

One of a slot step starts from a state that does not hold the key slashed.

A slashed key stays slashed up to the end of the run. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.prefix_deposits_clean (h : Setting
  config checks g split fin pulled anc counted V)
    {a : ForkedBeaconState preset} (pre : Run config checks ⟨fork, split⟩ a)
    (aEarly : a.fork < .glamsterdam) (highC : ℕ) {e1 : List (BalanceEvent preset)}
    (replayed1 : pre.balanceEvents highC = .ok e1) (v : ValidatorIndex)
    (unslashedA : (a.state.validators.data[v.toNat]?.map (·.slashed)).getD false = false) :
    ∀ e ∈ e1, e.source = .deposits →
      Internal.keyCredit v.toNat e = 0 ∨ ¬ slashedFlagAt e.before.state v.toNat = some true := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  intro e member dep
  rcases (Internal.run_located pre electra aEarly highC replayed1).1 e member dep with
    unconditional | ⟨u, w, ok, es, contains, replayedEs, inEs, -⟩
  · have := unconditional v.toNat
    unfold Internal.keyCredit
    omega
  · right
    intro slashed
    obtain ⟨p1, p2, -⟩ := pre.contains_split (Step.slot ok) contains
    have wEarly : w.fork < .glamsterdam :=
      Nat.lt_of_le_of_lt (fork_le_of_chainSteps p2.chainSteps) aEarly
    have holds := Run.invariant h.genesis.invariant ((toFin.append fromFin).append p1)
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, one, two, -⟩ :=
      (Step.balanceEvents_sites (Step.slot ok) wEarly holds h.caps.compounding replayedEs) e inEs
    obtain ⟨x, found, flagged⟩ : ∃ x, e.before.state.validators.data[v.toNat]? = some x ∧
        x.slashed = true := by
      unfold slashedFlagAt at slashed
      cases hx : e.before.state.validators.data[v.toNat]? <;> simp_all
    obtain ⟨y, foundA, flagA⟩ :=
      ((one.trans two).trans p2.slashedPersistence) v.toNat x found flagged
    simp [foundA, flagA] at unslashedA

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A bound along R's run from the first state of a key holds on the whole run.

Before the first state `c` the key is absent, so its effective balance is zero there. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.path_le_of_start {a e :
  ForkedBeaconState preset} {c : BeaconState preset fork}
    (toC : Run config checks a ⟨fork, c⟩) (fromC : Run config checks ⟨fork, c⟩ e) (i X : ℕ)
    (before : ∀ p ∈ toC.balancePath, p = ⟨fork, c⟩ ∨ effectiveAt p i = 0)
    (after : ∀ z ∈ fromC.balancePath, effectiveAt z i ≤ X) :
    ∀ z ∈ (toC.append fromC).balancePath, effectiveAt z i ≤ X := by
  intro z member
  rw [Run.balancePath_append] at member
  rcases List.mem_append.mp member with front | later
  · rcases before z front with atC | zero
    · obtain ⟨rest, head⟩ := Run.balancePath_head fromC
      rw [atC]
      exact after _ (by rw [head]; exact List.mem_cons_self)
    · rw [zero]
      exact Nat.zero_le _
  · exact after z (List.mem_of_mem_tail later)

/-- No due entry names a key past the registry when the targets of the queue are inside it. -/
private theorem dueAt_eq_zero_of_targets (X : BeaconState preset fork) (high : ℕ)
    {v : ValidatorIndex}
    (inside : ∀ electra : .pectra ≤ fork, ∀ c ∈ (X.pendingConsolidations electra).data.toList,
      c.targetIndex.toNat < X.validators.data.size)
    (outside : X.validators.data.size ≤ v.toNat) : Internal.dueAt X high {v} = 0 := by
  unfold Internal.dueAt
  split
  · rename_i electra
    have none : (X.pendingConsolidations electra).data.toList.filter
        (fun c => decide (c.targetIndex ∈ ({v} : Finset ValidatorIndex))) = [] :=
      List.filter_eq_nil_iff.mpr fun c member => by
        have target := inside electra c member
        simp only [Finset.mem_singleton, decide_eq_true_eq]
        rintro rfl
        omega
    rw [none]
    rfl
  · rfl

/-- A key created after the split and activated by C has a deposit credit on C's run.

It holds the activation reserve at its start.

No gross block credit reaches it before its activation, so a deposit or a consolidation pays it.

A consolidation needs an entry of the finalized queue, whose target is inside that registry. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_deposit (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
      := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  by_contra none
  have depZero := Nat.eq_zero_of_not_pos none
  have finGrows : fin.validators.data.size ≤ split.validators.data.size :=
    registryGrows_of_chainSteps fromFin.chainSteps
  obtain ⟨_, pre, post, splitEq, -, -, -, -, funded, -, -, walk, noGross, -⟩ :=
    Internal.created_start h tailC highC endEpochC activated absent
  have positive := Internal.maxEffectiveBalance_pos h
  have consScan : (Internal.creditScan (fun _ => false) (fun s => decide (s = .consolidations))
    v.toNat
      highC tailC) ≤ Internal.consAmt eventsC v.toNat :=
    Internal.scan_le_events _ _ (· = .consolidations) (by intro s; simp) tailC highC v replayedC
  subst splitEq
  have depSplit := Internal.creditScan_append (fun _ => false) (fun s => decide (s = .deposits))
    v.toNat highC pre post
  have consSplit := Internal.creditScan_append (fun _ => false) (fun s => decide (s =
    .consolidations))
    v.toNat highC pre post
  have noCons := Internal.consAmt_zero h fromFin replayedF (pre.append post) highC endEpochC h.near
    replayedC v (dueAt_eq_zero_of_targets fin highC (toFin.pendingConsolidation_targets
      h.genesis h.early (Internal.Setting.delay h)) (by omega))
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C's branch holds beyond the split pays an upward band.

The deposit that creates it on C's run supplies the credit band. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.created_band (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {v : ValidatorIndex} (activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
      w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted)
    (absent : split.validators.data.size ≤ v.toNat) :
    preset.upwardBand ≤ Internal.bandC tailC highC v.toNat + Internal.bandX fin highC v.toNat := by
  have replayedF' := Internal.replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called
      h)
    replayedF
  have deposit :=
    Internal.created_deposit h fromFin replayedF' tailC highC endEpochC replayedC activated absent
  have positive : 0 < Internal.grossScan v.toNat highC tailC +
      (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) v.toNat highC tailC)
        := by
    omega
  have band : Internal.bandC tailC highC v.toNat = preset.upwardBand := by
    unfold Internal.bandC
    simp [positive]
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of `SC` that R neither slashes nor exits, and that is not active at C, is charged on C.

An exit unset at the split is set by the key's slashing on C's run, which charges it.

An exit set at the split belongs to a key activated by the split's epoch.

If R slashes the key, its withdrawal is a vector past the split, so `slashedRB` holds.

Otherwise its exit is after R's next epoch, or `exitedSlashable` counts it.

An exit after R's next epoch leaves the key active at C. -/
private theorem sc_inactive_charged (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {i : ℕ}
    (member : i ∈ (Internal.slashedOnC split counted).filter (fun i => i <
        split.validators.data.size))
    (notRB : ¬ (pinTerms config pulled anc fin).slashedRB i = true)
    (notES : ¬ PinTerms.exitedSlashable anc pulled i = true)
    (inactive : ¬ isActiveAt counted (getCurrentEpoch counted) i = true) :
    ∃ c ∈ tailC.departureCharges, c.index = i := by
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
  obtain ⟨-, unslashedS, slashedC⟩ := Finset.mem_filter.mp inSlashed
  obtain ⟨u, foundS⟩ : ∃ u, split.validators.data[i]? = some u :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  have cleanU : u.slashed = false := by simpa [foundS] using unslashedS
  obtain ⟨wc, foundC, lifeC⟩ := tailC.registryLifecycle.validators i u foundS
  have markedC : wc.slashed = true := by simpa [foundC] using slashedC
  by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
  · have assigned : wc.exitEpoch ≠ FAR_FUTURE_EPOCH :=
      run_slashed_exit_assigned ((toFin.append fromFin).append tailC) h.genesis
        h.caps.activation h.caps.compounding h.early (Internal.Setting.delay h) i wc foundC markedC
    obtain ⟨c, inRun, index, -⟩ :=
      tailC.departure_charge_of_assigned i u wc foundS foundC unset assigned
    exact ⟨c, inRun, index⟩
  exfalso
  obtain ⟨w, foundP, lifeP⟩ := tail.registryLifecycle.validators i u foundS
  have exitP : w.exitEpoch = u.exitEpoch := lifeP.exitEpoch unset
  have exitC : wc.exitEpoch = u.exitEpoch := lifeC.exitEpoch unset
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have belowS := getCurrentEpoch_succ_lt_farFuture h.twoSlots split
  have activated : u.activationEpoch.toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp ((toFin.append fromFin).exit_activated h.genesis i u foundS unset)
  have actAssigned : u.activationEpoch ≠ FAR_FUTURE_EPOCH := fun same => by
    rw [same] at activated
    omega
  have actC : wc.activationEpoch = u.activationEpoch := lifeC.activationEpoch actAssigned
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  cases slashedP : w.slashed
  · by_cases early : u.exitEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1
    · -- R keeps the key unslashed and exits it by its next epoch, so `exitedSlashable` counts it
      apply notES
      have delayS := (toFin.append fromFin).withdrawable_eq_exit_delay h.genesis i u foundS cleanU
      have delayP := ((toFin.append fromFin).append tail).withdrawable_eq_exit_delay h.genesis i w
        foundP slashedP
      have unassigned : u.exitEpoch.toNat ≠ 2 ^ 64 - 1 := fun same =>
        unset (UInt64.toNat_inj.mp (by rw [same, far]))
      have positive := (Internal.Setting.delay h)
      have openS : (getCurrentEpoch split).toNat < u.withdrawableEpoch.toNat := by
        by_cases exited : u.exitEpoch ≤ getCurrentEpoch split
        · exact UInt64.lt_iff_toNat_lt.mp (tailC.newly_slashed_initial_exited_unwithdrawable
            h.caps.activation h.caps.compounding h.early i u wc foundS foundC cleanU markedC exited)
        · have later := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp exited)
          rcases delayS with ⟨same, -⟩ | same
          · exact absurd same unset
          · omega
      have wdP : w.withdrawableEpoch.toNat = u.withdrawableEpoch.toNat := by
        rcases delayS with ⟨same, -⟩ | eqS
        · exact absurd same unset
        rcases delayP with ⟨same, -⟩ | eqP
        · exact absurd (exitP ▸ same) unset
        rw [eqS, eqP, exitP]
      unfold PinTerms.exitedSlashable
      simp only [foundP, Option.map_some, Option.getD_some, slashedP, Option.any_some, exitP,
        decide_eq_true_eq, true_and]
      omega
    · -- its exit is after R's next epoch, so it is active at C
      apply inactive
      have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
      refine isActiveAt_eq_true_iff.mpr ⟨wc, foundC, ?_⟩
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rw [actC]
        exact UInt64.le_iff_toNat_le.mpr (by simp only at splitC; omega)
      · rw [exitC]
        exact UInt64.lt_iff_toNat_lt.mpr (by omega)
  · -- R slashes the key after the split, so its withdrawal is a vector past the split
    exact notRB (Internal.slashedRB_of_newly_slashed h foundS foundP cleanU slashedP)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key absent or unslashed at the finalized state is bounded from there or its creation.

A key already in the split's registry needs its slashing withdrawal bound.

A later key gets that bound from the state that first holds it. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.envelope_of_clean_fin (h : Setting
  config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (replayed : tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (inside : v.toNat < pulled.validators.data.size)
    (cleanFin : ∀ u, fin.validators.data[v.toNat]? = some u → u.slashed = false)
    (slashedLateSplit : v.toNat < split.validators.data.size →
      ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
        anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat)
    (late : ∀ w, pulled.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat) :
    ∀ z ∈ (fromFin.append tail).balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat + preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((Internal.syncD eventsF v.toNat + Internal.syncD events v.toNat +
            Internal.slashW (pinTerms config pulled anc fin) v.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  intro z inPath
  by_cases inFin : v.toNat < fin.validators.data.size
  · have splitSize : v.toNat < split.validators.data.size :=
      Nat.lt_of_lt_of_le inFin (registryGrows_of_chainSteps fromFin.chainSteps)
    exact Internal.envelope_of_voter h fromFin tail replayedF replayed v
      (Run.nil : Run config checks ⟨fork, fin⟩ ⟨fork, fin⟩) (fromFin.append tail)
      (Run.nil_append (fromFin.append tail)) cleanFin (slashedLateSplit splitSize) inFin
      (Or.inl ⟨Internal.effective_fin_le_ebUp h v.toNat, Nat.le_refl _⟩) (fun w fw clean' =>
        Internal.late_of_withdrawable h fromFin tail v.toNat w fw clean' (late w fw)) z inPath
  · obtain ⟨c, toC, fromC, cutC, insideC, clean, before, floorStart, firstAfter⟩ :=
      Internal.created_first_state h (fromFin.append tail) (by omega) inside
    have slashedLate : ∀ w, pulled.validators.data[v.toNat]? = some w → w.slashed = true →
        anc.finalizedCheckpoint.epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat ≤
          w.withdrawableEpoch.toNat := by
      by_cases inSplit : v.toNat < split.validators.data.size
      · exact slashedLateSplit inSplit
      · have after := firstAfter split fromFin tail rfl inSplit
        have finalizedNat := UInt64.le_iff_toNat_le.mp h.finalized
        exact Internal.slashed_withdrawable_of_clean h fromC v clean insideC
          (UInt64.le_iff_toNat_le.mpr (by omega))
    have envC := Internal.envelope_of_voter h fromFin tail replayedF replayed v toC fromC cutC clean
      slashedLate insideC (Or.inr floorStart) (fun w fw clean' =>
        Internal.late_of_withdrawable h fromFin tail v.toNat w fw clean' (late w fw))
    rw [← cutC] at inPath
    exact Internal.path_le_of_start toC fromC v.toNat _ before envC z inPath

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The replays of the branch from `fin` to the split and of R's run, read at R's epoch.

Both runs end by R's epoch, so the horizon of the replay does not change their events. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.replays_at_pulled
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF) :
    fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF ∧
      tail.balanceEvents (getCurrentEpoch pulled).toNat = .ok events :=
  ⟨Internal.replay_at_pulled pulled fromFin high endEpoch (currentEpoch_le_of_chainSteps
      tail.chainSteps)
      replayedF,
    Internal.replay_at_pulled pulled tail high endEpoch (UInt64.le_refl _) replayed⟩

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key of the split's registry, unslashed there, induces a leak on R's run only with a debit.

Its envelope on R's run is `ebUp` with its debits and its penalty in whole increments.

The penalty is below an increment.

So a key without a sync debit stays within `ebUp`, and induces no leak. -/
private theorem induced_debited (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {i : ℕ} (inside : i < split.validators.data.size)
    (unslashed : (split.validators.data[i]?.map (·.slashed)).getD false = false)
    (positive : 0 < Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i) :
    0 < Internal.syncD eventsF i + Internal.syncD events i := by
  obtain ⟨replayedF', replayed'⟩ :=
    Internal.replays_at_pulled tail high endEpoch replayed fromFin replayedF
  by_contra none
  have zero : Internal.syncD eventsF i + Internal.syncD events i = 0 := by omega
  by_cases late : ∀ w, pulled.validators.data[i]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.withdrawableEpoch.toNat
  swap
  · obtain ⟨w, found, notLate⟩ : ∃ w, pulled.validators.data[i]? = some w ∧
        w.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
      by_contra no
      exact late fun w found => by
        by_contra notLate
        exact no ⟨w, found, by omega⟩
    rw [Internal.inducedR_of_withdrawn _ _ _ (Internal.withdrawnRB_of_le config pulled anc fin found
      notLate)]
      at positive
    exact Nat.lt_irrefl 0 positive
  have below := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split)
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  have cleanSplit : ∀ u, split.validators.data[v.toNat]? = some u → u.slashed = false :=
    fun u foundU => by
      rw [foundU] at unslashed
      simpa using unslashed
  have envelope := Internal.envelope_of_clean_fin h fromFin tail replayedF' replayed' v
    (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tail.chainSteps))
    (fun u foundU => Internal.unslashed_of_run fromFin foundU cleanSplit)
    (fun splitSize => Internal.slashed_withdrawable_of_clean h tail v cleanSplit splitSize
      h.finalized) late
  have hWdb := Internal.slashW_add_downwardBand_le h v.toNat
  have bandLow := h.facts.bandLow
  have incBig := h.facts.incrementSize
  have hW : Internal.slashW (pinTerms config pulled anc fin) v.toNat <
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by omega
  have perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement := by
    have := Internal.four_le_perIncrement h
    omega
  have bound := Internal.inducedR_le config pulled anc fin h.bands.1 perPos (fromFin.append tail)
    v.toNat
    0 0 (Nat.zero_le _) fun z inPath => by
      have within := envelope z inPath
      rw [zero, Nat.zero_add, Nat.div_eq_of_lt hW] at within
      simpa using within
  simp at bound
  omega

/-- Pre-slashing deposits are bounded by all deposits in the replay. -/
private theorem depPre_le_deposits (L : List (BalanceEvent preset)) (i : ℕ) :
    Internal.depPre L i ≤ ((L.filter fun e => e.source = .deposits).map (Internal.keyCredit i)).sum
      := by
  induction L with
  | nil => simp [Internal.depPre]
  | cons e rest ih =>
    unfold Internal.depPre at ih ⊢
    by_cases dep : e.source = .deposits
    · by_cases slashed : slashedFlagAt e.before.state i = some true <;>
        simp [dep, slashed] at ih ⊢ <;> omega
    · simp [dep] at ih ⊢
      omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key credited by a consolidation from the split, or on the shared segment, has a due entry.

The entry is in the queue of the finalized state, so the key has its band. -/
private theorem band_of_consolidation (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    {ending : BeaconState preset fork}
    (run : Run config checks ⟨fork, split⟩ ⟨fork, ending⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch ending).toNat ≤ high + 1)
    (near : (getCurrentEpoch ending).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {events : List (BalanceEvent preset)} (replayed : run.balanceEvents high = .ok events)
    {i : ℕ} (small : i < 2 ^ 64) (credited : 0 < Internal.consAmt eventsF i + Internal.consAmt
      events i) :
    preset.upwardBand ≤ Internal.bandX fin high i := by
  by_contra low
  have none : Internal.dueAt fin high {(UInt64.ofNat i : ValidatorIndex)} = 0 := by
    unfold Internal.bandX at low
    by_contra pos
    exact low (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero pos))
  have zero := Internal.consAmt_zero h fromFin replayedF run high endEpoch near replayed _ none
  rw [UInt64.toNat_ofNat_of_lt' small] at zero
  omega

/-- Ten quotients times three ceilings of a slack are zero, or within thirty slacks and quotients.
-/
private theorem ceil_round (X Q : ℕ) (pos : 0 < Q) :
    10 * Q * (3 * ((X + Q - 1) / Q)) = 0 ∨
      (0 < X ∧ 10 * Q * (3 * ((X + Q - 1) / Q)) ≤ 30 * X + 30 * Q - 30) := by
  rcases Nat.eq_zero_or_pos X with rfl | positive
  · left
    rw [Nat.zero_add, Nat.div_eq_of_lt (by omega)]
    simp
  · right
    refine ⟨positive, ?_⟩
    have floor := Nat.div_mul_le_self (X + Q - 1) Q
    have e : 10 * Q * (3 * ((X + Q - 1) / Q)) = 30 * ((X + Q - 1) / Q * Q) := by ring
    rw [e]
    omega

/-- Thirty-three of an amount is within ten quotients of its share. -/
private theorem share_ge (pos : 0 < (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
    (x : ℕ) :
    33 * x ≤ 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat *
      Internal.wShare preset fork x := by
  unfold Internal.wShare
  generalize (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat = Q at pos ⊢
  exact le_smul_ceilDiv (β := Nat) (show 0 < 10 * Q by omega)

/-- A key's credits on C's run have their gross scan and their credit or consolidation band. -/
private theorem credit_band_bounds (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) {eventsF : List (BalanceEvent preset)}
    (replayedF : fromFin.balanceEvents (getCurrentEpoch pulled).toNat = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {i : ℕ} (small : i < 2 ^ 64) :
    Internal.propN tailC highC i ≤ Internal.grossScan i highC tailC ∧
      Internal.whistC tailC highC i ≤ Internal.grossScan i highC tailC ∧
      (Internal.syncCr eventsC i = 0 ∨ 0 < Internal.grossScan i highC tailC) ∧
      ((0 < Internal.grossScan i highC tailC + (Internal.creditScan (fun _ => false)
          (fun s => decide (s = .deposits)) i highC tailC) ∧
          Internal.bandC tailC highC i = preset.upwardBand) ∨
        (Internal.grossScan i highC tailC + (Internal.creditScan (fun _ => false)
          (fun s => decide (s = .deposits)) i highC tailC) = 0 ∧ Internal.bandC tailC highC i = 0))
            ∧
      (Internal.consAmt eventsC i = 0 ∨ preset.upwardBand ≤ Internal.bandX fin highC i) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Internal.scan_le_gross tailC highC i (fun s => decide (s = .rewards))
      fun s h => by simp at h; simp [h]
  · exact Internal.scan_le_gross tailC highC i (fun s => decide (s = .slashings))
      fun s h => by simp at h; simp [h]
  · rcases Nat.eq_zero_or_pos (Internal.syncCr eventsC i) with none | positive
    · exact .inl none
    · exact .inr (Internal.syncCr_gross (Nat.le_trans (by decide) h.fulu) h.early tailC highC
      replayedC i
        positive)
  · unfold Internal.bandC
    split_ifs <;> omega
  · rcases Nat.eq_zero_or_pos (Internal.consAmt eventsC i) with none | positive
    · exact .inl none
    · exact .inr (band_of_consolidation h fromFin replayedF tailC highC endEpochC h.near replayedC
        small (by omega))

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The rounding of one key of `SC` is within its shares and bands, at ten quotients.

The slack's credits pay at eleven tenths of three, the shares' rate.

Each source of the key's slack brings a band, which pays the rounding of its floor. -/
private theorem sc_key_round (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    (eventsP : List (BalanceEvent preset)) (Q : ℕ)
    (hQ : Q = (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) {i : ℕ}
    (member : i ∈ (Internal.slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)) :
    10 * Q * (3 * ((Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append
      tail) highC
        high eventsC eventsF events fin i +
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          + Q - 1) / Q)) ≤
      33 * Internal.propN tailC highC i + 33 * Internal.depPre eventsC i + 33 * Internal.syncCr
        eventsC i +
        33 * Internal.consAmt eventsC i + 33 * Internal.syncD eventsF i + 33 * Internal.syncD events
          i +
        30 * (Q * Internal.whistC tailC highC i) + 10 * (Q * Internal.bandC tailC highC i) +
        10 * (Q * Internal.bandX fin highC i) +
        33 * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.syncCr eventsF i else 0) +
        33 * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.consAmt eventsF i else 0) +
        10 * (Q * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.bandX fin high i else 0)) +
        10 * (Q * (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events
          eventsF i +
          Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
          Internal.bandR (eventsF ++ events) i +
          if (pinTerms config pulled anc fin).exitBeforeFin i = true then
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0)) +
        33 * Internal.propN pre highC i + 10 * (Q * Internal.syncCr eventsP i) +
        30 * (Q * (if ∃ c ∈ tailC.departureCharges, c.index = i then Internal.whistC pre highC i
          else 0)) +
        10 * (Q * (if ∃ c ∈ tailC.departureCharges, c.index = i then
          (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
            i then
            preset.upwardBand else 0) else 0)) := by
  have quotient : 30 ≤ Q := hQ ▸ h.facts.whistleblower fork
  have up := h.bands.2
  have incBig := h.facts.incrementSize
  have unit : 4 ≤ (pinTerms config pulled anc fin).unitGain := by
    have finalized := UInt64.le_iff_toNat_le.mp h.finalized
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have depth : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    have unitEq : (pinTerms config pulled anc fin).unitGain =
        (pinTerms config pulled anc fin).depth * ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) := rfl
    have product := Nat.mul_le_mul (show 2 ≤ (pinTerms config pulled anc fin).depth by omega)
      (Nat.le_add_left 2 ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat))
    omega
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨inSlashed, inside⟩ := Finset.mem_filter.mp member
  obtain ⟨-, unslashedS, -⟩ := Finset.mem_filter.mp inSlashed
  have small := inside.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early split)
  have replayedF' := Internal.replay_at_pulled pulled fromFin high endEpoch (Internal.Setting.called
      h)
    replayedF
  -- the credits that the slack reads, and the bands that they bring
  obtain ⟨grossP, grossW, grossS, hbC, consBand⟩ :=
    credit_band_bounds h fromFin replayedF' tailC highC endEpochC replayedC small
  obtain ⟨-, credits⟩ := Internal.creditScan_bounds ∅ UInt64.toNat (fun _ => false)
    (fun s => decide (s = .deposits)) highC (fun _ => 0) tailC replayedC (fun e _ _ => by simp)
  have dep := credits (fun s => decide (s = .deposits))
    (Or.inr fun electra early replayed i => Internal.block_deposit_zero electra early
      replayed i)
    (Or.inl fun _ covered => covered) electra h.early i
  have deposits := (depPre_le_deposits eventsC i).trans dep
  have bandXZero : ∀ hh, Internal.bandX fin hh i = 0 ∨ preset.upwardBand ≤ Internal.bandX fin hh i
    := by
    intro hh
    unfold Internal.bandX
    rcases Nat.eq_zero_or_pos (Internal.dueAt fin hh {(UInt64.ofNat i : ValidatorIndex)}) with zero
      | pos
    · exact .inl (by rw [zero, Nat.mul_zero])
    · exact .inr (Nat.le_mul_of_pos_right _ pos)
  have hbX : (Internal.bandX fin highC i = 0 ∧ Internal.consAmt eventsC i = 0) ∨
      preset.upwardBand ≤ Internal.bandX fin highC i := by
    rcases bandXZero highC with zero | big
    · rcases consBand with none | big
      · exact .inl ⟨zero, none⟩
      · exact .inr big
    · exact .inr big
  have hbXh : (Internal.bandX fin high i = 0 ∧ Internal.consAmt eventsF i = 0) ∨
      preset.upwardBand ≤ Internal.bandX fin high i := by
    rcases bandXZero high with zero | big
    · rcases Nat.eq_zero_or_pos (Internal.consAmt eventsF i) with none | pos
      · exact .inl ⟨zero, none⟩
      · exact .inr (band_of_consolidation h fromFin replayedF' tail high endEpoch (by omega)
          replayed small (by omega))
    · exact .inr big
  have hbR : (Internal.syncD eventsF i + Internal.syncD events i = 0 ∧ Internal.bandR (eventsF ++
    events) i = 0 ∧
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i = 0) ∨
      Internal.bandR (eventsF ++ events) i =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat + preset.downwardBand - 1 := by
    have induced : Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i = 0 ∨
        0 < Internal.syncD eventsF i + Internal.syncD events i := by
      rcases Nat.eq_zero_or_pos
          (Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i) with zero |
            pos
      · exact .inl zero
      · exact .inr (induced_debited h tail high endEpoch replayed fromFin replayedF inside
          unslashedS pos)
    rw [Internal.bandR_eq]
    simp only [List.map_append, List.sum_append]
    unfold Internal.syncD at induced ⊢
    split_ifs <;> omega
  have huK : (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i =
    0 ∧
        (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
          (pinTerms config pulled anc fin).unitGain else 0) = 0) ∨
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i =
        (pinTerms config pulled anc fin).unitGain := by
    unfold Internal.unitK Internal.flowCredit
    split_ifs <;> omega
  have hSW : (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0) ≤
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i := by
    unfold Internal.unitK Internal.flowCredit
    split_ifs <;> omega
  have huSF : (Internal.syncCr eventsF i = 0 ∧
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) = 0) ∨
      (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) = preset.upwardBand := by
    split_ifs <;> omega
  have hb5 : (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i =
    0 ∧
        (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
          then
          preset.upwardBand else 0) = 0) ∨
      (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
        then
        preset.upwardBand else 0) = preset.upwardBand := by
    split_ifs <;> omega
  -- the terms of a key that exited by the finalized state
  have hE : ((if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.syncCr eventsF i else 0) = Internal.syncCr eventsF i ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.consAmt eventsF i else 0) = Internal.consAmt eventsF i ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.bandX fin high i else 0) = Internal.bandX fin high i ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) =
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
            fin high i +
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) =
          (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
            fin high i +
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0)) ∨
      ((if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.syncCr eventsF i else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.consAmt eventsF i else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          Internal.bandX fin high i else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) = 0 ∧
        (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
            fin high i +
            (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) = 0) := by
    by_cases e : (pinTerms config pulled anc fin).exitBeforeFin i = true
    · left
      simp only [e, ↓reduceIte, and_self]
    · right
      simp only [e, Bool.false_eq_true, ↓reduceIte, and_self]
  -- the terms of a key not active at C that R neither slashes nor exits, which is charged
  have hD : ((if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          =
          Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i ∧
        (if ∃ c ∈ tailC.departureCharges, c.index = i then Internal.whistC pre highC i else 0) =
          Internal.whistC pre highC i ∧
        (if ∃ c ∈ tailC.departureCharges, c.index = i then
          (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
            i then
            preset.upwardBand else 0) else 0) =
          (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
            i then
            preset.upwardBand else 0)) ∨
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          = 0 := by
    by_cases d : ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true ∧
        ¬ isActiveAt counted (getCurrentEpoch counted) i = true
    · have charged := sc_inactive_charged h fromFin tail tailC member d.1 d.2.1 d.2.2
      exact .inl ⟨ite_eq_left d, ite_eq_left charged, ite_eq_left charged⟩
    · exact .inr (ite_eq_right d)
  -- the products by the quotient
  have pWT := Nat.mul_le_mul_right (Internal.whistC tailC highC i) (show 2 ≤ Q by omega)
  have pSP := Nat.mul_le_mul_right (Internal.syncCr eventsP i) (show 3 ≤ Q by omega)
  have pWP := Nat.mul_le_mul_right
    (if ∃ c ∈ tailC.departureCharges, c.index = i then Internal.whistC pre highC i else 0)
    (show 3 ≤ Q by omega)
  obtain ⟨SB, hSB⟩ : ∃ SB, SB = Internal.bandC tailC highC i + Internal.bandX fin highC i +
      (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
        Internal.bandR (eventsF ++ events) i +
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      (if (pinTerms config pulled anc fin).exitBeforeFin i = true then Internal.bandX fin high i
        else 0) +
      (if ∃ c ∈ tailC.departureCharges, c.index = i then
        (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
          then
          preset.upwardBand else 0) else 0) := ⟨_, rfl⟩
  have hQSB : Q * Internal.bandC tailC highC i + Q * Internal.bandX fin highC i +
      Q * (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
        Internal.bandR (eventsF ++ events) i +
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      Q * (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        Internal.bandX fin high i else 0) +
      Q * (if ∃ c ∈ tailC.departureCharges, c.index = i then
        (if 0 < Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i
          then
          preset.upwardBand else 0) else 0) = Q * SB := by
    rw [hSB]
    ring
  have pSB := Nat.mul_le_mul_right SB quotient
  -- the slack is zero, or it has a band of at least four
  have hc := ceil_round (Internal.whistleSlack (pinTerms config pulled anc fin) tailC
    (fromFin.append tail)
    highC high eventsC eventsF events fin i +
    (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true ∧
        ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
      Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0))
        Q (by omega)
  unfold Internal.whistleSlack Internal.whistleSlackBase at hc ⊢
  have big : (11 * (Internal.propN tailC highC i + Internal.depPre eventsC i + Internal.whistC tailC
    highC i +
        Internal.syncCr eventsC i + Internal.consAmt eventsC i + Internal.syncD eventsF i +
          Internal.syncD events i) + 9) / 10 +
      Internal.bandC tailC highC i + Internal.bandX fin highC i + Internal.bandR (eventsF ++ events)
        i +
      Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0) +
      (if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (11 * (Internal.syncCr eventsF i + Internal.consAmt eventsF i) + 9) / 10 + Internal.bandX
          fin high i +
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          = 0 ∨ 4 ≤ SB := by
    omega
  rcases big with zero | four
  · omega
  · have pFour := Nat.mul_le_mul_left Q four
    omega

/-- The slack and the rounding of the rewards of the keys of `SC` are paid by their shares.

A key of the split's registry is read at its bound and the slack that `registry` adds.

A key that exits on C's branch is read at its charge and its rise after it.

The slashing credits of the slack are the keys' own.

The aggregate reward bound subtracts those credits.

The unit, the induced leak and the bands of the slack are paid unscaled.

Its credits are paid by the shares, with a tenth for their gains.

Each credited key has an upward band, which pays the rounding of its floor. -/
private theorem whistle_slack_sc (h : Setting config checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork}
    (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩) (eventsP : List (BalanceEvent preset)) :
    3 * (∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)),
        min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      3 * (∑ i ∈ ((Internal.slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter
          (fun i => (pinTerms config pulled anc fin).slashedRB i = true),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        ∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter
          (fun i => PinTerms.exitedSlashable anc pulled i = true),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        ∑ i ∈ ((((Internal.slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter
            (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
              ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
            (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).filter
            (fun i => ¬ ((pinTerms config pulled anc fin).tight = false ∧
              ((pinTerms config pulled anc fin).lateB i = true ∨
                (pinTerms config pulled anc fin).pendingRB i = true))),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        ∑ i ∈ ((((Internal.slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter
            (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
              ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
            (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).filter
            (fun i => (pinTerms config pulled anc fin).tight = false ∧
              ((pinTerms config pulled anc fin).lateB i = true ∨
                (pinTerms config pulled anc fin).pendingRB i = true)),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        3 * (∑ i ∈ (((Internal.slashedOnC split counted).filter
            (fun i => i < split.validators.data.size)).filter
            (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
              ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
            (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true),
          (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) /
            (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        3 * (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i <
            split.validators.data.size),
          Internal.whistC tailC highC i) +
        (Internal.wShare preset fork ((∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC
          highC v.toNat) +
            ∑ v ∈ Internal.SC pulled counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr
            eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt
            eventsC v.toNat) +
          Internal.wShare preset fork
            (∑ v ∈ Internal.SC pulled counted split, (Internal.syncD eventsF v.toNat +
              Internal.syncD events v.toNat)) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandX fin highC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.syncCr eventsF
              v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              Internal.consAmt eventsF v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              Internal.bandX fin high v.toNat) : ℕ) +
        (∑ v ∈ Internal.SC pulled counted split,
          (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF
            v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
            Internal.bandR (eventsF ++ events) v.toNat +
            if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
              (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) : ℕ) +
        Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre
          highC v.toNat) +
        (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsP v.toNat) +
        3 * (∑ v ∈ Internal.scCharged pulled counted split tailC, Internal.whistC pre highC v.toNat)
          +
        (∑ v ∈ Internal.scCharged pulled counted split tailC,
          if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
            Internal.syncCr eventsP v.toNat then
            preset.upwardBand else 0) := by
  have quotient := h.facts.whistleblower fork
  have pos : 0 < (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by omega
  -- each key is read at its group's bound, with the ceiling of its slack
  obtain ⟨base, hbase⟩ : ∃ base : ℕ → ℕ, ∀ i, base i =
      if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
      else Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℕ, ∀ i, X i =
      Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC high
        eventsC
        eventsF events fin i +
      (if ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true ∧
          ¬ isActiveAt counted (getCurrentEpoch counted) i = true then
        Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i else 0)
          := ⟨_, fun _ => rfl⟩
  have floorKey : ∀ i ∈ (Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size),
      3 * (min (whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      3 * base i + 3 * ((X i + (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) /
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
    intro i member
    rw [hbase, hX]
    by_cases hD : ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true ∧
        ¬ isActiveAt counted (getCurrentEpoch counted) i = true
    · -- the key is charged, and read at its charge
      obtain ⟨c, inRun, index⟩ := sc_inactive_charged h fromFin tail tailC member hD.1 hD.2.1 hD.2.2
      have any : (tailC.departureCharges.any fun c => c.index == i) = true :=
        List.any_eq_true.mpr ⟨c, inRun, by simp [index]⟩
      have read : whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i ≤
          (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) +
            (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail)
              highC high
              eventsC eventsF events fin i +
              (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP
                i)) := by
        unfold whistleRead
        rw [ite_eq_left ⟨hD.2.2, any⟩]
        exact (min_le_right _ _).trans (by omega)
      rw [ite_eq_left hD, ite_eq_left hD]
      have down := Nat.div_le_div_right
        (c := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
        ((min_le_left _ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat).trans read)
      have split := floor_add_ceil_le (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i)
        (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
          high
          eventsC eventsF events fin i +
          (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i)) _
            pos
      omega
    · -- the key is read at its bound and its slack
      have read : whistleRead (pinTerms config pulled anc fin) pulled anc counted tailC
          (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin i ≤
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i := by
        unfold whistleRead
        split
        · exact min_le_left _ _
        · exact le_rfl
      rw [ite_eq_right hD, ite_eq_right hD, Nat.add_zero]
      have down := Nat.div_le_div_right
        (c := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
        ((min_le_left _ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat).trans read)
      have split := floor_add_ceil_le (Internal.whistleEnv (pinTerms config pulled anc fin) pulled
        anc fin i)
        (Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
          high
          eventsC eventsF events fin i) _ pos
      omega
  have floors := Finset.sum_le_sum floorKey
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum] at floors
  -- the bounds of the keys are the sums of the groups
  have apart : ∀ i ∈ (Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size),
      (pinTerms config pulled anc fin).slashedRB i = true →
        ¬ PinTerms.exitedSlashable anc pulled i = true := by
    intro i _ rb es
    rw [Internal.slashedRB_eq] at rb
    unfold PinTerms.exitedSlashable at es
    cases f : pulled.validators.data[i]? with
    | none => simp [f] at rb
    | some w => simp [f] at rb es; simp [rb.1] at es
  have splitThree : ∀ (S : Finset ℕ) (p q : ℕ → Prop) [DecidablePred p] [DecidablePred q],
      (∀ i ∈ S, p i → ¬ q i) → ∀ f : ℕ → ℕ, ∑ i ∈ S, f i = ∑ i ∈ S.filter p, f i +
        ∑ i ∈ S.filter q, f i + ∑ i ∈ S.filter (fun i => ¬ p i ∧ ¬ q i), f i := by
    intro S p q _ _ disjoint f
    rw [← Finset.sum_filter_add_sum_filter_not S p, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => ¬ p i)) q, Finset.filter_filter,
      Finset.filter_filter]
    congr 1
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, -, hq⟩
      exact ⟨hi, hq⟩
    · rintro ⟨hi, hq⟩
      exact ⟨hi, fun hp => disjoint i hi hp hq, hq⟩
  have three := splitThree
    ((Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size))
    (fun i => (pinTerms config pulled anc fin).slashedRB i = true)
    (fun i => PinTerms.exitedSlashable anc pulled i = true) apart base
  have g1 : ∑ i ∈ ((Internal.slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => (pinTerms config pulled anc fin).slashedRB i = true), base i =
      ∑ i ∈ ((Internal.slashedOnC split counted).filter
        (fun i => i < split.validators.data.size)).filter
          (fun i => (pinTerms config pulled anc fin).slashedRB i = true),
        Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun i m => by
      rw [hbase, ite_eq_right fun hD => hD.1 (Finset.mem_filter.mp m).2]
  have g2 : ∑ i ∈ ((Internal.slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => PinTerms.exitedSlashable anc pulled i = true), base i =
      ∑ i ∈ ((Internal.slashedOnC split counted).filter
        (fun i => i < split.validators.data.size)).filter
          (fun i => PinTerms.exitedSlashable anc pulled i = true),
        Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    Finset.sum_congr rfl fun i m => by
      rw [hbase, ite_eq_right fun hD => hD.2.1 (Finset.mem_filter.mp m).2]
  have y := (Finset.sum_filter_add_sum_filter_not (((Internal.slashedOnC split counted).filter
    (fun i => i < split.validators.data.size)).filter
      (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true) base).symm
  have g3 := Finset.sum_congr rfl fun i (m : i ∈ (((Internal.slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
      (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)) => show base i =
        Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat by
      rw [hbase, ite_eq_right fun hD => hD.2.2 (Finset.mem_filter.mp m).2]
  have g4 := Finset.sum_congr rfl fun i (m : i ∈ (((Internal.slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)).filter
        (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
          ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
      (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true)) => show base i =
        (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat by
      obtain ⟨inY, inactive⟩ := Finset.mem_filter.mp m
      obtain ⟨-, both⟩ := Finset.mem_filter.mp inY
      rw [hbase, ite_eq_left ⟨both.1, both.2, inactive⟩]
  have g5 := (Finset.sum_filter_add_sum_filter_not ((((Internal.slashedOnC split counted).filter
    (fun i => i < split.validators.data.size)).filter
      (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
        ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
      (fun i => isActiveAt counted (getCurrentEpoch counted) i = true))
    (fun i => (pinTerms config pulled anc fin).tight = false ∧
      ((pinTerms config pulled anc fin).lateB i = true ∨
        (pinTerms config pulled anc fin).pendingRB i = true))
    (fun i => Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)).symm
  have part := congrArg
    (fun x => 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat * (3 * x))
    ((three.trans (by rw [g1, g2, y, g3, g4, g5])) : _ = _)
  -- the rounding of the keys is within the shares and bands
  have rounds := Finset.sum_le_sum fun i (m : i ∈ (Internal.slashedOnC split counted).filter
      (fun i => i < split.validators.data.size)) => by
    have one := sc_key_round h tail high endEpoch replayed fromFin replayedF tailC highC endEpochC
      replayedC pre eventsP _ rfl m
    rw [← hX i] at one
    exact one
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at rounds
  -- the sums over `SC` are sums over the positions
  have fEBF (f : ℕ → ℕ) : ∑ v ∈ Internal.SC pulled counted split with
      (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, f v.toNat =
      ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then f i else 0 :=
    (sum_SC_filter_positions h (fun i => (pinTerms config pulled anc fin).exitBeforeFin i = true)
      f).trans (Finset.sum_filter _ _)
  have fCharged (f : ℕ → ℕ) : ∑ v ∈ Internal.scCharged pulled counted split tailC, f v.toNat =
      ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
        if ∃ c ∈ tailC.departureCharges, c.index = i then f i else 0 :=
    (sum_SC_filter_positions h (fun i => ∃ c ∈ tailC.departureCharges, c.index = i) f).trans
      (Finset.sum_filter _ _)
  rw [fEBF (fun i => Internal.syncCr eventsF i), fEBF (fun i => Internal.consAmt eventsF i),
    fEBF (fun i => Internal.bandX fin high i), fCharged (fun i => Internal.whistC pre highC i),
    fCharged (fun i => if 0 < Internal.propN pre highC i + Internal.whistC pre highC i +
      Internal.syncCr eventsP i then
      preset.upwardBand else 0),
    sum_SC_positions h (fun i => Internal.propN tailC highC i),
    sum_SC_positions h (fun i => Internal.depPre eventsC i),
    sum_SC_positions h (fun i => Internal.syncCr eventsC i), sum_SC_positions h (fun i =>
      Internal.consAmt eventsC i),
    sum_SC_positions h (fun i => Internal.syncD eventsF i + Internal.syncD events i),
    sum_SC_positions h (fun i => Internal.bandC tailC highC i),
    sum_SC_positions h (fun i => Internal.bandX fin highC i),
    sum_SC_positions h (fun i => Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC
      events
      eventsF i + Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      Internal.bandR (eventsF ++ events) i + if (pinTerms config pulled anc fin).exitBeforeFin i =
        true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0),
    sum_SC_positions h (fun i => Internal.propN pre highC i), sum_SC_positions h (fun i =>
      Internal.syncCr eventsP i)]
  simp only [Finset.sum_add_distrib]
  refine Nat.le_of_mul_le_mul_left
    (c := 10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ?_ (by omega)
  have scaled := Nat.mul_le_mul_left
    (10 * (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) floors
  have s1 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.propN tailC highC i +
    ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.depPre eventsC i)
  have s2 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.syncCr eventsC i)
  have s3 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.consAmt eventsC i)
  have s4 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.syncD eventsF i +
    ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.syncD events i)
  have s5 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then Internal.syncCr eventsF i else
        0)
  have s6 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then Internal.consAmt eventsF i
        else 0)
  have s7 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size),
      Internal.propN pre highC i)
  linarith

/-- The largest representable epoch is reserved for keys without an assigned exit. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.exitEpoch_toNat_lt_of_ne_far {epoch
  : Epoch} (assigned : epoch ≠ FAR_FUTURE_EPOCH) :
    epoch.toNat < 2 ^ 64 - 1 := by
  have bound := epoch.toNat_lt
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have ne := mt UInt64.toNat_inj.mp assigned
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- A key that C's run creates and slashes is credited its proposer credits and consolidations.

It is also credited its deposits before its exit.

The run charges the key at the step that sets its exit, and its deposits stop there.

The key is unslashed before that step, since a slashed key has its exit set.

The consolidation credits that the run scans are among those of its events. -/
private theorem created_credC_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {i : ℕ} (created : ¬ i < split.validators.data.size)
    (slashedC : (counted.validators.data[i]?.map (·.slashed)).getD false = true) :
    Internal.credC tailC highC i ≤ Internal.propN tailC highC i + Internal.depPre eventsC i +
      Internal.consAmt eventsC i := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨wc, foundC⟩ : ∃ wc, counted.validators.data[i]? = some wc := by
    cases f : counted.validators.data[i]? with
    | none => simp [f] at slashedC
    | some w => exact ⟨w, rfl⟩
  have markedC : wc.slashed = true := by simpa [foundC] using slashedC
  have assignedC := run_slashed_exit_assigned ((shared.append fromFin).append tailC) h.genesis
    h.caps.activation h.caps.compounding h.early (Internal.Setting.delay h) i wc foundC markedC
  obtain ⟨c, inRun, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early i
    (fun v found => absurd (Array.getElem?_eq_some_iff.mp found).1 created) wc foundC assignedC
  have late := DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c inRun
  simp only at late
  obtain ⟨a, b, pre, step, post, site, u, w, foundA, foundB, unset, set, -, epochW⟩ :=
    tailC.departure_charge_site c inRun
  rw [index] at foundA foundB
  subst site
  have aFork : a.fork = fork :=
    Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  have aEarly : a.fork < .glamsterdam := by rw [aFork]; exact h.early
  have aFulu : .fusaka ≤ a.fork := by rw [aFork]; exact h.fulu
  have aEpoch : (getCurrentEpoch a.state).toNat ≤ highC + 1 :=
    Nat.le_trans (UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
      ((Run.nil.snoc step).append post).chainSteps)) endEpochC
  -- the key is unslashed at the step that sets its exit
  have cleanA : u.slashed = false := by
    cases s : u.slashed
    · rfl
    · exact absurd unset (run_slashed_exit_assigned ((shared.append fromFin).append pre)
        h.genesis h.caps.activation h.caps.compounding aEarly (Internal.Setting.delay h) i u foundA
          s)
  -- the events of C's run are those before the step and those from it
  obtain ⟨e1, replayed1⟩ := pre.balanceEvents_ok aEarly highC
  obtain ⟨eS, replayedS⟩ := ((Run.nil.snoc step).append post).balanceEvents_ok h.early highC
  have whole := balanceEvents_append pre ((Run.nil.snoc step).append post) highC replayed1
    replayedS
  rw [← pre.snoc_append_eq step post, replayedC] at whole
  obtain rfl := Except.ok.inj whole
  have insideC := (Array.getElem?_eq_some_iff.mp foundC).1
  have below := insideC.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' below⟩
  have insideA := (Array.getElem?_eq_some_iff.mp foundA).1
  -- from the step on, the key is exited and not withdrawable through C
  have exited := Internal.exitEpoch_toNat_lt_of_ne_far set
  have held : (getCurrentEpoch counted).toNat < w.withdrawableEpoch.toNat := by
    have delay := (((shared.append fromFin).append pre).snoc step).exit_withdrawable_delay
      h.genesis v.toNat w foundB set
    have shallow := h.shallow
    have near := h.near
    have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
    have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    simp only at finSplit
    omega
  have zeroS := Internal.Run.charge_deposit_credit_zero (shared.append (fromFin.append pre))
    h.genesis step post aFulu h.early highC aEpoch replayedS v.toNat insideA w foundB exited held
  have cleanPre := Internal.prefix_deposits_clean h pre aEarly highC replayed1 v (by simp [foundA,
      cleanA])
  have depFirst := Internal.deposits_le_depPre e1 v.toNat cleanPre
  have scanPre := Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits))
    (· = .deposits) (by intro s; simp) pre highC v replayed1
  have scanRest := Internal.scan_le_events (fun _ => false) (fun s => decide (s = .deposits))
    (· = .deposits) (by intro s; simp) ((Run.nil.snoc step).append post) highC v replayedS
  have consAll := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp)
    ((pre.snoc step).append post) highC v replayedC
  have depSplit := Internal.creditScan_append (fun _ => false) (fun s => decide (s = .deposits))
    v.toNat
    highC pre ((Run.nil.snoc step).append post)
  rw [← pre.snoc_append_eq step post] at depSplit
  have depMono : Internal.depPre e1 v.toNat ≤ Internal.depPre (e1 ++ eS) v.toNat := by
    unfold Internal.depPre
    simp only [List.filter_append, List.map_append, List.sum_append]
    omega
  beta_reduce at scanPre scanRest consAll
  rw [Internal.credC_split, Internal.credN_split]
  unfold Internal.consAmt
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The reward of one key of `CS` is within its charge, its shares and its bands, at ten quotients.

The active key uses the cap or credit bound, and the exited key uses its charge and credits.

The credits of a slashed created key are its proposer credits, deposits and consolidations. -/
private theorem cs_key_round (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (Q : ℕ) (hQ : Q = (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) {i : ℕ}
    (member : i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i <
        split.validators.data.size)) :
    10 * Q * (if isActiveAt counted (getCurrentEpoch counted) i = true then
        3 * (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q)
      else 3 * (min (Internal.chargeAmt tailC i + whistleExtra (pinTerms config pulled anc fin)
        tailC highC
          eventsC i) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q)) ≤
      10 * Q * (if isActiveAt counted (getCurrentEpoch counted) i = true then 0
        else 3 * ((Internal.chargeAmt tailC i + preset.upwardBand + (pinTerms config pulled anc
          fin).depth *
          (pinTerms config pulled anc fin).gainRateMax) / Q)) +
        33 * Internal.propN tailC highC i + 33 * Internal.depPre eventsC i + 33 * Internal.syncCr
          eventsC i +
        33 * Internal.consAmt eventsC i + 30 * (Q * Internal.whistC tailC highC i) +
        10 * (Q * Internal.bandC tailC highC i) + 10 * (Q * Internal.bandX fin highC i) +
        10 * (Q * (if isActiveAt counted (getCurrentEpoch counted) i = true then
          (if (pinTerms config pulled anc fin).gainHigh = true then
            preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
          else (pinTerms config pulled anc fin).unitGain) else 0)) := by
  obtain ⟨fromFin⟩ := h.fromFin
  have quotient : 30 ≤ Q := hQ ▸ h.facts.whistleblower fork
  have pos : 0 < Q := by omega
  have up := h.bands.2
  have incBig := h.facts.incrementSize
  have below := (Internal.PinPresetFacts.below h.facts)
  obtain ⟨inSlashed, created⟩ := Finset.mem_filter.mp member
  obtain ⟨-, -, slashedC⟩ := Finset.mem_filter.mp inSlashed
  have insideC : i < counted.validators.data.size := by
    cases f : counted.validators.data[i]? with
    | none => simp [f] at slashedC
    | some w => exact (Array.getElem?_eq_some_iff.mp f).1
  have small := insideC.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  obtain ⟨eventsF, replayedF⟩ := fromFin.balanceEvents_ok h.early (getCurrentEpoch pulled).toNat
  -- the credits of the key and their bands
  have cred := created_credC_le h tailC highC endEpochC replayedC created slashedC
  obtain ⟨grossP, grossW, grossS, hbC, hbX⟩ :=
    credit_band_bounds h fromFin replayedF tailC highC endEpochC replayedC small
  have splitC := Internal.credC_split tailC highC i
  have splitN := Internal.credN_split tailC highC i
  obtain ⟨v, rfl⟩ : ∃ v : ValidatorIndex, v.toNat = i :=
    ⟨UInt64.ofNat i, UInt64.toNat_ofNat_of_lt' small⟩
  have consScan := Internal.scan_le_events (fun s => decide (s = .consolidations))
    (fun s => decide (s = .consolidations)) (· = .consolidations) (by intro s; simp) tailC highC v
    replayedC
  beta_reduce at consScan
  have consEq : Internal.consAmt eventsC v.toNat =
      ((eventsC.filter fun e => e.source = .consolidations).map (Internal.keyCredit v.toNat)).sum :=
        rfl
  have pWT := Nat.mul_le_mul_right (Internal.whistC tailC highC v.toNat) (show 2 ≤ Q by omega)
  have pC := Nat.mul_le_mul_right (Internal.bandC tailC highC v.toNat) quotient
  have pX := Nat.mul_le_mul_right (Internal.bandX fin highC v.toNat) quotient
  by_cases active : isActiveAt counted (getCurrentEpoch counted) v.toNat = true
  · rw [ite_eq_left active, ite_eq_left active, ite_eq_left active]
    -- a key active at C has the band of its creation
    obtain ⟨wv, foundV, activeV⟩ := isActiveAt_eq_true_iff.mp active
    have activated : ∃ w, counted.validators.data[v.toNat]? = some w ∧
        w.activationEpoch ≠ FAR_FUTURE_EPOCH ∧ w.activationEpoch ≤ getCurrentEpoch counted :=
      ⟨wv, foundV, Consensus.Internal.assigned_of_active activeV,
        activationLe_of_active activeV⟩
    have band := Internal.created_band h fromFin (getCurrentEpoch pulled).toNat (by omega) replayedF
        tailC
      highC endEpochC replayedC activated (by omega)
    have floorMin := Nat.div_mul_le_self
      (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC v.toNat)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) Q
    have minLe := min_le_left (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC
      v.toNat) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    have minMax := min_le_right (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC
      v.toNat) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
    have e : 10 * Q * (3 * (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC
        v.toNat) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q)) =
        30 * (min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC v.toNat)
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / Q * Q) := by ring
    rw [e]
    by_cases high : (pinTerms config pulled anc fin).gainHigh = true
    · rw [ite_eq_left high]
      have pM := Nat.mul_le_mul_right preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        (show 3 ≤ Q by omega)
      omega
    · rw [ite_eq_right high]
      have lowGain : (pinTerms config pulled anc fin).gainHigh = false := by simpa using high
      -- off the high rate, the gains of the credits are within a tenth of them
      have wide := wide_of_lowGain h lowGain
      have tenth := Internal.gain_tenth preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        WEIGHT_DENOMINATOR.toNat
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum (pinTerms config pulled anc fin).perIncrement
        (pinTerms config pulled anc fin).depth (Internal.credC tailC highC v.toNat +
          Internal.whistC tailC highC v.toNat + Internal.syncCr eventsC v.toNat) wide
      rw [Nat.mul_assoc (11 * (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC
        v.toNat +
          Internal.syncCr eventsC v.toNat) /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))] at tenth
      have ceilEq : createdCeil (pinTerms config pulled anc fin) tailC highC eventsC v.toNat =
          Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
            eventsC v.toNat +
            (pinTerms config pulled anc fin).depth *
              (11 * (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
                  Internal.syncCr eventsC v.toNat) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
                    *
                ((pinTerms config pulled anc fin).perIncrement *
                  (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) / WEIGHT_DENOMINATOR.toNat) +
            (pinTerms config pulled anc fin).depth *
              ((pinTerms config pulled anc fin).perIncrement *
                (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) +
            preset.downwardBand := by
        unfold createdCeil
        simp only [lowGain, Bool.false_eq_true, ↓reduceIte]
      have unitEq : (pinTerms config pulled anc fin).unitGain =
          (pinTerms config pulled anc fin).depth *
            ((pinTerms config pulled anc fin).perIncrement *
              (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2) := rfl
      have pU := Nat.mul_le_mul_right (pinTerms config pulled anc fin).unitGain
        (show 3 ≤ Q by omega)
      omega
  · rw [ite_eq_right active, ite_eq_right active, ite_eq_right active]
    -- a key that has exited is read at its charge and its credits
    have extra : Internal.chargeAmt tailC v.toNat + whistleExtra (pinTerms config pulled anc fin)
      tailC
        highC eventsC v.toNat = (Internal.chargeAmt tailC v.toNat + preset.upwardBand +
          (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) +
        (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
          eventsC v.toNat) := by
      unfold whistleExtra
      omega
    have mn := Nat.div_le_div_right (c := Q)
      ((min_le_left _ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat).trans (le_of_eq extra))
    have fl := floor_add_ceil_le (Internal.chargeAmt tailC v.toNat + preset.upwardBand +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax)
      (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
        eventsC v.toNat) Q pos
    have mul := Nat.mul_le_mul_left (10 * Q) (Nat.mul_le_mul_left 3 (mn.trans fl))
    have dist : 10 * Q * (3 * ((Internal.chargeAmt tailC v.toNat + preset.upwardBand +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) / Q +
        (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat + Internal.syncCr
          eventsC v.toNat + Q - 1) /
          Q)) =
        10 * Q * (3 * ((Internal.chargeAmt tailC v.toNat + preset.upwardBand +
          (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) /
            Q)) +
        10 * Q * (3 * ((Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
          Internal.syncCr eventsC v.toNat + Q - 1) / Q)) := by ring
    have hc := ceil_round (Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat
      +
      Internal.syncCr eventsC v.toNat) Q pos
    -- credits bring a band of at least four
    have big : Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
      Internal.syncCr eventsC v.toNat = 0 ∨
        preset.upwardBand ≤ Internal.bandC tailC highC v.toNat + Internal.bandX fin highC v.toNat :=
          by
      omega
    rcases big with zero | four
    · omega
    · have pB := Nat.mul_le_mul_left Q four
      have pUp := Nat.mul_le_mul_left Q (show 4 ≤ preset.upwardBand by omega)
      rw [Nat.mul_add] at pB
      omega

/-- The slack and the rounding of the rewards of the keys of `CS` are paid by their shares.

A created key that has exited is read at its charge and its credits.

A created key active at C is charged for its credits and their gains, or at the largest cap.

Its credits are paid by the shares, with a tenth for their gains.

Its unit, or its largest cap at a high rate, is paid for each active key.

Each credited key has an upward band, which pays the rounding of its floor.

The credits of a slashed created key are its proposer credits.

They are also its deposits before the slashing and its consolidations. -/
private theorem whistle_slack_cs (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    3 * (∑ i ∈ (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
        split.validators.data.size)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i
        = true)), min (createdCeil (pinTerms config pulled anc fin) tailC highC eventsC i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      3 * (∑ i ∈ (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter (fun i => ¬ isActiveAt counted (getCurrentEpoch
          counted) i = true)), min (Internal.chargeAmt tailC i + whistleExtra (pinTerms config
            pulled anc
          fin) tailC highC eventsC i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      3 * (∑ i ∈ (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter (fun i => ¬ isActiveAt counted (getCurrentEpoch
          counted) i = true)), (Internal.chargeAmt tailC i + preset.upwardBand + (pinTerms config
            pulled anc
          fin).depth * (pinTerms config pulled anc fin).gainRateMax) / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
        3 * (∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => ¬ i <
            split.validators.data.size)),
            Internal.whistC tailC highC i) +
        (Internal.wShare preset fork ((∑ v ∈ Internal.CS counted split, Internal.propN tailC highC
          v.toNat) +
            ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.syncCr eventsC
            v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC
            v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandX fin highC v.toNat) : ℕ) +
        ((Internal.CS counted split).filter fun v => isActiveAt counted (getCurrentEpoch counted)
          v.toNat =
          true).card * (if (pinTerms config pulled anc fin).gainHigh = true then
              preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
            else (pinTerms config pulled anc fin).unitGain) := by
  have quotient := h.facts.whistleblower fork
  have pos : 0 < (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by omega
  -- each key of `CS` is within its charge, its shares and its bands
  have rounds := Finset.sum_le_sum fun i (m : i ∈ (Internal.slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)) =>
    cs_key_round h tailC highC endEpochC replayedC _ rfl m
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at rounds
  -- the two groups of the created keys are the keys active at C and the others
  have active (f g : ℕ → ℕ) : ∑ i ∈ (Internal.slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size),
        (if isActiveAt counted (getCurrentEpoch counted) i = true then f i else g i) =
      ∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter
        (fun i => isActiveAt counted (getCurrentEpoch counted) i = true), f i +
      ∑ i ∈ ((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter
        (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true), g i :=
    Finset.sum_ite _ _
  simp only [active, Finset.sum_const_zero, Nat.zero_add, Nat.add_zero] at rounds
  simp only [← Finset.mul_sum] at rounds
  -- the units of the keys active at C are those of the active keys of `CS`
  have cap := sum_CS_positions h (fun i => if isActiveAt counted (getCurrentEpoch counted) i = true
    then 1 else 0)
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const,
    smul_eq_mul, smul_eq_mul, Nat.mul_one, Nat.mul_one] at cap
  have units : ∑ i ∈ ((Internal.slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => isActiveAt counted (getCurrentEpoch counted) i = true),
        (if (pinTerms config pulled anc fin).gainHigh = true then
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        else (pinTerms config pulled anc fin).unitGain) =
      ((Internal.CS counted split).filter fun v => isActiveAt counted (getCurrentEpoch counted)
        v.toNat =
        true).card * (if (pinTerms config pulled anc fin).gainHigh = true then
          preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        else (pinTerms config pulled anc fin).unitGain) := by
    rw [Finset.sum_const, smul_eq_mul, cap]
  rw [units] at rounds
  rw [sum_CS_positions h (fun i => Internal.propN tailC highC i), sum_CS_positions h (fun i =>
      Internal.depPre eventsC i), sum_CS_positions h (fun i => Internal.syncCr eventsC i),
    sum_CS_positions h (fun i => Internal.consAmt eventsC i), sum_CS_positions h (fun i =>
      Internal.bandC tailC highC i), sum_CS_positions h (fun i => Internal.bandX fin highC i)]
  refine Nat.le_of_mul_le_mul_left (c := 10 *
    (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ?_ (by omega)
  have s1 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.propN tailC highC i +
    ∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.depPre eventsC i)
  have s2 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.syncCr eventsC i)
  have s3 := share_ge (preset := preset) (fork := fork) pos
    (∑ i ∈ (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size),
      Internal.consAmt eventsC i)
  linarith

/-- A charge on C's run of a key not active at C is due by C's epoch.

It is also due after the split's epoch and the seed lookahead, as every charge of the run is.

The key is activated at the step that starts its exit, so it is inactive at C only by its exit.

That step is a seed lookahead before the charge's epoch, so the activation is by R's epoch. -/
private theorem charge_due (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) {i : ℕ}
    (inactive : ¬ isActiveAt counted (getCurrentEpoch counted) i = true)
    {c : DepartureCharge} (member : c ∈ tailC.departureCharges) (index : c.index = i) :
    (getCurrentEpoch split).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch ∧
      c.epoch ≤ (getCurrentEpoch counted).toNat ∧
      ∀ wC, counted.validators.data[i]? = some wC →
        wC.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by
  obtain ⟨fromFin⟩ := h.fromFin
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨stop, chosen⟩ := Internal.stop_of_charge fromFin tailC member index
  have selected := stop.selected
  rw [chosen] at selected
  obtain ⟨-, -, -, next, step, remaining, -, inStep, v, w, atStop, atNext, unset, assigned, -⟩ :=
    selected
  have stopElectra : .pectra ≤ stop.state.fork :=
    Nat.le_trans electra (fork_le_of_chainSteps stop.pre.chainSteps)
  have activated := step.chainStep.exit_assigned_activated stopElectra atStop atNext unset assigned
  have activatedNat := UInt64.le_iff_toNat_le.mp activated
  have toCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps stop.post.chainSteps)
  simp only at toCounted
  have stepLow := DirectSafety.Run.departureCharges_epoch_ge_start (Run.nil.snoc step) stopElectra
    (Nat.lt_of_le_of_lt (fork_le_of_chainSteps remaining.chainSteps) h.early) c
    (by simpa [Run.departureCharges] using inStep)
  obtain ⟨last, located, kept⟩ := stop.post.registryLifecycle.validators i v atStop
  have below := getCurrentEpoch_succ_lt_farFuture h.twoSlots stop.state.state
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have sameActivation := kept.activationEpoch (fun same => by
    rw [same] at activatedNat
    omega)
  obtain ⟨wC, foundC, -, epochC⟩ := Run.departure_charge_exit tailC c member
  rw [index] at foundC
  obtain rfl : last = wC := Option.some.inj (located.symm.trans foundC)
  have notActive : isActiveValidator last (getCurrentEpoch counted) = false := by
    cases now : isActiveValidator last (getCurrentEpoch counted)
    · rfl
    · exact absurd (isActiveAt_eq_true_iff.mpr ⟨last, located, now⟩) inactive
  simp only [isActiveValidator, Bool.and_eq_false_iff, decide_eq_false_iff_not] at notActive
  have due : c.epoch ≤ (getCurrentEpoch counted).toNat := by
    rw [← epochC]
    rcases notActive with late | exited
    · exact absurd (UInt64.le_iff_toNat_le.mpr (by rw [sameActivation]; omega)) late
    · exact Nat.le_of_not_lt fun lt => exited (UInt64.lt_iff_toNat_lt.mpr lt)
  refine ⟨DirectSafety.Run.departureCharges_epoch_ge_start tailC electra h.early c member, due,
    fun wC' found => ?_⟩
  obtain rfl : wC' = last := Option.some.inj (found.symm.trans located)
  have near := h.near
  have lookahead : 3 ≤ preset.MAX_SEED_LOOKAHEAD.toNat := h.window
  rw [sameActivation]
  omega

/-- Positions charged on C's run that are not active at C pay at most the window, and are few.

Each such position holds a validator at C, so it is a validator index.

Its charge is due by C's epoch, and it is activated by R's epoch.
-/
private theorem charged_window (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (T : Finset ℕ)
    (keys : ∀ i ∈ T, ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      ∃ c ∈ tailC.departureCharges, c.index = i) :
    ∑ i ∈ T, Internal.chargeAmt tailC i ≤ (pinTerms config pulled anc fin).queueWindow ∧
      T.card ≤ (pinTerms config pulled anc fin).queueKeys := by
  classical
  have small : ∀ i ∈ T, i < 2 ^ 64 := by
    intro i member
    obtain ⟨-, c, inRun, index⟩ := keys i member
    obtain ⟨w, found, -⟩ := Run.departure_charge_exit tailC c inRun
    rw [index] at found
    exact (Array.getElem?_eq_some_iff.mp found).1.trans
      (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted)
  have injective : Set.InjOn (fun i => (UInt64.ofNat i : ValidatorIndex)) T :=
    fun a ha b hb same => by
      have := congrArg UInt64.toNat same
      rwa [UInt64.toNat_ofNat_of_lt' (small a ha), UInt64.toNat_ofNat_of_lt' (small b hb)] at this
  have back : ∀ v ∈ T.image (fun i => (UInt64.ofNat i : ValidatorIndex)), v.toNat ∈ T ∧
      ¬ isActiveAt counted (getCurrentEpoch counted) v.toNat = true ∧
      ∃ c ∈ tailC.departureCharges, c.index = v.toNat := by
    intro v member
    obtain ⟨i, inT, rfl⟩ := Finset.mem_image.mp member
    rw [UInt64.toNat_ofNat_of_lt' (small i inT)]
    exact ⟨inT, keys i inT⟩
  have image : ∑ v ∈ T.image (fun i => (UInt64.ofNat i : ValidatorIndex)),
      Internal.chargeAmt tailC v.toNat = ∑ i ∈ T, Internal.chargeAmt tailC i :=
    Internal.sum_image_ofNat T small (Internal.chargeAmt tailC)
  refine ⟨image ▸ Internal.charge_amounts_le_queueWindow h tailC _ fun v member => ?_, ?_⟩
  · obtain ⟨-, inactive, c, inRun, index⟩ := back v member
    exact ⟨c, inRun, index, (charge_due h tailC inactive inRun index).2.1⟩
  · rw [← Finset.card_image_of_injOn injective]
    refine Internal.charged_count_of h tailC _ fun v member => ?_
    obtain ⟨-, inactive, c, inRun, index⟩ := back v member
    exact ⟨(charge_due h tailC inactive inRun index).2.2,
      fun d dRun dIndex => (charge_due h tailC inactive dRun dIndex).2.1, c, inRun, index⟩

/-- The reward reserve covers keys that R exits, with a queue allowance for newly created keys.

A key of the split's registry that is not slashed at R is a term of `exitedSlashable`.

It exits by R's next epoch.

It is read at its balance and rise, or at its finalized balance.

A key of the split's registry that is none of those, and not active at C, is not slashed at R.

Its exit was assigned on C's branch.

It pays its charge and its rise after it, from the window.

A created key that has exited by C pays its charge from the window.

Each key the queues can exit adds a rounding band and gains at the largest rate. -/
private theorem whistle_exited (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) :
    3 * (∑ i ∈ (((Internal.slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)).filter
        (fun i => PinTerms.exitedSlashable anc pulled i = true)),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
            / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      3 * (∑ i ∈ ((((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB
          i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => ¬ isActiveAt
          counted
          (getCurrentEpoch counted) i = true)), (Internal.chargeAmt tailC i + Internal.riseQ tailC
            highC i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) +
      3 * (∑ i ∈ (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
          split.validators.data.size)).filter (fun i => ¬ isActiveAt counted (getCurrentEpoch
          counted) i = true)), (Internal.chargeAmt tailC i + preset.upwardBand + (pinTerms config
            pulled anc
          fin).depth * (pinTerms config pulled anc fin).gainRateMax) / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (pinTerms config pulled anc fin).reserveW := by
  classical
  set G := preset.upwardBand + (pinTerms config pulled anc fin).depth *
    (pinTerms config pulled anc fin).gainRateMax with hG
  set W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hW
  set S1 := ((Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter
    (fun i => PinTerms.exitedSlashable anc pulled i = true) with hS1
  set S2 := (((Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter
    (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
      ¬ PinTerms.exitedSlashable anc pulled i = true)).filter
    (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true) with hS2
  set S3 := ((Internal.slashedOnC split counted).filter (fun i => ¬ i <
      split.validators.data.size)).filter
    (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true) with hS3
  set P := (pinTerms config pulled anc fin).positions.filter
    (PinTerms.exitedSlashable anc pulled · = true)
  have reserveEq : (pinTerms config pulled anc fin).reserveW =
      3 * (∑ i ∈ P, max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
          (max ((pinTerms config pulled anc fin).bF i) (balanceAt fin i)) +
        (if (pinTerms config pulled anc fin).tight = true then 0 else
          (pinTerms config pulled anc fin).queueWindow +
            (pinTerms config pulled anc fin).queueKeys * G)) / W := rfl
  -- the keys that `exitedSlashable` marks are its terms
  have group1 : ∑ i ∈ S1, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i ≤
      ∑ i ∈ P, max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (max ((pinTerms config pulled anc fin).bF i) (balanceAt fin i)) := by
    have term : ∀ i ∈ S1, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i =
        max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
          (max ((pinTerms config pulled anc fin).bF i) (balanceAt fin i)) := by
      intro i member
      have marked := of_decide_eq_true (Finset.mem_filter.mp member).2
      have notRB : ¬ (pinTerms config pulled anc fin).slashedRB i = true := by
        rw [Internal.slashedRB_eq]
        simp only [decide_eq_true_eq, not_and]
        intro slashed
        rw [marked.1] at slashed
        exact absurd slashed Bool.false_ne_true
      rw [Internal.whistleEnv, ite_eq_right_of_eq_false _ _ (eq_false notRB),
        ite_eq_left_of_eq_true _ _ (eq_true (Or.inl (Finset.mem_filter.mp member).2))]
    rw [Finset.sum_congr rfl term]
    refine Finset.sum_le_sum_of_subset fun i member => ?_
    have marked := of_decide_eq_true (Finset.mem_filter.mp member).2
    obtain ⟨w, found⟩ := Internal.validator_of_flag (state := pulled) (Or.inl marked.2.2)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
        (Finset.mem_filter.mp member).2⟩
  -- the keys charged on C's run, of the split's registry or created on it
  have createdCharged : ∀ i ∈ S3, ∃ c ∈ tailC.departureCharges, c.index = i := by
    intro i member
    obtain ⟨⟨slashedC, created⟩, -⟩ := Finset.mem_filter.mp member |>.imp_left Finset.mem_filter.mp
    obtain ⟨-, flags⟩ := Finset.mem_filter.mp slashedC
    have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
    cases foundC : counted.validators.data[i]? with
    | none => simp [foundC] at flags
    | some w =>
      have marked : w.slashed = true := by simpa [foundC] using flags.2
      have assigned := (Internal.CapStep.run tailC h.caps.activation h.caps.compounding
        h.early).1.appended (Internal.Setting.delay h) i w (Nat.le_of_not_lt created) foundC marked
      obtain ⟨c, inRun, index, -⟩ := Internal.Run.charge_of_exit tailC electra h.early i
        (fun v found => absurd (Array.getElem?_eq_some_iff.mp found).1 created) w foundC assigned
      exact ⟨c, inRun, index⟩
  set T2 := S2.filter fun i => ∃ c ∈ tailC.departureCharges, c.index = i with hT2
  have dropUncharged : ∑ i ∈ S2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) =
      ∑ i ∈ T2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) := by
    rw [hT2, Finset.sum_filter (p := fun i => ∃ c ∈ tailC.departureCharges, c.index = i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with charged
    · rfl
    · rw [Internal.chargeAmt_eq_zero tailC charged,
        Internal.riseQ_eq_zero tailC highC i fun c member same => charged ⟨c, member, same⟩]
      rfl
  have inT : ∀ i ∈ T2 ∪ S3, ¬ isActiveAt counted (getCurrentEpoch counted) i = true ∧
      ∃ c ∈ tailC.departureCharges, c.index = i := by
    intro i member
    rcases Finset.mem_union.mp member with inT2 | inS3
    · obtain ⟨inS2, charged⟩ := Finset.mem_filter.mp inT2
      exact ⟨(Finset.mem_filter.mp inS2).2, charged⟩
    · exact ⟨(Finset.mem_filter.mp inS3).2, createdCharged i inS3⟩
  have apart : Disjoint T2 S3 := by
    refine Finset.disjoint_left.mpr fun i one two => ?_
    have small := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
      (Finset.mem_filter.mp one).1).1).1).2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp two).1).2 small
  have queued : ∑ i ∈ T2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) +
      ∑ i ∈ S3, (Internal.chargeAmt tailC i + preset.upwardBand +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) ≤
      (if (pinTerms config pulled anc fin).tight = true then 0 else
        (pinTerms config pulled anc fin).queueWindow +
          (pinTerms config pulled anc fin).queueKeys * G) := by
    by_cases tight : (pinTerms config pulled anc fin).tight = true
    · -- tight: no charge of the run is due by C's epoch
      have empty : T2 ∪ S3 = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun i member => ?_
        obtain ⟨inactive, c, inRun, index⟩ := inT i member
        have bounds := charge_due h tailC inactive inRun index
        have depthBound := (Internal.tight_iff config pulled anc fin).mp tight
        have finalized := UInt64.le_iff_toNat_le.mp h.finalized
        have near := h.near
        omega
      have none2 : T2 = ∅ := Finset.subset_empty.mp (empty ▸ Finset.subset_union_left)
      have none3 : S3 = ∅ := Finset.subset_empty.mp (empty ▸ Finset.subset_union_right)
      simp [none2, none3, tight]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false tight)]
      have rises : ∀ i ∈ T2, Internal.riseQ tailC highC i ≤ G := fun i _ => by
        rw [hG]
        exact Internal.riseQ_le h tailC highC i
      obtain ⟨window, count⟩ := charged_window h tailC (T2 ∪ S3) inT
      rw [Finset.sum_union apart] at window
      rw [Finset.card_union_of_disjoint apart] at count
      have riseSum : ∑ i ∈ T2, Internal.riseQ tailC highC i ≤ T2.card * G := by
        simpa using Finset.sum_le_card_nsmul T2 _ G rises
      have rewrite3 : ∑ i ∈ S3, (Internal.chargeAmt tailC i + preset.upwardBand +
          (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) =
          ∑ i ∈ S3, Internal.chargeAmt tailC i + S3.card * G := by
        rw [hG, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const,
          smul_eq_mul, smul_eq_mul]
        ring
      rw [Finset.sum_add_distrib, rewrite3]
      have times := Nat.mul_le_mul_right G count
      rw [Nat.add_mul] at times
      omega
  have floors := DirectSafety.Apriori.Internal.sum_div_le S1
    (Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin) W
  have floors2 := DirectSafety.Apriori.Internal.sum_div_le S2
    (fun i => Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) W
  have floors3 := DirectSafety.Apriori.Internal.sum_div_le S3
    (fun i => Internal.chargeAmt tailC i + preset.upwardBand +
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) W
  rw [reserveEq]
  generalize ∑ i ∈ S1, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i = a
    at floors group1
  generalize ∑ i ∈ S2, (Internal.chargeAmt tailC i + Internal.riseQ tailC highC i) = b
    at floors2 dropUncharged
  generalize ∑ i ∈ S3, (Internal.chargeAmt tailC i + preset.upwardBand +
    (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).gainRateMax) = c
    at floors3 queued
  have total : 3 * (a / W) + 3 * (b / W) + 3 * (c / W) ≤ 3 * (a + b + c) / W := by
    calc 3 * (a / W) + 3 * (b / W) + 3 * (c / W) = 3 * (a / W + b / W + c / W) := by ring
      _ ≤ 3 * ((a + b + c) / W) := Nat.mul_le_mul_left 3
          ((Nat.add_le_add Nat.div_add_div_le_add_div (Nat.le_refl _)).trans
            Nat.div_add_div_le_add_div)
      _ ≤ 3 * (a + b + c) / W := Nat.mul_div_le_mul_div_assoc 3 (a + b + c) W
  refine le_trans (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 3 floors)
    (Nat.mul_le_mul_left 3 floors2)) (Nat.mul_le_mul_left 3 floors3)) (total.trans ?_)
  exact Nat.div_le_div_right (Nat.mul_le_mul_left 3 (by omega))

/-- A key active at C has no exit by the finalized epoch at R, so its `bF` is zero.

Such an exit is already set at the finalized state, which would leave the key inactive at C. -/
private theorem bF_zero_of_active (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} (active : isActiveAt counted (getCurrentEpoch counted) i = true) :
    (pinTerms config pulled anc fin).bF i = 0 := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨tailC⟩ := h.toCounted
  have stays : (pinTerms config pulled anc fin).exitBeforeFin i = false := by
    show (pulled.validators.data[i]?).any
      (fun v => decide (v.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat)) = false
    cases found : pulled.validators.data[i]? with
    | none => rfl
    | some w =>
      simp only [Option.any_some, decide_eq_false_iff_not]
      intro exited
      obtain ⟨w0, foundFin, kept⟩ := Internal.exit_kept_of_le_fin h found exited
      have inactive := Internal.inactive_of_exited h.twoSlots (fromFin.append tailC) foundFin
        (by rw [kept]; exact exited)
      simp only at inactive
      rw [inactive] at active
      exact Bool.false_ne_true active
  show (if (pinTerms config pulled anc fin).exitBeforeFin i = true then _ else 0) = 0
  rw [stays]
  rfl

/-- Three rewards at a bound above an aligned bound cost at most the excess more.

The excess is zero or an increment, since both bounds are whole numbers of increments.

An excess below an increment could raise the quotient's floor by one.

Three rewards weigh that more than the excess itself. -/
private theorem floor_excess {E V r Q inc : ℕ} (quotient : 30 ≤ Q) (big : 4 ≤ inc)
    (alignedE : E % inc = 0) (alignedV : V % inc = 0) (within : V ≤ E + r) :
    3 * (max E V / Q) ≤ 3 * (E / Q) + r := by
  by_cases le : V ≤ E
  · rw [max_eq_left le]
    omega
  · have lt : E < V := Nat.lt_of_not_le le
    rw [max_eq_right lt.le]
    have gap := add_le_of_lt_of_aligned alignedV alignedE lt
    obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le lt.le
    have sum : (E + x) / Q ≤ E / Q + x / Q + 1 := by
      rw [Nat.add_div (by omega)]
      split_ifs <;> omega
    have small : x / Q ≤ x / 30 := Nat.div_le_div_left quotient (by norm_num)
    omega

/-- The balance of a key at R with its rise is a whole number of increments. -/
private theorem eR_rise_aligned (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} (within : i < pulled.validators.data.size) :
    (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  obtain ⟨kind, alignedMin, alignedMax⟩ := Internal.capAt_kind h i within
  obtain ⟨alignedR, alignedFin⟩ := Internal.balances_aligned h i
  have fill : ∀ X : ℕ, X % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
      (balanceAt pulled i + (X - balanceAt pulled i)) %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := fun X aligned => by
    rcases le_total (balanceAt pulled i) X with le | le
    · rw [Nat.add_sub_of_le le]
      exact aligned
    · rw [Nat.sub_eq_zero_of_le le, Nat.add_zero]
      exact alignedR
  by_cases kept : (pinTerms config pulled anc fin).keptArm i = true
  · have capAligned : (pinTerms config pulled anc fin).capFor i %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
      rw [Internal.capFor_eq]
      split
      · rcases kind with e | e <;> rw [e] <;> assumption
      · exact alignedMax
    rw [Internal.rise_kept config pulled anc fin i rfl kept]
    exact fill _ (Internal.min_max_aligned capAligned (Internal.min_max_aligned
      (Internal.round_aligned _ _)
      (Internal.min_max_aligned alignedFin (Internal.round_aligned _ _)).2).1).1
  · rw [Internal.rise_of_notKept h i kept]
    exact fill _ alignedMax

/-- A key charged to the flagged-key budget is slashable at R.

It is in R's registry and unslashed there.

It is activated by R's next epoch.

It is not yet withdrawable at the finalized epoch.

A key outside those cases is charged as slashed, late or pending. -/
private theorem free_slashable (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} (inside : i < split.validators.data.size) (below : i < 2 ^ 64)
    (unslashedS : (split.validators.data[i]?.map (·.slashed)).getD false = false)
    (slashedC : (counted.validators.data[i]?.map (·.slashed)).getD false = true)
    (notSlashedR : ¬ (pinTerms config pulled anc fin).slashedRB i = true)
    (active : isActiveAt counted (getCurrentEpoch counted) i = true)
    (notLate : ¬ ((pinTerms config pulled anc fin).tight = false ∧
      ((pinTerms config pulled anc fin).lateB i = true ∨
        (pinTerms config pulled anc fin).pendingRB i = true))) :
    ∃ w, pulled.validators.data[i]? = some w ∧ w.slashed = false ∧
      w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 ∧
      anc.finalizedCheckpoint.epoch.toNat < w.withdrawableEpoch.toNat := by
  classical
  obtain ⟨rp⟩ := h.toPulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have near := h.near
  have roundTrip : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' below
  have oldFound := Array.getElem?_eq_getElem inside
  have oldUnslashed : split.validators.data[i].slashed = false := by
    simpa [oldFound] using unslashedS
  obtain ⟨w, foundR, lifeSplit⟩ := rp.registryLifecycle.validators i _ oldFound
  have unslashedR : w.slashed = false := by
    by_contra slashed
    exact notSlashedR (Internal.slashedRB_of_newly_slashed h oldFound foundR oldUnslashed
      (by simpa using slashed))
  have activated : w.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    by_contra late
    by_cases tight : (pinTerms config pulled anc fin).tight = true
    · have bound := (Internal.tight_iff config pulled anc fin).mp tight
      have memberAC : (UInt64.ofNat i : ValidatorIndex) ∈ Internal.AC counted := by
        simpa [Internal.AC, activeVoters] using mem_getActiveValidatorIndices_of_isActiveAt
          (by rw [roundTrip]; exact active)
      have le := Internal.activation_le_of_active h (by omega) memberAC (by rw [roundTrip]; exact
        foundR)
      omega
    · have loose : (pinTerms config pulled anc fin).tight = false := by simpa using tight
      have deep := mt (Internal.tight_iff config pulled anc fin).mpr tight
      exact notLate ⟨loose, Internal.late_or_pending h foundR (by omega) (by omega)⟩
  have settled : anc.finalizedCheckpoint.epoch.toNat < w.withdrawableEpoch.toNat := by
    by_contra waited
    cases foundC : counted.validators.data[i]? with
    | none => simp [foundC] at slashedC
    | some u =>
      simp only [foundC, Option.map_some, Option.getD_some] at slashedC
      exact Internal.sc3a_unwithdrawn h oldFound foundR foundC oldUnslashed slashedC unslashedR
        (by omega)
  exact ⟨w, foundR, unslashedR, activated, settled⟩

/-- The reward bound charges the key either as flagged or through its stake at C and seat debits.

Its bound is `ebUp` or its balance and rise.

The excess over `ebUp` is at most its `rise`.

If the floor test fails, `flagged` pays the reward at `ebUp`.

Otherwise the key's balance at C contributes to the reward bound.

It also adds the key's seat debits on both runs. -/
private theorem free_key (h : Setting config checks g split fin pulled anc counted V)
    (high : ℕ) (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (v : ValidatorIndex) (inside : v.toNat < split.validators.data.size)
    (unslashedS : (split.validators.data[v.toNat]?.map (·.slashed)).getD false = false)
    (slashedC : (counted.validators.data[v.toNat]?.map (·.slashed)).getD false = true)
    (notSlashedR : ¬ (pinTerms config pulled anc fin).slashedRB v.toNat = true)
    (notExited : ¬ PinTerms.exitedSlashable anc pulled v.toNat = true)
    (active : isActiveAt counted (getCurrentEpoch counted) v.toNat = true)
    (notLate : ¬ ((pinTerms config pulled anc fin).tight = false ∧
      ((pinTerms config pulled anc fin).lateB v.toNat = true ∨
        (pinTerms config pulled anc fin).pendingRB v.toNat = true)))
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat)) :
    3 * (Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin v.toNat / (parameters
      preset
        fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      (if 2 * ((pinTerms config pulled anc fin).lowEB v.toNat - max
          ((pinTerms config pulled anc fin).ebUp v.toNat)
          (max (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).base0 v.toNat) +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
              fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
          3 * ((pinTerms config pulled anc fin).ebUp v.toNat / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) then
        3 * ((pinTerms config pulled anc fin).ebUp v.toNat / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) else 0) +
      (((pinTerms config pulled anc fin).rise v.toNat + 2 * balanceAt counted v.toNat) +
        2 * Internal.syncD eventsF v.toNat + 2 * Internal.syncD eventsC v.toNat) := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have below : v.toNat < 2 ^ 64 := v.toNat_lt
  obtain ⟨w, foundR, -, -, -⟩ := free_slashable h inside below unslashedS slashedC notSlashedR
    active notLate
  have bound := bF_zero_of_active h active
  -- the bound of the key is `ebUp` or its balance and rise
  have env : Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin v.toNat =
      max ((pinTerms config pulled anc fin).ebUp v.toNat)
        (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat) := by
    unfold Internal.whistleEnv
    rw [ite_eq_right_of_eq_false _ _ (eq_false notSlashedR),
      ite_eq_right_of_eq_false _ _ (eq_false (not_or.mpr ⟨notExited, notLate⟩)), bound]
    exact max_zero _
  have excess := floor_excess (r := (pinTerms config pulled anc fin).rise v.toNat)
    (h.facts.whistleblower fork) (by have := h.facts.incrementSize; omega)
    (Internal.ebUp_aligned h v.toNat) (eR_rise_aligned h (Array.getElem?_eq_some_iff.mp foundR).1)
    (by
      obtain ⟨t, ht⟩ : ∃ t, (pinTerms config pulled anc fin).ebUp v.toNat =
          max (max (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
            (min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
              (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
        ⟨_, Internal.ebUp_eq config pulled anc fin electra v.toNat _ rfl⟩
      have := le_trans (le_max_left _ _) (le_max_left _ _) |>.trans ht.ge
      omega)
  rw [env]
  split_ifs with flag
  · omega
  · have floorLe : (pinTerms config pulled anc fin).lowEB v.toNat - max
        ((pinTerms config pulled anc fin).ebUp v.toNat)
        (max (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).base0 v.toNat) +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
            fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
        balanceAt counted v.toNat + Internal.syncD eventsF v.toNat + Internal.syncD eventsC v.toNat
          := by
      cases foundFin : fin.validators.data[v.toNat]? with
      | none =>
        have zero : balanceAt fin v.toNat = 0 := by simp [balanceAt, foundFin]
        have : (pinTerms config pulled anc fin).lowEB v.toNat = 0 := by
          rw [Internal.lowEB_unfold, zero]
          simp
        rw [this, Nat.zero_sub]
        exact Nat.zero_le _
      | some val =>
        have unslashedFin : val.slashed = false := by
          by_contra slashed
          obtain ⟨now, nowFound, nowSlashed⟩ := fromFin.slashedPersistence v.toNat val foundFin
            (by simpa using slashed)
          simp [nowFound, nowSlashed] at unslashedS
        have events := Internal.V_events h fromFin tailC high highC endEpoch endEpochC replayedF
          replayedC
        have := Internal.lowEB_slashed h fromFin tailC events v val foundFin unslashedFin retained
        simp only [List.map_append, List.sum_append] at this
        unfold Internal.syncD
        omega
    omega

/-- The reward budget counts the stake of active keys outside C's quorum twice. -/
private theorem free_k7 (T : Finset ValidatorIndex)
    (member : ∀ v ∈ T, v ∈ Internal.AC counted ∧ v ∉ Internal.Q counted) :
    ((2 * ∑ v ∈ T, balanceAt counted v.toNat : ℕ) : ℤ) ≤ -Internal.cK7 pulled counted := by
  classical
  let term : ValidatorIndex → ℤ := fun v => if v ∈ Internal.AC counted ∧ v ∉ Internal.Q counted then
    ((2 * Internal.eC counted v : ℕ) : ℤ) + (if v ∈ Internal.AR pulled then (Internal.eR pulled v :
      ℤ) else 0) else 0
  have negK7 : -Internal.cK7 pulled counted = ∑ v ∈ Internal.U pulled counted, term v := by
    unfold Internal.cK7
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [term]
    split_ifs <;> push_cast <;> ring
  have onT : ∀ v ∈ T, ((2 * balanceAt counted v.toNat : ℕ) : ℤ) ≤ term v := fun v hv => by
    have inside := member v hv
    simp only [term, inside.1, inside.2, not_false_eq_true, and_self, ↓reduceIte]
    split_ifs <;> simp [Internal.eC]
  rw [negK7, Finset.mul_sum, Nat.cast_sum]
  exact (Finset.sum_le_sum onT).trans (Finset.sum_le_sum_of_subset_of_nonneg
    (fun v hv => Finset.mem_union.mpr (.inl (Finset.mem_union.mpr (.inr (member v hv).1))))
    fun v _ _ => by simp only [term]; split_ifs <;> positivity)

/-- The whistleblower rewards of C's other slashed keys are paid from their own stake.

These are the keys of the split's registry that C slashes and leaves active.

R neither slashes them nor exits them.

Outside the tight window, R does not count them in `late` or `pendingR`.

They are active at both branches.

A slashable key whose floor does not cover its reward is flagged, and `flagged` pays it at `ebUp`.

The other keys draw on their stake at C and their seat debits.

C's branch has a separate allowance for seat debits.

The sync budget covers the seat debits of the shared segment.

The excess of the bound over `ebUp` is the key's own `rise`. -/
private theorem whistle_free (h : Setting config checks g split fin pulled anc counted V)
    (high : ℕ) (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ((3 * (∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i
        = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt
        counted
        (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms config pulled anc
        fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
        pulled anc fin).pendingRB i = true)))),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
            / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) : ℕ) : ℤ) ≤
      -Internal.cK7 pulled counted - Internal.cS pulled counted V + (pinTerms config pulled anc
        fin).flagged +
          (pinTerms config pulled anc fin).seatShortfall +
        ((∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc
            fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun
            i =>
            isActiveAt counted (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms
            config pulled anc fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true
            ∨ (pinTerms config pulled anc fin).pendingRB i = true)))), (pinTerms config pulled anc
            fin).rise i + 2 * ∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
            split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc
            fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun
            i =>
            isActiveAt counted (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms
            config pulled anc fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true
            ∨ (pinTerms config pulled anc fin).pendingRB i = true)))),
            Internal.syncD eventsF i : ℕ) : ℤ) := by
  classical
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  set FW : Finset ℕ := (((((Internal.slashedOnC split counted).filter (fun i => i <
    split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i
    = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt counted
    (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms config pulled anc
    fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
    pulled anc fin).pendingRB i = true)))) with hFW
  have facts : ∀ i ∈ FW, i < split.validators.data.size ∧ i < 2 ^ 64 ∧
      (split.validators.data[i]?.map (·.slashed)).getD false = false ∧
      (counted.validators.data[i]?.map (·.slashed)).getD false = true ∧
      ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
      ¬ PinTerms.exitedSlashable anc pulled i = true ∧
      isActiveAt counted (getCurrentEpoch counted) i = true ∧
      ¬ ((pinTerms config pulled anc fin).tight = false ∧
        ((pinTerms config pulled anc fin).lateB i = true ∨
          (pinTerms config pulled anc fin).pendingRB i = true)) := by
    intro i hi
    simp only [hFW, Internal.slashedOnC, Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨⟨⟨⟨⟨count, unslashed, slashedC⟩, inside⟩, notSlashed, notExited⟩, active⟩, notLate⟩ :=
      hi
    exact ⟨inside, count.trans (BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted),
      unslashed, slashedC, notSlashed, notExited, active, notLate⟩
  have retained : ∀ v : ValidatorIndex, v.toNat ∈ FW →
      ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat) :=
    fun v member => by
      obtain ⟨tail⟩ := h.toPulled
      obtain ⟨⟨⟨⟨onC, inside⟩, notR, notExit⟩, -⟩, -⟩ := by
        simpa only [hFW, Finset.mem_filter] using member
      exact slashedC_retained h fromFin tail tailC v onC inside notR notExit
  -- each key is paid by `flagged`, its stake at C, its seat debits and its rise
  have key := fun i (member : i ∈ FW) => by
    obtain ⟨inside, below, unslashed, slashedC, notSlashed, notExited, active, notLate⟩ :=
      facts i member
    have roundTrip : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' below
    have paid := free_key h high endEpoch fromFin replayedF tailC highC endEpochC replayedC
      (UInt64.ofNat i) (by simpa only [roundTrip] using inside)
      (by simpa only [roundTrip] using unslashed) (by simpa only [roundTrip] using slashedC)
      (by simpa only [roundTrip] using notSlashed)
      (by simpa only [roundTrip] using notExited) (by simpa only [roundTrip] using active)
      (by simpa only [roundTrip] using notLate)
      (retained _ (by simpa only [roundTrip] using member))
    simpa only [roundTrip] using paid
  have summed := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at summed
  -- `flagged` pays the keys that fail the floor test
  have flagSum : ∑ i ∈ FW, (if 2 * ((pinTerms config pulled anc fin).lowEB i - max
      ((pinTerms config pulled anc fin).ebUp i)
      (max (balanceAt fin i) ((pinTerms config pulled anc fin).base0 i) +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
          fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
      3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
        fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) then
      3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
        fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) else 0) ≤
      (pinTerms config pulled anc fin).flagged := by
    have flaggedEq : (pinTerms config pulled anc fin).flagged =
        ∑ i ∈ (Finset.range pulled.validators.data.size).filter (fun i =>
          ((pulled.validators.data[i]?.map (·.slashed)).getD false = false ∧
            (pulled.validators.data[i]?).any (fun v =>
              decide (v.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1) &&
                decide (anc.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat)) = true) ∧
          2 * ((pinTerms config pulled anc fin).lowEB i - max
            ((pinTerms config pulled anc fin).ebUp i)
            (max (balanceAt fin i) ((pinTerms config pulled anc fin).base0 i) +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) / (parameters preset
                fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) <
          3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)),
          3 * ((pinTerms config pulled anc fin).ebUp i / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := rfl
    rw [flaggedEq, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset fun i member => ?_
    obtain ⟨inFW, flag⟩ := Finset.mem_filter.mp member
    obtain ⟨inside, below, unslashed, slashedC, notSlashed, notExited, active, notLate⟩ :=
      facts i inFW
    obtain ⟨w, found, unslashedR, activated, settled⟩ := free_slashable h inside below unslashed
      slashedC notSlashed active notLate
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1,
      ⟨by simp [found, unslashedR], ?_⟩, flag⟩
    simp [found, activated, settled]
  -- `seatShortfall` pays the seat debits of C's run
  have seats : 2 * ∑ i ∈ FW, Internal.syncD eventsC i ≤ (pinTerms config pulled anc
    fin).seatShortfall := by
    have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
    have debits := (Internal.Run.syncDebits_le tailC h.fulu h.early highC replayedC
      pulledTotal.toNat (Internal.step_band_of_tail h fromFin tailC h.near pulledOk) FW).1
    have totalEq := Internal.getD_total_eq pulledOk
    have seatEq : (pinTerms config pulled anc fin).seatShortfall =
        2 * ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat * PinTerms.syncEnvelope preset
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat) := rfl
    have depthEq : (pinTerms config pulled anc fin).depth =
        (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
    have epochs : (getCurrentEpoch counted).toNat + 1 - (getCurrentEpoch split).toNat ≤
        (pinTerms config pulled anc fin).depth := by
      have := h.near
      omega
    rw [seatEq, totalEq]
    exact Nat.mul_le_mul_left 2 (debits.trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ epochs))))
  -- `cK7` pays twice the stake at C of the keys, which are active at C and slashed there
  have k7 : ((2 * ∑ i ∈ FW, balanceAt counted i : ℕ) : ℤ) ≤ -Internal.cK7 pulled counted := by
    have toSC := sum_SC_filter_positions h (fun i => ((¬ (pinTerms config pulled anc
      fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true) ∧
      isActiveAt counted (getCurrentEpoch counted) i = true) ∧ ¬ ((pinTerms config pulled anc
      fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
      pulled anc fin).pendingRB i = true))) (fun i => balanceAt counted i)
    have sameFW : ∑ i ∈ FW, balanceAt counted i = ∑ i ∈ ((Internal.slashedOnC split counted).filter
        (fun i => i < split.validators.data.size)).filter (fun i => ((¬ (pinTerms config pulled
          anc fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true) ∧
          isActiveAt counted (getCurrentEpoch counted) i = true) ∧ ¬ ((pinTerms config pulled anc
          fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
          pulled anc fin).pendingRB i = true))), balanceAt counted i := by
      rw [hFW]
      simp only [Finset.filter_filter]
      exact Finset.sum_congr (Finset.filter_congr fun x _ => by tauto) fun _ _ => rfl
    rw [sameFW, ← toSC]
    refine free_k7 _ fun v member => ?_
    obtain ⟨inSC, ⟨⟨-, active⟩, -⟩⟩ := Finset.mem_filter.mp member
    refine ⟨by simpa [Internal.AC, activeVoters] using
      mem_getActiveValidatorIndices_of_isActiveAt active, ?_⟩
    intro quorum
    have flag := (Finset.mem_filter.mp inSC).2.1
    simp only [Internal.Q, quorumVoters, Finset.mem_filter] at quorum
    unfold slashedFlagAt at flag
    have := quorum.2
    rw [flag] at this
    simp at this
  have rest : 0 ≤ -Internal.cS pulled counted V := by
    unfold Internal.cS
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_nonneg fun v _ => by split_ifs <;> simp
  have nat : 3 * ∑ i ∈ FW, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (pinTerms config pulled anc fin).flagged +
      (∑ i ∈ FW, (pinTerms config pulled anc fin).rise i + 2 * ∑ i ∈ FW, balanceAt counted i +
        2 * ∑ i ∈ FW, Internal.syncD eventsF i + 2 * ∑ i ∈ FW, Internal.syncD eventsC i) := by
    omega
  push_cast at k7 ⊢
  have seatsZ : (2 * ∑ i ∈ FW, Internal.syncD eventsC i : ℤ) ≤
      (pinTerms config pulled anc fin).seatShortfall := by exact_mod_cast seats
  have natZ := (Int.ofNat_le.mpr nat)
  push_cast at natZ
  linarith

/-- The rise and seat debit of an active key, with its late or pending charge. -/
def _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whistleActiveRow (config : Config)
  (pulled anc fin : BeaconState preset fork)
    (i seatDebit : ℕ) : ℕ :=
  let terms := pinTerms config pulled anc fin
  let W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat
  let excess := (balanceAt fin i - balanceAt pulled i - terms.rise i + (W - 1)) / W
  terms.rise i + 2 * seatDebit +
    (if terms.tight = false ∧ terms.lateB i = true then 3 * balanceAt pulled i + 3 * excess
      else 0) +
    (if terms.tight = false ∧ terms.pendingRB i = true then balanceAt pulled i + 3 * excess
      else 0)

/-- A key of the split's registry that only C activates pays from its row of R.

At R the key is late or pending, and only the upcoming-only quorum class can share that charge.

It needs no floor.

Its effective part is that row's, three times for `late`, and its rise is the single claim.

Its finalized balance can exceed its balance and rise at R.

The row's reward of that excess, rounded up, pays the rest. -/
private theorem whistle_late (h : Setting config checks g split fin pulled anc counted V) :
    3 * (∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
        split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i
        = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt
        counted
        (getCurrentEpoch counted) i = true)).filter (fun i => ((pinTerms config pulled anc
        fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
        pulled anc fin).pendingRB i = true)))),
          Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
            / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      ∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)).filter (fun i => ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms
          config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc fin).pendingRB i =
          true)))), Internal.whistleActiveRow config pulled anc fin i 0 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i member => ?_
  simp only [Finset.mem_filter] at member
  obtain ⟨⟨⟨-, notRB⟩, active⟩, late⟩ := member
  -- the key is active at C, so its `bF` is zero
  have noExit := bF_zero_of_active h active
  rw [Internal.whistleEnv, ite_eq_right_of_eq_false _ _ (eq_false notRB.1),
    ite_eq_left_of_eq_true _ _ (eq_true (Or.inr late)), noExit, max_eq_right (Nat.zero_le _)]
  have quotient := h.facts.whistleblower fork
  -- the larger of the two balances is the balance and rise at R, and the excess over them
  have floor : max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (balanceAt fin i) / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (balanceAt fin i - balanceAt pulled i - (pinTerms config pulled anc fin).rise i +
          ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1)) /
          (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
    have split := floor_add_ceil_le (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
      (balanceAt fin i - (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat (by omega)
    have whole : max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (balanceAt fin i) = balanceAt pulled i + (pinTerms config pulled anc fin).rise i +
          (balanceAt fin i - (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)) := by
      rw [Nat.max_def]
      split_ifs <;> omega
    have excess : balanceAt fin i - (balanceAt pulled i + (pinTerms config pulled anc fin).rise i) +
        (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1 =
        balanceAt fin i - balanceAt pulled i - (pinTerms config pulled anc fin).rise i +
          ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) := by
      omega
    rw [whole]
    rw [excess] at split
    exact split
  have three : 3 * ((balanceAt pulled i + (pinTerms config pulled anc fin).rise i) /
      (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) ≤
      balanceAt pulled i + (pinTerms config pulled anc fin).rise i :=
    (Nat.mul_le_mul_right _ (by omega)).trans (Nat.mul_div_le _ _)
  simp only [Internal.whistleActiveRow]
  split_ifs
  · omega
  · omega
  · omega
  · rename_i notLate notPending
    rcases late.2 with lateKey | pendingKey
    · exact absurd ⟨late.1, lateKey⟩ notLate
    · exact absurd ⟨late.1, pendingKey⟩ notPending

/-- W from the keys' payers.

The reserve covers the rewards through the keys' shares and the separate slashing charges.

The seat debits, the keys' own `rise` and R's slashing of the key pay the rest.

`registry` is the bound of the keys of the split's registry on each step of C's branch. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_whistle_of (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {eventsP : List (BalanceEvent preset)}
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
                eventsC eventsF events fin i)
    (registryCharge : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
            (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
                eventsC eventsF events fin i) :
    3 * ((∑ v ∈ (Internal.K4 pulled counted V), (Internal.whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (Internal.K5 counted V), (Internal.whistC tailC highC v.toNat : ℤ)) +
      (∑ v ∈ (Internal.K6 pulled counted), (Internal.whistC tailC highC v.toNat : ℤ))) ≤
      -Internal.cK7 pulled counted - Internal.cS pulled counted V + (pinTerms config pulled anc
        fin).reserveW +
        (pinTerms config pulled anc fin).flagged + (pinTerms config pulled anc fin).seatShortfall +
        ((Internal.wShare preset fork ((∑ v ∈ Internal.SC pulled counted split, Internal.propN tailC
          highC v.toNat) +
            ∑ v ∈ Internal.SC pulled counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr
            eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.consAmt
            eventsC v.toNat) +
          Internal.wShare preset fork
            (∑ v ∈ Internal.SC pulled counted split, (Internal.syncD eventsF v.toNat +
              Internal.syncD events v.toNat)) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.bandX fin highC v.toNat) +
          Internal.wShare preset fork ((∑ v ∈ Internal.CS counted split, Internal.propN tailC highC
            v.toNat) +
            ∑ v ∈ Internal.CS counted split, Internal.depPre eventsC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.syncCr eventsC
            v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.CS counted split, Internal.consAmt eventsC
            v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandC tailC highC v.toNat) +
          (∑ v ∈ Internal.CS counted split, Internal.bandX fin highC v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.syncCr eventsF
              v.toNat) +
          Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true,
              Internal.consAmt eventsF v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split with
            (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true, Internal.bandX fin high
              v.toNat) :
            ℕ) : ℤ) +
        ((∑ v ∈ Internal.SC pulled counted split, (Internal.unitK (pinTerms config pulled anc fin)
          tailC highC eventsC
            events eventsF v.toNat +
            Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) v.toNat +
              Internal.bandR (eventsF
                ++ events) v.toNat +
            if (pinTerms config pulled anc fin).exitBeforeFin v.toNat = true then
              (if 0 < Internal.syncCr eventsF v.toNat then preset.upwardBand else 0) else 0) : ℕ) :
                ℤ) +
        ((Internal.wShare preset fork (∑ v ∈ Internal.SC pulled counted split, Internal.propN pre
          highC v.toNat) +
          (∑ v ∈ Internal.SC pulled counted split, Internal.syncCr eventsP v.toNat) +
          3 * (∑ v ∈ Internal.scCharged pulled counted split tailC, Internal.whistC pre highC
            v.toNat) +
          (∑ v ∈ Internal.scCharged pulled counted split tailC,
            if 0 < Internal.propN pre highC v.toNat + Internal.whistC pre highC v.toNat +
              Internal.syncCr eventsP v.toNat then
              preset.upwardBand else 0) : ℕ) : ℤ) +
        ((∑ v ∈ Internal.SC pulled counted split with (¬ (pinTerms config pulled anc fin).slashedRB
          v.toNat =
            true ∧
          ¬ PinTerms.exitedSlashable anc pulled v.toNat = true) ∧
          isActiveAt counted (getCurrentEpoch counted) v.toNat = true,
          Internal.whistleActiveRow config pulled anc fin v.toNat (Internal.syncD eventsF v.toNat) :
            ℕ) : ℤ) +
        ((3 * ∑ v ∈ Internal.SC pulled counted split with (pinTerms config pulled anc fin).slashedRB
          v.toNat
            = true,
          ((max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
            (balanceAt fin v.toNat)) / (parameters
              preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
            (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + (parameters preset
                fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) / (parameters preset
                fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) : ℕ) : ℤ) +
        (((Internal.CS counted split).filter fun v => isActiveAt counted (getCurrentEpoch counted)
          v.toNat =
          true).card * (if (pinTerms config pulled anc fin).gainHigh = true then
              preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
            else (pinTerms config pulled anc fin).unitGain) : ℕ) := by
  classical
  have quotient := h.facts.whistleblower fork
  -- the whistleblower credits of the classes and of `CS` are bounded by the reward base
  have core := whistle_core h fromFin tail high tailC highC endEpochC replayedC pre registry
    registryCharge ((Internal.K4 pulled counted V ∪ Internal.K5 counted V ∪ Internal.K6 pulled
      counted) ∪ Internal.SC pulled counted
      split ∪ Internal.CS counted split)
  obtain ⟨dK, -⟩ := Internal.cs_disjoint h
  obtain ⟨dS, -⟩ := Internal.sc_disjoint h
  obtain ⟨d45, d46, d56, -⟩ := Internal.classes_disjoint h
  rw [Finset.sum_union dK, Finset.sum_union dS,
    Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d46, d56⟩), Finset.sum_union d45,
    sum_CS_positions h (fun i => Internal.whistC tailC highC i),
    sum_SC_positions h (fun i => Internal.whistC tailC highC i)] at core
  -- the part of the reward base that each payer takes
  have sc := whistle_slack_sc h tail high endEpoch replayed fromFin replayedF tailC highC
    endEpochC replayedC pre eventsP
  have cs := whistle_slack_cs h tailC highC endEpochC replayedC
  have whistSplit := (Finset.sum_filter_add_sum_filter_not (Internal.slashedOnC split counted)
    (fun i => i < split.validators.data.size) (fun i => Internal.whistC tailC highC i)).symm
  have exited := whistle_exited h tailC highC
  have free := whistle_free h high endEpoch fromFin replayedF tailC highC endEpochC replayedC
  -- the keys that R slashes pay `branchR`'s claim
  have slashedKeys : 3 * ∑ i ∈ (((Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter (fun i => (pinTerms config pulled anc fin).slashedRB i =
      true)), Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i / (parameters
        preset
      fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat ≤
      3 * ∑ v ∈ Internal.SC pulled counted split with (pinTerms config pulled anc fin).slashedRB
        v.toNat =
          true,
        ((max (balanceAt pulled v.toNat + (pinTerms config pulled anc fin).rise v.toNat)
            (balanceAt fin v.toNat)) / (parameters
            preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + (parameters preset
              fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) / (parameters preset
              fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
    rw [sum_SC_filter_positions h (fun i => (pinTerms config pulled anc fin).slashedRB i = true)
      (fun i => (max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
          (balanceAt fin i)) / (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat + (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 1) / (parameters preset
            fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)]
    refine Nat.mul_le_mul_left 3 (Finset.sum_le_sum fun i member => ?_)
    have slashedR : (pinTerms config pulled anc fin).slashedRB i = true := (Finset.mem_filter.mp
        member).2
    simp only [slashedR, Internal.whistleEnv, ite_true]
    exact (Nat.div_le_div_right (by omega : max (balanceAt pulled i +
      (pinTerms config pulled anc fin).rise i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      (balanceAt fin i) ≤ max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
      (balanceAt fin i) + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)).trans
      (floor_add_ceil_le (max (balanceAt pulled i + (pinTerms config pulled anc fin).rise i)
        (balanceAt fin i)) preset.EFFECTIVE_BALANCE_INCREMENT.toNat (parameters preset
          fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat (by omega))
  -- the keys that C leaves active, read at their rise, their rows and their seat debits
  have activeKeys : ∑ v ∈ Internal.SC pulled counted split with (¬ (pinTerms config pulled anc
    fin).slashedRB
      v.toNat = true ∧
        ¬ PinTerms.exitedSlashable anc pulled v.toNat = true) ∧
        isActiveAt counted (getCurrentEpoch counted) v.toNat = true,
        Internal.whistleActiveRow config pulled anc fin v.toNat (Internal.syncD eventsF v.toNat) =
      ∑ i ∈ ((((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)), Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i) := by
    rw [sum_SC_filter_positions h (fun i => (¬ (pinTerms config pulled anc fin).slashedRB i = true ∧
      ¬ PinTerms.exitedSlashable anc pulled i = true) ∧ isActiveAt counted (getCurrentEpoch
      counted) i =
          true)
      (fun i => Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i))]
    simp only [Finset.filter_filter, and_assoc]
  have late := whistle_late h
  have partition := Finset.sum_filter_add_sum_filter_not ((((Internal.slashedOnC split
      counted).filter (fun i
      => i < split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc
      fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i =>
      isActiveAt
      counted (getCurrentEpoch counted) i = true)) (fun i => ((pinTerms config pulled anc fin).tight
      = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc
      fin).pendingRB i = true)))
    (fun i => Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i))
  have freeKeys : ∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i =
      true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt counted
      (getCurrentEpoch counted) i = true)).filter (fun i => ¬ ((pinTerms config pulled anc
      fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config
      pulled anc fin).pendingRB i = true)))), (pinTerms config pulled anc fin).rise i + 2 * ∑ i ∈
      (((((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter (fun i
      => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬ PinTerms.exitedSlashable anc
      pulled i =
      true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).filter (fun i
      => ¬ ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms config pulled anc fin).lateB
      i = true ∨ (pinTerms config pulled anc fin).pendingRB i = true)))), Internal.syncD eventsF i ≤
      ∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)).filter (fun i => ¬ ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms
          config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc fin).pendingRB i =
          true)))), Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i) :=
            by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by simp only [Internal.whistleActiveRow]; split_ifs <;> omega
  have lateKeys : ∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
      split.validators.data.size)).filter (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i =
      true ∧ ¬ PinTerms.exitedSlashable anc pulled i = true)).filter (fun i => isActiveAt counted
      (getCurrentEpoch counted) i = true)).filter (fun i => ((pinTerms config pulled anc fin).tight
      = false ∧ ((pinTerms config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc
      fin).pendingRB i = true)))), Internal.whistleActiveRow config pulled anc fin i 0 ≤
      ∑ i ∈ (((((Internal.slashedOnC split counted).filter (fun i => i <
          split.validators.data.size)).filter
          (fun i => ¬ (pinTerms config pulled anc fin).slashedRB i = true ∧ ¬
          PinTerms.exitedSlashable anc
          pulled i = true)).filter (fun i => isActiveAt counted (getCurrentEpoch counted) i =
          true)).filter (fun i => ((pinTerms config pulled anc fin).tight = false ∧ ((pinTerms
          config pulled anc fin).lateB i = true ∨ (pinTerms config pulled anc fin).pendingRB i =
          true)))), Internal.whistleActiveRow config pulled anc fin i (Internal.syncD eventsF i) :=
    Finset.sum_le_sum fun i _ => by simp only [Internal.whistleActiveRow]; split_ifs <;> omega
  have wSplit := (Finset.sum_filter_add_sum_filter_not (Internal.slashedOnC split counted)
    (fun i => i < split.validators.data.size) (fun i => Internal.whistC tailC highC i)).symm
  zify at core sc cs whistSplit exited free late slashedKeys activeKeys partition
  zify at freeKeys lateKeys wSplit ⊢
  linarith

/-- Glue: V keys are current at R, and distinct keys have distinct positions. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_fall (h : Setting config checks
  g split fin pulled anc counted V) :
    (∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) ≤
      ∑ i ∈ (pinTerms config pulled anc fin).positions with
        (pinTerms config pulled anc fin).current i = true,
        (pinTerms config pulled anc fin).fall i := by
  have within := BeaconState.registryWithinLimit_of_lt h.early pulled
  refine voters_sum_le (pinTerms config pulled anc fin).fall fun v voter => ?_
  have listed : v ∈ getActiveValidatorIndices pulled (getCurrentEpoch pulled) := by
    simpa [activeVoters] using (h.voting v voter).1
  obtain ⟨validator, found, active⟩ := (mem_getActiveValidatorIndices within).mp listed
  exact Internal.mem_positions_filter config pulled anc fin found
    (isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩)

/-- The quorum reserve covers the stake that joins the active set. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.bud_joining : (pinTerms config
  pulled anc fin).joining ≤
    (pinTerms config pulled anc fin).quorum := by
  dsimp only [pinTerms, quorumReserve]
  exact (show ∀ a b c : ℕ, a ≤ 2 * (a + b) + 3 * c by intros; omega) _ _ _

/-- The weighted gains of the flows fit `creditLow`, the slashed term and the credits themselves.

The gains are bounded linearly, at the rate `11 * D * FP / (I * WD)` of a unit of flow.

The credit part pays at a rate below one, so it costs at most itself.

The other parts round down their increments once, and `f` at least two covers the rounding.

The consolidations are a whole number `m` of increments, and the slashed keys are at most `n`. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_close (I WD FP D D2 m OC Wr Wc
  Wo Ws n df L : ℕ)
    (hI : 0 < I) (hWD : 0 < WD) (key : 0 < L → 11 * D * FP < WD * I) (f2 : 0 < L → 2 ≤ FP / WD)
    (hD : D ≤ df) (hDD : D ≤ D2) (hc : Wc ≤ 3 * (I * m)) (ho : Wo ≤ OC) (hs : Ws ≤ 3 * (I * n))
    (lin : 10 * (I * WD) * L ≤ 11 * D * FP * (Wr + Wc + Wo + Ws)) :
    10 * L ≤ 10 * ((33 * D2 * (m * FP / WD) + 11 * D2 * ((OC / I) * FP / WD) +
      30 * D2 * (FP / WD + 1) + 9) / 10 + 3 * (n * (2 * df * (FP / WD)))) + Wr := by
  rcases Nat.eq_zero_or_pos L with zero | pos
  · subst zero; simp
  have key := key pos
  have f2 := f2 pos
  generalize hf : FP / WD = f at f2 ⊢
  generalize hcg : m * FP / WD = cg
  generalize hog : OC / I * FP / WD = og
  have cG : m * FP ≤ WD * (cg + 1) := by
    have := Nat.lt_mul_div_succ (m * FP) hWD; rw [hcg] at this; exact this.le
  have oG : OC / I * FP ≤ WD * (og + 1) := by
    have := Nat.lt_mul_div_succ (OC / I * FP) hWD; rw [hog] at this; exact this.le
  have fG : FP ≤ WD * (f + 1) := by
    have := Nat.lt_mul_div_succ FP hWD; rw [hf] at this; exact this.le
  have ocLt : OC < I * (OC / I + 1) := by
    have := Nat.lt_mul_div_succ OC hI; exact this
  -- the credit part pays at the rate below one
  have rate : 11 * D * FP * Wr ≤ I * WD * Wr := by
    have := Nat.mul_le_mul_right Wr key.le; linarith
  have consB : 11 * D * FP * Wc ≤ I * WD * (33 * D * (cg + 1)) := by
    calc 11 * D * FP * Wc ≤ 11 * D * FP * (3 * (I * m)) := Nat.mul_le_mul_left _ hc
      _ = 33 * D * I * (m * FP) := by ring
      _ ≤ 33 * D * I * (WD * (cg + 1)) := Nat.mul_le_mul_left _ cG
      _ = I * WD * (33 * D * (cg + 1)) := by ring
  have otherB : 11 * D * FP * Wo ≤ I * WD * (11 * D * (og + f + 2)) := by
    have step1 : FP * OC ≤ FP * (I * (OC / I)) + FP * I := by
      have := Nat.mul_le_mul_left FP ocLt.le
      calc FP * OC ≤ FP * (I * (OC / I + 1)) := this
        _ = FP * (I * (OC / I)) + FP * I := by ring
    have step2 : FP * (I * (OC / I)) ≤ I * (WD * (og + 1)) := by
      calc FP * (I * (OC / I)) = I * (OC / I * FP) := by ring
        _ ≤ I * (WD * (og + 1)) := Nat.mul_le_mul_left _ oG
    have step3 : FP * I ≤ I * (WD * (f + 1)) := by
      calc FP * I = I * FP := by ring
        _ ≤ I * (WD * (f + 1)) := Nat.mul_le_mul_left _ fG
    calc 11 * D * FP * Wo ≤ 11 * D * (FP * OC) := by
          calc 11 * D * FP * Wo = 11 * D * (FP * Wo) := by ring
            _ ≤ 11 * D * (FP * OC) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ho)
      _ ≤ 11 * D * (I * (WD * (og + 1)) + I * (WD * (f + 1))) := by
          refine Nat.mul_le_mul_left _ ?_
          omega
      _ = I * WD * (11 * D * (og + f + 2)) := by ring
  have slashB : 11 * D * FP * Ws ≤ I * WD * (33 * D * n * (f + 1)) := by
    calc 11 * D * FP * Ws ≤ 11 * D * FP * (3 * (I * n)) := Nat.mul_le_mul_left _ hs
      _ = 33 * D * n * I * FP := by ring
      _ ≤ 33 * D * n * I * (WD * (f + 1)) := Nat.mul_le_mul_left _ fG
      _ = I * WD * (33 * D * n * (f + 1)) := by ring
  have total : 10 * (I * WD) * L ≤ I * WD * (Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) +
      33 * D * n * (f + 1)) := by
    calc 10 * (I * WD) * L ≤ 11 * D * FP * (Wr + Wc + Wo + Ws) := lin
      _ = 11 * D * FP * Wr + 11 * D * FP * Wc + 11 * D * FP * Wo + 11 * D * FP * Ws := by ring
      _ ≤ _ := by nlinarith [rate, consB, otherB, slashB]
  have cancel : 10 * L ≤ Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) + 33 * D * n * (f + 1) := by
    have hq : 0 < I * WD := Nat.mul_pos hI hWD
    have : I * WD * (10 * L) ≤ I * WD * (Wr + 33 * D * (cg + 1) + 11 * D * (og + f + 2) +
      33 * D * n * (f + 1)) := by linarith
    exact Nat.le_of_mul_le_mul_left this hq
  have t1 : 25 * D ≤ 19 * (D * f) := by nlinarith
  have t2 : 33 * D * n * (f + 1) ≤ 60 * (n * (df * f)) := by
    have a : D * n * f ≤ n * (df * f) := by
      calc D * n * f = n * (D * f) := by ring
        _ ≤ n * (df * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD)
    have b : D * n * 2 ≤ n * (df * f) := by
      calc D * n * 2 ≤ n * (df * 2) := by
            have := Nat.mul_le_mul_left n (Nat.mul_le_mul_right 2 hD); linarith
        _ ≤ n * (df * f) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ f2)
    have e : 33 * D * n * (f + 1) = 33 * (D * n * f) + 33 * (D * n) := by ring
    have hN := Nat.zero_le (n * (df * f))
    linarith
  have rnd : 33 * D2 * cg + 11 * D2 * og + 30 * D2 * (f + 1) ≤
      10 * ((33 * D2 * cg + 11 * D2 * og + 30 * D2 * (f + 1) + 9) / 10) := by omega
  have m1 : D * cg ≤ D2 * cg := Nat.mul_le_mul_right _ hDD
  have m2 : D * og ≤ D2 * og := Nat.mul_le_mul_right _ hDD
  have m3 : D * f ≤ D2 * f := Nat.mul_le_mul_right _ hDD
  have e1 : 33 * D * (cg + 1) = 33 * D * cg + 33 * D := by ring
  have e2 : 11 * D * (og + f + 2) = 11 * D * og + 11 * (D * f) + 22 * D := by ring
  have e3 : 30 * D2 * (f + 1) = 30 * (D2 * f) + 30 * D2 := by ring
  have e4 : 3 * (n * (2 * df * f)) = 6 * (n * (df * f)) := by ring
  rw [e3] at rnd
  rw [e3, e4]
  linarith

/-- The gains of the counted keys, at their weights, are at most the linear rate of their flows.

The credits of each class are read through the function `cA`, `cB` or `cC` of the key. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_lin (t : PinTerms preset) {x y
  : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (A B C : Finset ValidatorIndex)
    (cA cB cC : ℕ → ℕ) :
    10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
        ((∑ v ∈ A, Internal.flowK t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
          3 * (∑ v ∈ B, Internal.flowK t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
          (∑ v ∈ C, Internal.flowK t tailC high eventsC events eventsF v.toNat (cC v.toNat))) ≤
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
        ((∑ v ∈ A, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
          3 * (∑ v ∈ B, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cB
            v.toNat)) +
          (∑ v ∈ C, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cC v.toNat)))
            := by
  have each (i c : ℕ) :
      10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
        Internal.flowK t tailC high eventsC events eventsF i c ≤
      11 * min t.depth t.depthFin *
          (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
        Internal.flowCredit t tailC high eventsC events eventsF i c := by
    have lin := Internal.gain_lin preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
      (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) (min t.depth t.depthFin)
      (Internal.flowCredit t tailC high eventsC events eventsF i c)
    unfold Internal.flowK
    split_ifs
    · unfold Internal.flowGain
      rwa [Nat.mul_assoc (11 * Internal.flowCredit t tailC high eventsC events eventsF i c /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat))]
    · simp
  have sum (S : Finset ValidatorIndex) (cS : ℕ → ℕ) :
      10 * (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * WEIGHT_DENOMINATOR.toNat) *
          (∑ v ∈ S, Internal.flowK t tailC high eventsC events eventsF v.toNat (cS v.toNat)) ≤
        11 * min t.depth t.depthFin *
            (t.perIncrement * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) *
          (∑ v ∈ S, Internal.flowCredit t tailC high eventsC events eventsF v.toNat (cS v.toNat)) :=
            by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun v _ => each v.toNat (cS v.toNat)
  have a := sum A cA
  have b := sum B cB
  have c := sum C cC
  nlinarith [a, b, c]

/-- On R's branch the budget counts one balance increment per slashing for initial penalties. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_slash (h : Setting config
  checks g split fin pulled anc counted V)
    (W : Finset ValidatorIndex) :
    ∑ v ∈ W, Internal.slashW (pinTerms config pulled anc fin) v.toNat ≤
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).slashedR := by
  refine le_trans (Finset.sum_le_sum fun v _ => ?_) (Internal.slashR_le config pulled anc fin W)
  unfold Internal.slashW Internal.slashR
  split_ifs
  · have := h.facts.slashBand
    exact le_trans (Nat.le_add_right _ _) this
  · exact le_rfl

/-- The sync budget bounds the flows of any set of keys.

The flows are C's credits and the debits of R's run and of the shared segment.

The debits of the shared segment and of R's run take the epochs from the finalized block to the end.

C's credit bound includes the seat rewards and the proposer's share. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_sync (h : Setting config
  checks g split fin pulled anc counted V)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (Internal.syncCr eventsC i + Internal.syncD events i + Internal.syncD eventsF i) ≤
      ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have totalEq := Internal.getD_total_eq pulledOk
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have credits := Internal.syncCredits_le h tailC highC replayedC keys
  have shared := (Internal.Run.syncDebits_le fromFin h.fulu h.early high replayedF
    pulledTotal.toNat (Internal.step_band_of_guard h fromFin (by omega) pulledOk) keys).1
  have own := (Internal.Run.syncDebits_le tail h.fulu h.early high replayed pulledTotal.toNat
    (Internal.step_band_of_tail h fromFin tail (Nat.le_succ _) pulledOk) keys).1
  have epochs := Internal.pin_epochs h fromFin
  rw [totalEq]
  simp only [Finset.sum_add_distrib]
  unfold Internal.syncCr Internal.syncD
  have scaled := Nat.mul_le_mul_right
    (preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
      PinTerms.syncEnvelope preset pulledTotal.toNat) (le_of_eq epochs)
  rw [totalEq] at credits
  nlinarith [credits, shared, own, scaled]

/-- Some counted key has a positive flow gain when the weighted gains are positive. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_pos (t : PinTerms preset) {x y
  : ForkedBeaconState preset}
    (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (A B C : Finset ValidatorIndex)
    (cA cB cC : ℕ → ℕ)
    (pos : 0 < (∑ v ∈ A, Internal.flowK t tailC high eventsC events eventsF v.toNat (cA v.toNat)) +
      3 * (∑ v ∈ B, Internal.flowK t tailC high eventsC events eventsF v.toNat (cB v.toNat)) +
      (∑ v ∈ C, Internal.flowK t tailC high eventsC events eventsF v.toNat (cC v.toNat))) :
    ∃ i c, 0 < Internal.flowK t tailC high eventsC events eventsF i c := by
  by_contra none
  have zero : ∀ i c, Internal.flowK t tailC high eventsC events eventsF i c = 0 := fun i c =>
    Nat.eq_zero_of_not_pos fun p => none ⟨i, c, p⟩
  simp only [zero, Finset.sum_const_zero] at pos
  omega

/-- A key with a positive flow gain is on a kept arm or beyond R's registry in the low regime.

Either way its rate per increment is below an eleventh, so the credit part pays below its worth. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_key (h : Setting config checks
  g split fin pulled anc counted V)
    {x y : ForkedBeaconState preset} (tailC : Run config checks x y) (high : ℕ)
    (eventsC events eventsF : List (BalanceEvent preset)) (i c : ℕ)
    (pos : 0 < Internal.flowK (pinTerms config pulled anc fin) tailC high eventsC events eventsF i
      c) :
    11 * (pinTerms config pulled anc fin).depth *
        ((pinTerms config pulled anc fin).perIncrement *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have arm : (pinTerms config pulled anc fin).keptArm i = true ∨
      (i ∉ (pinTerms config pulled anc fin).positions ∧
        (pinTerms config pulled anc fin).gainHigh = false) := by
    by_contra none
    unfold Internal.flowK at pos
    rw [ite_eq_right_iff.mpr (fun c => absurd c none)] at pos
    exact Nat.lt_irrefl 0 pos
  rcases arm with kept | ⟨-, low⟩
  · exact Internal.key_of_kept h i _ (Nat.le_refl _) kept
  · exact wide_of_lowGain h low

/-- The rate of one increment, at the pin's base reward, is at least two.

The base reward per increment is at least four. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_rate (h : Setting config
  checks g split fin pulled anc counted V) :
    2 ≤ (pinTerms config pulled anc fin).perIncrement *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
  have four := Internal.four_le_perIncrement h
  have weights : (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum = 54 := by decide
  have denominator : WEIGHT_DENOMINATOR.toNat = 64 := by decide
  rw [weights, denominator]
  omega

/-- The bound `ebUp` of a key of the registry is at least one increment.

Its top holds the leak of the cap over the window.

That leak is positive since the cap is an increment or more and the rate is at least four. -/
private theorem inc_le_ebUp (h : Setting config checks g split fin pulled anc counted V) {i : ℕ}
    (inside : i < pulled.validators.data.size) :
    preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ (pinTerms config pulled anc fin).ebUp i := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  have four := Internal.four_le_perIncrement h
  obtain ⟨fromFin⟩ := h.fromFin
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have incMeb : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat := by
    have newKey := h.facts.newKey fork
    have := ((newKey.trans (Nat.sub_le _ _)).trans (Nat.sub_le _ _)).trans (Nat.sub_le _ _)
    omega
  have capLe : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
    unfold PinTerms.capAt
    simp only [Array.getElem?_eq_getElem inside, Option.map_some, Option.getD_some]
    exact Nat.le_trans incMeb (UInt64.le_iff_toNat_le.mp
      (Internal.minimum_cap h.caps.activation h.caps.compounding _))
  have floor : ∀ T : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T →
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T - T % preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    fun T le => by
      have parts := Nat.div_add_mod T preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      have one : 1 ≤ T / preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
        (Nat.le_div_iff_mul_le incPos).2 (by omega)
      have whole : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            (T / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by nlinarith
      omega
  have leak : 2 * (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (pinTerms config pulled anc fin).perIncrement) ≤
        (pinTerms config pulled anc fin).leakAt
          (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i :=
    Nat.le_add_right _ _
  have capOne : 1 ≤ PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i /
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat := (Nat.le_div_iff_mul_le incPos).2 (by omega)
  have leakPos : 1 ≤ (pinTerms config pulled anc fin).leakAt
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i := by
    have := Nat.mul_le_mul capOne four
    omega
  have window : 1 ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by omega
  have product := Nat.mul_le_mul window leakPos
  rw [Internal.ebUp_eq config pulled anc fin electra i _ rfl]
  refine le_max_of_le_right (le_min capLe (floor _ ?_))
  omega

/-- The bound that the core reads for a key of R's registry is at most its bound and its slack. -/
private theorem whistleRead_le (t : PinTerms preset) (pulled anc counted : BeaconState preset fork)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {x' y' : ForkedBeaconState preset} (rrun : Run config checks x' y')
    {x'' y'' : ForkedBeaconState preset} (pre : Run config checks x'' y'') (highC high : ℕ)
    (eventsC eventsF events eventsP : List (BalanceEvent preset)) (fin : BeaconState preset fork)
    (i : ℕ) :
    whistleRead t pulled anc counted tail rrun pre highC high eventsC eventsF events eventsP fin
        i ≤
      Internal.whistleEnv t pulled anc fin i +
        Internal.whistleSlack t tail rrun highC high eventsC eventsF events fin i := by
  unfold whistleRead
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- A key of R's registry is read at most twice the largest of its bounds by `whistleEnv`.

The increment that a key slashed on R's branch adds is at most its bound `ebUp`.

Every other branch reads at most the key's balance and rise, or `bF`, or its bound `ebUp`. -/
private theorem whistleEnv_le (t : PinTerms preset) (pulled anc fin : BeaconState preset fork)
    (i : ℕ) (inc : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ t.ebUp i)
    (finLe : balanceAt fin i ≤ t.ebUp i) :
    Internal.whistleEnv t pulled anc fin i ≤
      2 * max (max (t.ebUp i) (balanceAt pulled i + t.rise i)) (t.bF i) := by
  unfold Internal.whistleEnv
  split_ifs <;> omega

/-- The keys of R's registry are read at twice the largest bounds that `otherCredits` pays. -/
private theorem whistleEnv_sum_le (h : Setting config checks g split fin pulled anc counted V)
    (T : Finset ℕ) (inside : ∀ i ∈ T, i < pulled.validators.data.size) :
    ∑ i ∈ T, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i ≤
      2 * ∑ i ∈ (pinTerms config pulled anc fin).positions,
        max (max ((pinTerms config pulled anc fin).ebUp i)
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
          ((pinTerms config pulled anc fin).bF i) := by
  calc ∑ i ∈ T, Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i
      ≤ ∑ i ∈ T, 2 * max (max ((pinTerms config pulled anc fin).ebUp i)
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
          ((pinTerms config pulled anc fin).bF i) :=
        Finset.sum_le_sum fun i member =>
          whistleEnv_le _ _ _ _ i (inc_le_ebUp h (inside i member))
            (Internal.effective_fin_le_ebUp h i)
    _ = 2 * ∑ i ∈ T, max (max ((pinTerms config pulled anc fin).ebUp i)
          (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
          ((pinTerms config pulled anc fin).bF i) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset fun i member =>
        Finset.mem_range.mpr (inside i member))

/-- The sync flows of any keys on the three runs fit the sync part of the credit total.

C's credits take the seats' envelope and the proposer's share.

The shared segment's credits and debits of a seat are at most its reward with the proposer's share.

R's debits take the envelope.

So the segment from the finalized state takes the share too. -/
private theorem sync_flows_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩) (highF : ℕ)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents highF = .ok eventsF)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (keys : Finset ℕ) :
    ∑ i ∈ keys, (Internal.syncCr eventsC i + Internal.syncCr eventsF i + Internal.syncD eventsF i +
      Internal.syncD events i) ≤
      ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
        preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
          PinTerms.syncEnvelope preset ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((pinTerms config pulled anc fin).depth +
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) *
            (pinTerms config pulled anc fin).syncProposer := by
  obtain ⟨pulledTotal, pulledOk⟩ := h.pulledTotal
  have totalEq := Internal.getD_total_eq pulledOk
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have credits := Internal.syncCredits_le h tailC highC replayedC keys
  have pair := (Internal.Run.syncDebits_le fromFin h.fulu h.early highF replayedF
    pulledTotal.toNat (Internal.step_band_of_guard h fromFin (by omega) pulledOk) keys).2.1
  have own := (Internal.Run.syncDebits_le tail h.fulu h.early high replayed pulledTotal.toNat
    (Internal.step_band_of_tail h fromFin tail (Nat.le_succ _) pulledOk) keys).1
  have epochs := Internal.pin_epochs h fromFin
  have proposer := Internal.syncProposer_eq config pulled anc fin
  rw [proposer] at credits ⊢
  rw [totalEq] at credits ⊢
  unfold Internal.syncSeatEnvelope at pair
  rw [← epochs]
  simp only [Finset.sum_add_distrib] at pair ⊢
  unfold Internal.syncCr Internal.syncD
  generalize PinTerms.syncEnvelope preset pulledTotal.toNat = env at *
  generalize env * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) =
    share at *
  generalize (pinTerms config pulled anc fin).depth = depth at *
  generalize (getCurrentEpoch pulled).toNat + 1 - (getCurrentEpoch split).toNat = n2 at *
  generalize (getCurrentEpoch split).toNat + 1 - (getCurrentEpoch fin).toNat = n1 at *
  nlinarith [credits, pair, own, Nat.zero_le (n2 * (preset.SLOTS_PER_EPOCH.toNat *
    preset.SYNC_COMMITTEE_SIZE.toNat * share))]

/-- The consolidation credits and bands of any keys, on C's run and the shared segment, fit caps.

Both runs charge entries of the finalized state's queue at their balance caps.

A due entry's cap is at least ten bands, so the bands of both runs are at most a fifth of the caps.

The consolidation reserve bounds the sum of those caps. -/
private theorem cons_slack_le (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (high : ℕ) (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat) (T : Finset ValidatorIndex) :
    (∑ v ∈ T, (Internal.consAmt eventsC v.toNat + Internal.consAmt eventsF v.toNat)) ≤
        (pinTerms config pulled anc fin).consolidationsX ∧
      10 * ((∑ v ∈ T, Internal.bandX fin highC v.toNat) + ∑ v ∈ T, Internal.bandX fin high v.toNat)
        ≤
        2 * (pinTerms config pulled anc fin).consolidationsX := by
  classical
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have finEpoch : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch pulled).toNat :=
    UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  obtain ⟨eventsFin, replayedFin⟩ := fromFin.balanceEvents_ok h.early highC
  have sameF : eventsFin = eventsF := by
    have splitC := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
    simp only at splitC
    have same := DirectSafety.Apriori.Internal.balanceEvents_eq_of_endpoint_le fromFin
      (high := highC) (localHigh := high) (by simp only; omega) (by simp only; omega)
    rw [same, replayedF] at replayedFin
    exact (Except.ok.inj replayedFin).symm
  rw [sameF] at replayedFin
  have boundC := Internal.cons_due_bound h fromFin tailC highC endEpochC highLe replayedFin
    replayedC T
  have caps : ∀ H, H ≤ (getCurrentEpoch pulled).toNat →
      ((Internal.dueList fin electra H T).map fun v =>
        (withdrawalMaxEffectiveBalance preset fork v).toNat).sum ≤
          (pinTerms config pulled anc fin).consolidationsX := fun H later =>
    (Internal.dueList_sum_mono fin electra later T fun v =>
      (withdrawalMaxEffectiveBalance preset fork v).toNat).trans
        ((Internal.dueList_sum_le_all fin electra (getCurrentEpoch pulled).toNat T fun v =>
          (withdrawalMaxEffectiveBalance preset fork v).toNat).trans
            (le_of_eq (Internal.consolidationsX_eq h electra).symm))
  have bands : ∀ H, H ≤ (getCurrentEpoch pulled).toNat →
      10 * ∑ v ∈ T, Internal.bandX fin H v.toNat ≤ (pinTerms config pulled anc fin).consolidationsX
        :=
    fun H later => by
      rw [Internal.bandX_sum fin electra H T, Internal.dueAt_eq fin electra H T]
      calc 10 * (preset.upwardBand * (Internal.dueList fin electra H T).length)
          = (10 * preset.upwardBand) * (Internal.dueList fin electra H T).length := by ring
        _ ≤ preset.MAX_EFFECTIVE_BALANCE.toNat * (Internal.dueList fin electra H T).length :=
          Nat.mul_le_mul_right _ h.facts.band
        _ ≤ _ := Internal.cap_floor_sum h _
        _ ≤ _ := caps H later
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun v _ => ?_) (boundC.trans (caps highC highLe))
    simp only [Internal.consAmt, List.filter_append, List.map_append, List.sum_append]
    omega
  · have first := bands highC highLe
    have second := bands high highLeR
    omega

/-- The rounding slacks of any keys credited on C's run fit the credited-key slots of the window. -/
private theorem band_credited_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (T : Finset ValidatorIndex) (inside : ∀ v ∈ T, v.toNat < counted.validators.data.size) :
    ∑ v ∈ T, Internal.bandC tailC highC v.toNat ≤ preset.upwardBand *
      ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) := by
  rw [Internal.band_sum]
  exact Nat.mul_le_mul_left _ (Internal.credited_slots_le h tailC highC T inside)

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The credits that the registry keys without a deposit gain on C's branch fit the credit total.

Each credit is rounded to at most its double, so the keys pay twice their credits.

Their whistleblower credits stay as they are, for the base to bound.

The proposer credits, the sync flows and the consolidations fit the credit total of `otherCredits`.

The bands of the consolidation targets are at most a fifth of the consolidation total.

The bands of the credited keys are the upward band for each slot of the window.

`SB` is the bands of the keys that hold a seat on the shared segment or on R's run.

`SU` is the units and the induced leak of the keys. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.slack_le (h : Setting config checks
  g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (highLeR : high ≤ (getCurrentEpoch pulled).toNat)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (highLe : highC ≤ (getCurrentEpoch pulled).toNat)
    (T : Finset ℕ) (inside : ∀ i ∈ T, i < split.validators.data.size)
    (quiet : ∀ i ∈ T, Internal.depPre eventsC i = 0) (SB SU : ℕ)
    (seat : ∑ i ∈ T, (Internal.bandR (eventsF ++ events) i +
      if (pinTerms config pulled anc fin).exitBeforeFin i = true then
        (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) ≤ SB)
    (units : ∑ i ∈ T, (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events
      eventsF i +
      Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
      (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
        (pinTerms config pulled anc fin).unitGain else 0)) ≤ SU) :
    ∑ i ∈ T, Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail)
      highC high
        eventsC eventsF events fin i ≤
      2 * ((11 * ((pinTerms config pulled anc fin).consolidationsX +
        (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit +
        (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).syncProposer) + 9) / 10) +
      2 * ∑ i ∈ T, Internal.whistC tailC highC i +
      preset.upwardBand * ((pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat +
        ((pinTerms config pulled anc fin).depth /
          max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat + 2) *
            preset.SYNC_COMMITTEE_SIZE.toNat +
        (pinTerms config pulled anc fin).depth * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) +
      SB + SU := by
  classical
  have grows : split.validators.data.size ≤ counted.validators.data.size := by
    have := registryGrows_of_chainSteps tailC.chainSteps
    exact this
  have within := BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted
  have small : ∀ i ∈ T, i < 2 ^ 64 := fun i member =>
    Nat.lt_trans (Nat.lt_of_lt_of_le (inside i member) grows) within
  have conv := Internal.sum_image_ofNat T small
  -- each credit is rounded to at most its double
  have pointwise : ∀ i ∈ T, Internal.whistleSlack (pinTerms config pulled anc fin) tailC
      (fromFin.append tail) highC high eventsC eventsF events fin i ≤
      2 * (Internal.propN tailC highC i + Internal.whistC tailC highC i +
        (Internal.syncCr eventsC i + Internal.syncCr eventsF i + Internal.syncD eventsF i +
          Internal.syncD events i) +
        (Internal.consAmt eventsC i + Internal.consAmt eventsF i)) +
      Internal.bandC tailC highC i + Internal.bandX fin highC i + Internal.bandX fin high i +
      (Internal.bandR (eventsF ++ events) i +
        if (pinTerms config pulled anc fin).exitBeforeFin i = true then
          (if 0 < Internal.syncCr eventsF i then preset.upwardBand else 0) else 0) +
      (Internal.unitK (pinTerms config pulled anc fin) tailC highC eventsC events eventsF i +
        Internal.inducedR (pinTerms config pulled anc fin) (fromFin.append tail) i +
        (if 0 < Internal.slashW (pinTerms config pulled anc fin) i then
          (pinTerms config pulled anc fin).unitGain else 0)) := by
    intro i member
    have dep := quiet i member
    unfold Internal.whistleSlack Internal.whistleSlackBase
    rw [dep]
    split_ifs <;> omega
  have total := Finset.sum_le_sum pointwise
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at total
  simp only [Finset.sum_add_distrib] at seat units
  -- the sums of the credits
  obtain ⟨toFin⟩ := h.toFin
  have prop := Internal.proposer_rewards_le h (toFin.append fromFin) (.inl ⟨fromFin⟩) Run.nil rfl
    tailC highC
    (T.image UInt64.ofNat)
  rw [Run.nil_append] at prop
  have c1 := conv fun i => Internal.propN tailC highC i
  beta_reduce at c1
  rw [c1] at prop
  have sync := sync_flows_le h fromFin high replayedF tail high replayed tailC highC replayedC T
  simp only [Finset.sum_add_distrib] at sync
  obtain ⟨consSum, consBand⟩ := cons_slack_le h fromFin high endEpoch replayedF highLeR tailC highC
    endEpochC replayedC highLe (T.image UInt64.ofNat)
  have c2 := conv fun i => Internal.consAmt eventsC i + Internal.consAmt eventsF i
  have c3 := conv fun i => Internal.bandX fin highC i
  have c4 := conv fun i => Internal.bandX fin high i
  beta_reduce at c2 c3 c4
  rw [c2] at consSum
  rw [c3, c4] at consBand
  simp only [Finset.sum_add_distrib] at consSum
  have bands := band_credited_le h tailC highC (T.image UInt64.ofNat) (by
    intro v member
    obtain ⟨i, mem, rfl⟩ := Finset.mem_image.mp member
    rw [UInt64.toNat_ofNat_of_lt' (small i mem)]
    exact Nat.lt_of_lt_of_le (inside i mem) grows)
  have c5 := conv fun i => Internal.bandC tailC highC i
  beta_reduce at c5
  rw [c5] at bands
  have credits : (∑ i ∈ T, Internal.propN tailC highC i) + (∑ i ∈ T, Internal.syncCr eventsC i) +
      (∑ i ∈ T, Internal.syncCr eventsF i) + (∑ i ∈ T, Internal.syncD eventsF i) + (∑ i ∈ T,
        Internal.syncD events i) ≤
      (pinTerms config pulled anc fin).depth * (pinTerms config pulled anc fin).proposerCredit +
        (pinTerms config pulled anc fin).depth * preset.SLOTS_PER_EPOCH.toNat *
          preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          preset.SLOTS_PER_EPOCH.toNat * preset.SYNC_COMMITTEE_SIZE.toNat *
            PinTerms.syncEnvelope preset
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).syncProposer := by
    nlinarith [prop, sync]
  omega

/-- The keys of a set that hold a deposit scan on C's run are at most the deposit recipients.

An epoch pass applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` deposits.

C's run has at most the epochs from the finalized state. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.deposit_scan_card_le (h : Setting
  config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ) (T : Finset ℕ)
    (positive : ∀ i ∈ T,
      0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC)) :
    T.card ≤ (pinTerms config pulled anc fin).depthFin *
      preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have shared : Run config checks g ⟨fork, split⟩ := toFin.append fromFin
  have low : (getCurrentEpoch split).toNat ≤ (getCurrentEpoch counted).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps tailC.chainSteps)
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have near := h.near
  have periodLe := Nat.div_le_div_right
    (c := max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) low
  have periods : (getCurrentEpoch counted).toNat /
      max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat =
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat +
        ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
          (getCurrentEpoch split).toNat /
            max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat) := by omega
  obtain ⟨B, S, D, cardB, cardS, cardD, hBS, hD, hSD⟩ := Internal.credited_pieces h.genesis
    h.parameters.lookahead (y := ⟨fork, counted⟩) h.early (Internal.Setting.delay h) highC
    ((getCurrentEpoch counted).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat -
      (getCurrentEpoch split).toNat / max 1 preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat)
    shared tailC h.fulu periods
  have inD : T ⊆ D := fun i member => hD i (positive i member)
  refine (Finset.card_le_card inD).trans (cardD.trans ?_)
  have epochs : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (pinTerms config pulled anc fin).depthFin := by
    show _ ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat
    omega
  rw [Nat.mul_comm]
  exact Nat.mul_le_mul_right _ epochs

/-- The deposited keys of R's registry and the created keys that C slashes fit the recipients.

A key that a deposit credits before its slashing has a positive deposit scan.

`created` is that scan for the keys created on C's branch and slashed there. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.whist_count (h : Setting config
  checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    (created : ∀ i ∈ (Internal.slashedOnC split counted).filter
        (fun i => ¬ i < split.validators.data.size),
      0 < (Internal.creditScan (fun _ => false) (fun s => decide (s = .deposits)) i highC tailC)) :
    ((((Internal.slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter
            (fun i => 0 < Internal.depPre eventsC i)).card +
        (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
            split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).card +
        (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
            split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true)).card) ≤
      (pinTerms config pulled anc fin).depthFin *
        preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  classical
  have apart : Disjoint
      (((Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
        (fun i => 0 < Internal.depPre eventsC i))
      ((Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size)) :=
    Finset.disjoint_left.mpr fun i registry beyond =>
      (Finset.mem_filter.mp beyond).2 (Finset.mem_filter.mp (Finset.mem_filter.mp registry).1).2
  have all := Internal.deposit_scan_card_le h tailC highC
    ((((Internal.slashedOnC split counted).filter (fun i => i < split.validators.data.size)).filter
        (fun i => 0 < Internal.depPre eventsC i)) ∪
      (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    fun i member => by
      rcases Finset.mem_union.mp member with deposited | beyond
      · exact Internal.depPre_pos_scan h tailC highC endEpochC replayedC i
          (Finset.mem_filter.mp deposited).2
      · exact created i beyond
  rw [Finset.card_union_of_disjoint apart] at all
  have split2 := Finset.card_filter_add_card_filter_not
    (s := (Internal.slashedOnC split counted).filter (fun i => ¬ i < split.validators.data.size))
    (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The whistleblower budget bounds the credits of any set of keys.

The bound uses base stake `Sx`, total credits `Y` and total rounding bands `Ck`.

A key that received a deposit on C's branch, or was created there, is read at the largest cap.

`count` bounds those keys by the deposit recipients of the window, so `Y` pays them.

`slack` is the credits that the other keys of R's registry gain on C's branch.

It holds their whistleblower credits twice, because their rounding is at most their double.

Those credits are within the base too, so the bound divides by the quotient less two. -/
theorem _root_.EthLib.Consensus.Models.Network.PinDrift.Internal.flow_whist_of (h : Setting config
  checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩)
    {eventsF events : List (BalanceEvent preset)} (high : ℕ)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC)
    {b : BeaconState preset fork} (pre : Run config checks ⟨fork, b⟩ ⟨fork, split⟩)
    {eventsP : List (BalanceEvent preset)}
    (registry : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
          effectiveAt a i ≤ Internal.whistleEnv (pinTerms config pulled anc fin) pulled anc fin i +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    (registryCharge : ∀ {a b : ForkedBeaconState preset} (step : Step config checks a b),
      tailC.Contains step → ∀ i, i < split.validators.data.size →
        (split.validators.data[i]?.map (·.slashed)).getD false = false →
        (!(a.state.validators.data[i]?.map (·.slashed)).getD false &&
          (b.state.validators.data[i]?.map (·.slashed)).getD false) = true →
        (tailC.departureCharges.any fun c => c.index == i) = true →
          effectiveAt a i ≤ Internal.chargeAmt tailC i + Internal.riseQ tailC highC i +
            (Internal.propN pre highC i + Internal.whistC pre highC i + Internal.syncCr eventsP i) +
            Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
              high
              eventsC eventsF events fin i)
    (Sx Y Ck : ℕ)
    (hSx : Sx = ∑ i ∈ (pinTerms config pulled anc fin).positions,
      max (max ((pinTerms config pulled anc fin).ebUp i)
        (balanceAt pulled i + (pinTerms config pulled anc fin).rise i))
        ((pinTerms config pulled anc fin).bF i))
    (count : ((((Internal.slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter
            (fun i => 0 < Internal.depPre eventsC i)).card +
        (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
            split.validators.data.size)).filter
          (fun i => isActiveAt counted (getCurrentEpoch counted) i = true)).card +
        (((Internal.slashedOnC split counted).filter (fun i => ¬ i <
            split.validators.data.size)).filter
          (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true)).card) ≤
      (pinTerms config pulled anc fin).depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat)
    (slack : (∑ i ∈ ((Internal.slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter (fun i => ¬ 0 < Internal.depPre eventsC
            i),
        Internal.whistleSlack (pinTerms config pulled anc fin) tailC (fromFin.append tail) highC
          high
          eventsC eventsF events fin i) +
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat *
        ((pinTerms config pulled anc fin).depthFin *
          preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) ≤
      2 * ((11 * Y + 9) / 10) + 2 * (Ck) +
        2 * ∑ i ∈ ((Internal.slashedOnC split counted).filter
          (fun i => i < split.validators.data.size)).filter (fun i => ¬ 0 < Internal.depPre eventsC
            i),
            Internal.whistC tailC highC i)
    (keys : Finset ValidatorIndex) :
    ∑ v ∈ keys, Internal.whistC tailC highC v.toNat ≤
      2 * (Sx + (11 * Y + 9) / 10 + Ck) /
        ((parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat - 2) := by
  classical
  obtain ⟨toPulled⟩ := h.toPulled
  have grows : split.validators.data.size ≤ pulled.validators.data.size :=
    registryGrows_of_chainSteps toPulled.chainSteps
  have core := whistle_core h fromFin tail high tailC highC endEpochC replayedC pre registry
    registryCharge
  obtain ⟨T1, hT1⟩ : ∃ T, T = (Internal.slashedOnC split counted).filter
      (fun i => i < split.validators.data.size) := ⟨_, rfl⟩
  obtain ⟨T2, hT2⟩ : ∃ T, T = ((Internal.slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => isActiveAt counted (getCurrentEpoch counted) i = true) := ⟨_, rfl⟩
  obtain ⟨T3, hT3⟩ : ∃ T, T = ((Internal.slashedOnC split counted).filter
      (fun i => ¬ i < split.validators.data.size)).filter
        (fun i => ¬ isActiveAt counted (getCurrentEpoch counted) i = true) := ⟨_, rfl⟩
  rw [← hT1, ← hT2, ← hT3] at core
  rw [← hT1] at count slack
  rw [← hT2, ← hT3] at count
  have insideT1 : ∀ i ∈ T1, i < pulled.validators.data.size := fun i member => by
    rw [hT1] at member
    exact Nat.lt_of_lt_of_le (Finset.mem_filter.mp member).2 grows
  have envSum := whistleEnv_sum_le h T1 insideT1
  rw [← hSx] at envSum
  have hW : 30 ≤ (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat :=
    h.facts.whistleblower fork
  set W := (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT.toNat with hWd
  set M := preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat with hM
  set t := pinTerms config pulled anc fin with ht
  have add2 : ∀ a b : ℕ, a / W + b / W ≤ (a + b) / W := fun a b =>
    (Nat.le_div_iff_mul_le (by omega)).2 (by
      rw [Nat.add_mul]
      exact Nat.add_le_add (Nat.div_mul_le_self a W) (Nat.div_mul_le_self b W))
  -- the registry keys without a deposit on C's branch pay their bound and their credits
  have x1 : ∑ i ∈ T1, min (whistleRead t pulled anc counted tailC (fromFin.append tail) pre highC
        high eventsC eventsF events eventsP fin i) M ≤
      (∑ i ∈ T1, Internal.whistleEnv t pulled anc fin i) +
        (∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i),
          Internal.whistleSlack t tailC (fromFin.append tail) highC high eventsC eventsF events fin
            i) +
        M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not T1 (fun i => 0 < Internal.depPre eventsC i)]
    have deposited : ∑ i ∈ T1.filter (fun i => 0 < Internal.depPre eventsC i), min (whistleRead t
      pulled anc
        counted tailC (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin
        i) M ≤
          M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card :=
      (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm])
    have quiet : ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), min (whistleRead t
      pulled anc
        counted tailC (fromFin.append tail) pre highC high eventsC eventsF events eventsP fin
        i) M ≤
          (∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), Internal.whistleEnv t pulled
            anc fin i) +
          ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i),
            Internal.whistleSlack t tailC (fromFin.append tail) highC high eventsC eventsF events
              fin i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun i _ =>
        (min_le_left _ _).trans (whistleRead_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    have sub : ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), Internal.whistleEnv t
      pulled anc fin i ≤
        ∑ i ∈ T1, Internal.whistleEnv t pulled anc fin i :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  have x2 : ∑ i ∈ T2, min (createdCeil t tailC highC eventsC i) M ≤ M * T2.card :=
    (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm])
  have x3 : ∑ i ∈ T3, min (Internal.chargeAmt tailC i + whistleExtra t tailC highC eventsC i) M ≤
      M * T3.card :=
    (Finset.sum_le_sum fun i _ => min_le_right _ _).trans (by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm])
  have paid : M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card + M * T2.card +
      M * T3.card ≤ M * (t.depthFin * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat) := by
    have := Nat.mul_le_mul_left M count
    rwa [Nat.mul_add, Nat.mul_add] at this
  -- the numerator of the three sums, which every set of keys is bounded by over `W`
  obtain ⟨N, hN⟩ : ∃ N, N = (∑ i ∈ T1, Internal.whistleEnv t pulled anc fin i) +
      (∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i),
        Internal.whistleSlack t tailC (fromFin.append tail) highC high eventsC eventsF events fin i)
          +
      M * (T1.filter (fun i => 0 < Internal.depPre eventsC i)).card + M * T2.card + M * T3.card :=
    ⟨_, rfl⟩
  have bound : ∀ S' : Finset ValidatorIndex, ∑ v ∈ S', Internal.whistC tailC highC v.toNat ≤ N / W
    := by
    intro S'
    refine (core S').trans ?_
    refine (Nat.add_le_add (Nat.add_le_add (sum_div_le T1 _ W) (sum_div_le T2 _ W))
      (sum_div_le T3 _ W)).trans ?_
    refine ((Nat.add_le_add_right (add2 _ _) _).trans (add2 _ _)).trans ?_
    refine Nat.div_le_div_right ?_
    omega
  -- the whistleblower credits of the keys in the numerator are bounded by the base itself
  have within := BeaconState.validators_size_lt_of_lt_glamsterdam h.early counted
  have credits : ∑ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), Internal.whistC tailC
    highC i ≤
      N / W := by
    have small : ∀ i ∈ T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i), i < 2 ^ 64 :=
      fun i member => by
        have inT1 := (Finset.mem_filter.mp member).1
        rw [hT1] at inT1
        have inSlashed := (Finset.mem_filter.mp inT1).1
        unfold Internal.slashedOnC at inSlashed
        exact Nat.lt_trans (Finset.mem_range.mp (Finset.mem_filter.mp inSlashed).1) within
    have image := bound ((T1.filter (fun i => ¬ 0 < Internal.depPre eventsC i)).image UInt64.ofNat)
    rwa [Internal.sum_image_ofNat _ small] at image
  -- `N` is at most the numerator that `otherCredits` pays, with the credits counted twice
  have numerator : N ≤ 2 * (Sx + (11 * Y + 9) / 10 +
      Ck) + 2 * (N / W) := by
    omega
  refine (bound keys).trans ?_
  refine (Nat.le_div_iff_mul_le (by omega)).2 ?_
  have shape : N / W * W ≤ N := Nat.div_mul_le_self N W
  have split2 : N / W * W = N / W * (W - 2) + N / W * 2 := by
    rw [← Nat.mul_add]
    congr 1
    omega
  omega

end Terms

end PinDrift
end EthLib.Consensus.Models.Network
