module

import EthLib.Consensus.Proofs.Transition.InactivityLeakBound
import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumDriftBound
import EthLib.Consensus.Proofs.Transition.SlashedFlags
import EthLib.Consensus.Proofs.Transition.LookaheadActive
import Mathlib.Data.Nat.ModEq
import EthLib.Consensus.Proofs.DirectSafety.Apriori.BlockFold
import Mathlib.Algebra.Order.Floor.Div
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound.ExitCharges

@[expose] public section

namespace EthLib.Consensus.Models.Network
namespace PinDrift

open Base Uint64 Models DirectSafety
open DirectSafety.Apriori.Internal (recordBalance_single)

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

section Terms
variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

namespace Internal

/-- The quarter of any total has a base reward per increment, if any total has one.

The factor times the increment fits in a `UInt64` for every total, and the quarter is positive. -/
theorem quarter_base_ok (facts : PinPresetFacts preset) {total perIncrement : Gwei}
    (perOk : getBaseRewardPerIncrement preset total = .ok perIncrement) (T : Gwei) :
    ∃ pq, getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5) = .ok pq := by
  have size := facts.incrementSize
  have positive : 0 < (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei).toNat := by
    split
    · rename_i big
      simp only [UInt64.toNat_div]
      show 0 < T.toNat / 4
      omega
    · simp only [UInt64.toNat_div]
      show 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat / 5
      omega
  generalize (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ T.toNat then T / 4
    else preset.EFFECTIVE_BALANCE_INCREMENT / 5 : Gwei) = q at positive ⊢
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff] at perOk
  obtain ⟨scaled, scaledOk, -⟩ := perOk
  have root : integerSquareroot q ≠ 0 := fun zero => by
    have value := toNat_integerSquareroot q
    rw [zero] at value
    have := Nat.sqrt_pos.mpr positive
    simp only [UInt64.toNat_zero] at value
    omega
  refine ⟨scaled / integerSquareroot q, ?_⟩
  simp only [getBaseRewardPerIncrement, liftArith, mapError_ok_iff, bind_ok_iff]
  exact ⟨scaled, scaledOk, divChecked_ok_iff.mpr ⟨root, by rw [UInt64.toNat_div]⟩⟩

/-- The pin has a rate `P` that bounds the reward rate at every state of a run from `fin`.

The rate is the reserve's base reward per increment, or zero if the reward read fails.

At the maximum effective balance this rate gives the reserve's flag gain bound. -/
theorem pin_rate_exists (h : Setting config checks g split fin pulled anc counted V) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat ≤
          (pinTerms config pulled anc fin).gainRateMax ∧
      ∀ {m : BeaconState preset fork} (_toM : Run config checks ⟨fork, fin⟩ ⟨fork, m⟩),
        (getCurrentEpoch m).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
        ∀ total perIncrement : Gwei, getTotalActiveBalance m = .ok total →
          getBaseRewardPerIncrement preset total = .ok perIncrement →
          perIncrement.toNat *
              ((∑ i ∈ (getActiveValidatorIndices m (getPreviousEpoch m)).toFinset,
                effectiveAt (⟨fork, m⟩ : ForkedBeaconState preset) i.toNat) /
                  preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
            P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  have gainMax : (pinTerms config pulled anc fin).gainRateMax =
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := rfl
  by_cases anyOk : ∃ total perIncrement : Gwei,
      getBaseRewardPerIncrement preset total = .ok perIncrement
  · obtain ⟨total, perIncrement, perOk⟩ := anyOk
    obtain ⟨pq, pqOk⟩ :=
      Internal.quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
    refine ⟨pq.toNat, by rw [pqOk]; rfl, ?_, fun toM inside =>
      Internal.rate_of_guard h toM inside (Or.inl rfl) pqOk⟩
    rw [gainMax, pqOk]
    simp only [Except.toOption, Option.getD_some, le_refl]
  · refine ⟨0, ?_, ?_, fun _ _ total perIncrement _ perOk =>
      absurd ⟨total, perIncrement, perOk⟩ anyOk⟩
    · cases hr : getBaseRewardPerIncrement preset
          (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
              ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
            (getTotalActiveBalance pulled).toOption.getD 0 / 4
          else preset.EFFECTIVE_BALANCE_INCREMENT / 5) with
      | error e => rfl
      | ok p => exact absurd ⟨_, p, hr⟩ anyOk
    · simp

/-- The pin's rate bounds the reward rate at each state of a prefix of C's tail.

The prefix ends at most one epoch after the call, and its states are of the fork of the setting. -/
theorem key_rate_forked (h : Setting config checks g split fin pulled anc counted V) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      ∀ a : ForkedBeaconState preset, Run config checks ⟨fork, split⟩ a → a.fork ≤ fork →
      (getCurrentEpoch a.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 →
      ∀ total perIncrement : Gwei, getTotalActiveBalance a.state = .ok total →
        getBaseRewardPerIncrement preset total = .ok perIncrement →
        perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices a.state
          (getPreviousEpoch a.state)).toFinset, effectiveAt a j.toNat) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
          P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨P, hP, -, rateAll⟩ := Internal.pin_rate_exists h
  obtain ⟨fromFin⟩ := h.fromFin
  refine ⟨P, hP, fun a run forkLe near total perIncrement totalOk perOk => ?_⟩
  obtain ⟨af, as⟩ := a
  have sameFork : af = fork := Internal.fork_eq_of_run run Run.nil forkLe
  subst sameFork
  simp only at near totalOk perOk ⊢
  exact rateAll (fromFin.append run) (by omega) total perIncrement totalOk perOk

/-- The pin's rate bounds the reward rate at every state of a prefix of C's tail.

The prefix ends at most one epoch after the call.

Each state of its balance path is the end of a run from the finalized block.

So the guard applies. -/
theorem key_rate_pre (h : Setting config checks g split fin pulled anc counted V)
    {a : BeaconState preset fork} (pre : Run config checks ⟨fork, split⟩ ⟨fork, a⟩)
    (near : (getCurrentEpoch a).toNat ≤ (getCurrentEpoch pulled).toNat + 1) :
    ∃ P : ℕ,
      P = ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat ∧
      ∀ z ∈ pre.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  obtain ⟨P, hP, rate⟩ := Internal.key_rate_forked h
  refine ⟨P, hP, fun z member total perIncrement totalOk perOk => ?_⟩
  obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint pre Run.nil
    (show (⟨fork, a⟩ : ForkedBeaconState preset).fork ≤
      (⟨fork, split⟩ : ForkedBeaconState preset).fork from Nat.le_refl _) member
  have order : (getCurrentEpoch z.state).toNat ≤ (getCurrentEpoch a).toNat :=
    UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r2.chainSteps)
  exact rate z r1 (fork_le_of_chainSteps r2.chainSteps) (by omega) total perIncrement totalOk
    perOk

/-- The depth times the reward rate for each increment stays below an eleventh of an increment.

It follows from the second test of the low rate at an aligned bound.

Its units are the gwei of the reward, scaled by the weight denominator. -/
theorem rate_per_increment (I WD F P e0 D : ℕ) (hI : 0 < I) (hWD : 0 < WD)
    (alignedE : e0 % I = 0) (rateLow : 11 * D * (e0 / I * P * F / WD + 1) ≤ e0) :
    11 * D * (P * F) < WD * I := by
  rcases Nat.eq_zero_or_pos D with zero | pos
  · subst zero
    simpa using Nat.mul_pos hWD hI
  · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero alignedE
    have e : e0 / I = m := by rw [hm, Nat.mul_div_cancel_left _ hI]
    rw [e] at rateLow
    have big : 11 ≤ e0 := Nat.le_trans (by
      have := Nat.mul_le_mul (show 11 ≤ 11 * D by omega)
        (Nat.le_add_left 1 (m * P * F / WD))
      simpa using this) rateLow
    have mPos : 0 < m := Nat.pos_of_ne_zero (fun z => by rw [z] at hm; omega)
    have a : m * P * F < WD * (m * P * F / WD + 1) := Nat.lt_mul_div_succ _ hWD
    have b := Nat.mul_lt_mul_of_pos_left a (show 0 < 11 * D by omega)
    have d := Nat.mul_le_mul_left WD rateLow
    have f : (11 * D * (P * F)) * m < (WD * I) * m := by
      calc (11 * D * (P * F)) * m = 11 * D * (m * P * F) := by ring
        _ < 11 * D * (WD * (m * P * F / WD + 1)) := b
        _ = WD * (11 * D * (m * P * F / WD + 1)) := by ring
        _ ≤ WD * e0 := d
        _ = (WD * I) * m := by rw [hm]; ring
    exact Nat.lt_of_mul_lt_mul_right f

/-- The base reward per increment is at least four. -/
theorem four_le_perIncrement (h : Setting config checks g split fin pulled anc counted V) :
    4 ≤ (pinTerms config pulled anc fin).perIncrement := by
  have definition : (pinTerms config pulled anc fin).perIncrement =
      ((getBaseRewardPerIncrement preset
        (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
            ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat := rfl
  obtain ⟨q, hq⟩ : ∃ q : Gwei, q = (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
          (getTotalActiveBalance pulled).toOption.getD 0 / 4
        else preset.EFFECTIVE_BALANCE_INCREMENT / 5) := ⟨_, rfl⟩
  rw [← hq] at definition
  have small : q.toNat < 2 ^ 62 ∨ 5 * q.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
    rw [hq]
    split_ifs
    · left
      have : ((getTotalActiveBalance pulled).toOption.getD 0).toNat < 2 ^ 64 :=
        ((getTotalActiveBalance pulled).toOption.getD 0).toNat_lt
      rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
    · right
      rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
  -- The base reward factor times the balance increment is at least `2 ^ 35`.
  have room := h.facts.rewardScale
  have reward := (Internal.PinPresetFacts.reward h.facts)
  have positive : 0 < q.toNat := by
    have size := h.facts.incrementSize
    rw [hq]
    split_ifs
    · rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
    · rw [UInt64.toNat_div]
      simp only [UInt64.reduceToNat]
      omega
  -- The read succeeds, since the quarter total is positive.
  --
  -- A preset fact also bounds the scaled factor.
  obtain ⟨per, computed⟩ :=
    DirectSafety.Apriori.Internal.perIncrement_exists positive h.facts.fits
  rw [computed] at definition
  simp only [Except.toOption, Option.getD_some] at definition
  have formula := toNat_getBaseRewardPerIncrement computed
  have rootPos : 0 < q.toNat.sqrt := Nat.sqrt_pos.mpr positive
  have rootSmall : 4 * q.toNat.sqrt ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      preset.BASE_REWARD_FACTOR.toNat := by
    rcases small with low | tiny
    -- The root of a quarter total is below `2 ^ 31`.
    · have : q.toNat.sqrt < 2 ^ 31 := Nat.sqrt_lt'.mpr (by norm_num at low ⊢; omega)
      omega
    -- Below the small total the root is at most a fifth of an increment.
    --
    -- The factor covers it.
    · have : q.toNat.sqrt ≤ q.toNat := Nat.sqrt_le_self _
      have : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat * preset.BASE_REWARD_FACTOR.toNat :=
        Nat.le_mul_of_pos_right _ reward
      omega
  have four : 4 ≤ per.toNat := by
    rw [formula]
    exact (Nat.le_div_iff_mul_le rootPos).mpr rootSmall
  rw [definition]
  exact four

/-- The gain on a positive number of increments is below an eleventh of them.

The rate is bounded per effective-balance increment. -/
private theorem gain_lt (I WD F P D k : ℕ) (hk : 0 < k)
    (key : 11 * D * (P * F) < WD * I) : 11 * (D * (k * P * F / WD)) < I * k := by
  have fl : WD * (k * P * F / WD) ≤ k * P * F := Nat.mul_div_le _ _
  have h1 : WD * (11 * (D * (k * P * F / WD))) < WD * (I * k) :=
    calc WD * (11 * (D * (k * P * F / WD))) = 11 * D * (WD * (k * P * F / WD)) := by ring
      _ ≤ 11 * D * (k * P * F) := Nat.mul_le_mul_left _ fl
      _ = k * (11 * D * (P * F)) := by ring
      _ < k * (WD * I) := Nat.mul_lt_mul_of_pos_left key hk
      _ = WD * (I * k) := by ring
  exact Nat.lt_of_mul_lt_mul_left h1

/-- The gain on a credit rounded up to an increment is at most an eleventh of the credit.

The credit is a whole number of increments, so its rounding up is itself. -/
private theorem gain_credit_le (I WD F P D C : ℕ) (hI : 0 < I)
    (alignedC : C % I = 0) (key : 11 * D * (P * F) < WD * I) :
    11 * (D * ((C + I - 1) / I * P * F / WD)) ≤ C := by
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero alignedC
  subst hu
  rw [show (I * u + I - 1) / I = u from smul_ceilDiv (β := Nat) hI u]
  rcases Nat.eq_zero_or_pos u with zero | pos
  · subst zero
    simp
  · exact (gain_lt I WD F P D u pos key).le

/-- The gain at the stake `e0 + C` over `k` epochs splits into two parts.

They are the gain on the credits and the gain at the base stake `e0`.

The floor costs one unit per epoch. -/
private theorem gain_split_flat (I WD F P e0 C k depth : ℕ) (hI : 0 < I) (hk : k ≤ depth)
    (alignedE : e0 % I = 0) (alignedC : C % I = 0) :
    k * ((e0 + C) / I * P * F / WD) ≤
      depth * ((C + I - 1) / I * P * F / WD) + (depth * (e0 / I * P * F / WD) + depth) := by
  obtain ⟨a, rfl⟩ := Nat.dvd_of_mod_eq_zero alignedE
  obtain ⟨b, rfl⟩ := Nat.dvd_of_mod_eq_zero alignedC
  rw [← Nat.mul_add, Nat.mul_div_cancel_left _ hI, Nat.mul_div_cancel_left _ hI,
    show (I * b + I - 1) / I = b from smul_ceilDiv (β := Nat) hI b]
  have floor := Nat.add_div_le_div_add_div_add_one (a * P * F) (b * P * F) WD
  have split : (a + b) * P * F = a * P * F + b * P * F := by ring
  rw [split]
  calc k * ((a * P * F + b * P * F) / WD)
      ≤ depth * ((a * P * F + b * P * F) / WD) := Nat.mul_le_mul_right _ hk
    _ ≤ depth * (a * P * F / WD + b * P * F / WD + 1) := Nat.mul_le_mul_left _ floor
    _ = depth * (b * P * F / WD) + (depth * (a * P * F / WD) + depth) := by ring

/-- The gain of one key's flows is at most the linear rate of the flows.

It drops the floor of the increments and the floor of the rate. -/
theorem gain_lin (I WD FP D Z : ℕ) :
    10 * (I * WD) * (D * (11 * Z / (10 * I) * FP / WD)) ≤ 11 * D * FP * Z := by
  have floorLe : WD * (11 * Z / (10 * I) * FP / WD) ≤ 11 * Z / (10 * I) * FP :=
    Nat.mul_div_le _ _
  have increments : 10 * I * (11 * Z / (10 * I)) ≤ 11 * Z := by
    rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  calc 10 * (I * WD) * (D * (11 * Z / (10 * I) * FP / WD))
      = 10 * I * D * (WD * (11 * Z / (10 * I) * FP / WD)) := by ring
    _ ≤ 10 * I * D * (11 * Z / (10 * I) * FP) := Nat.mul_le_mul_left _ floorLe
    _ = D * FP * (10 * I * (11 * Z / (10 * I))) := by ring
    _ ≤ D * FP * (11 * Z) := Nat.mul_le_mul_left _ increments
    _ = 11 * D * FP * Z := by ring

/-- The gain on whole increments of a stake, at eleven tenths, is at most a tenth of the stake.

The rate is bounded per effective-balance increment. -/
theorem gain_tenth (I WD F P D Zr : ℕ)
    (key : 11 * D * (P * F) < WD * I) :
    D * (11 * Zr / (10 * I) * P * F / WD) ≤ Zr / 10 := by
  have lin := Internal.gain_lin I WD (P * F) D Zr
  rw [Nat.mul_assoc (11 * Zr / (10 * I)) P F]
  generalize D * (11 * Zr / (10 * I) * (P * F) / WD) = G at lin ⊢
  have pos : 0 < I * WD := by
    have := Nat.lt_of_le_of_lt (Nat.zero_le _) key
    rwa [Nat.mul_comm] at this
  have rate : 11 * D * (P * F) * Zr ≤ WD * I * Zr := Nat.mul_le_mul_right Zr key.le
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  refine Nat.le_of_mul_le_mul_left ?_ pos
  calc I * WD * (G * 10) = 10 * (I * WD) * G := by ring
    _ ≤ 11 * D * (P * F) * Zr := lin
    _ ≤ WD * I * Zr := rate
    _ = I * WD * Zr := by ring

/-- The rise bound covers the gain on the base stake with an extra tenth. -/
private theorem base_absorb (D Df q : ℕ) (hDf : D ≤ Df) :
    D * q + D + (D * q + D) / 10 ≤ Df * ((11 * q + 9) / 10 + 3) := by
  have step : 11 * q ≤ 10 * ((11 * q + 9) / 10) := by omega
  have scaled := Nat.mul_le_mul_left D step
  have left : D * (11 * q) = 11 * (D * q) := by ring
  have right : D * (10 * ((11 * q + 9) / 10)) = 10 * (D * ((11 * q + 9) / 10)) := by ring
  have widen := Nat.mul_le_mul_right ((11 * q + 9) / 10 + 3) hDf
  have expand : D * ((11 * q + 9) / 10 + 3) = D * ((11 * q + 9) / 10) + 3 * D := by ring
  omega

/-- The gain of a key's flows and of the base stake is at most its flow gain, a unit and the base.

The joint floor of the flows and the base stake splits by kind with one step.

With no flow there is no step. -/
theorem flow_gain_split (I WD F P D Dt Df q Zk Z' : ℕ)
    (key : 11 * D * (P * F) < WD * I) (hDt : D ≤ Dt) (hDf : D ≤ Df) (hZ : Zk ≤ Z') :
    D * (11 * (Zk + (D * q + D)) / (10 * I) * P * F / WD) + (D * q + D) ≤
      Dt * (11 * Z' / (10 * I) * P * F / WD) +
        (if 0 < Z' then Dt * (P * F / WD + 2) else 0) + Df * ((11 * q + 9) / 10 + 3) := by
  have tenth := Internal.gain_tenth I WD F P D (D * q + D) key
  have absorb := base_absorb D Df q hDf
  have monoGain : D * (11 * Zk / (10 * I) * P * F / WD) ≤
      Dt * (11 * Z' / (10 * I) * P * F / WD) :=
    Nat.mul_le_mul hDt (Nat.div_le_div_right (Nat.mul_le_mul_right F (Nat.mul_le_mul_right P
      (Nat.div_le_div_right (Nat.mul_le_mul_left 11 hZ)))))
  rcases Nat.eq_zero_or_pos Zk with zero | pos
  · subst zero
    simp only [Nat.zero_add]
    split_ifs <;> omega
  · have posZ : 0 < Z' := Nat.lt_of_lt_of_le pos hZ
    have joint : 11 * (Zk + (D * q + D)) / (10 * I) ≤
        11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1 := by
      have := Nat.add_div_le_div_add_div_add_one (11 * Zk) (11 * (D * q + D)) (10 * I)
      rwa [← Nat.mul_add] at this
    have step : D * (11 * (Zk + (D * q + D)) / (10 * I) * P * F / WD) ≤
        D * ((11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1) * P * F / WD) :=
      Nat.mul_le_mul_left D (Nat.div_le_div_right (Nat.mul_le_mul_right F
        (Nat.mul_le_mul_right P joint)))
    have split : (11 * Zk / (10 * I) + 11 * (D * q + D) / (10 * I) + 1) * P * F =
        11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F + P * F := by ring
    have floors : (11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F + P * F) /
        WD ≤ 11 * Zk / (10 * I) * P * F / WD + 11 * (D * q + D) / (10 * I) * P * F / WD +
          P * F / WD + 2 := by
      have one := Nat.add_div_le_div_add_div_add_one
        (11 * Zk / (10 * I) * P * F + 11 * (D * q + D) / (10 * I) * P * F) (P * F) WD
      have two := Nat.add_div_le_div_add_div_add_one (11 * Zk / (10 * I) * P * F)
        (11 * (D * q + D) / (10 * I) * P * F) WD
      omega
    rw [split] at step
    have wide := Nat.mul_le_mul_left D floors
    have expand : ∀ A B C : ℕ, D * (A + B + C + 2) = D * A + D * B + D * C + 2 * D :=
      fun A B C => by ring
    rw [expand] at wide
    have unit : D * (P * F / WD + 2) ≤ Dt * (P * F / WD + 2) := Nat.mul_le_mul_right _ hDt
    have unitSplit : D * (P * F / WD + 2) = D * (P * F / WD) + 2 * D := by ring
    simp only [posZ, ↓reduceIte]
    omega

/-- The closure test of the credit ceiling with the credits rounded down to increments. -/
private theorem ceiling_closed_floor (I WD F P e0 D Cr Cr' S W C q : ℕ)
    (hq : q = e0 / I * P * F / WD) (hI : 0 < I) (key : 11 * D * (P * F) < WD * I)
    -- The stake above `e0` is the credits, the slack `W` and the gain at the base stake.
    (hC : C = I * (11 * (Cr' + W + D * q + D) / (10 * I))) (start : S + Cr ≤ e0 + Cr' + W) :
    S + Cr + (D * ((C + I - 1) / I * P * F / WD) + (D * q + D)) < e0 + C + I := by
  subst hq
  have alignedC : C % I = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  -- The gain on the rounded credits is at most an eleventh of them.
  have credit := gain_credit_le I WD F P D C hI alignedC key
  have div := Nat.div_add_mod (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D)) (10 * I)
  -- Rounding down leaves less than an increment of the stake above `e0` unrounded.
  --
  -- The increment of the bound covers it.
  have lt := Nat.mod_lt (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D)) (show 0 < 10 * I by omega)
  have times : 10 * I * (11 * (Cr' + W + D * (e0 / I * P * F / WD) + D) / (10 * I)) = 10 * C := by
    rw [hC]
    ring
  omega

/-- The arithmetic of the credit ceiling, for any run.

The bound `e0` on the effective balance, with the credits rounded down to increments, is closed.

The gain of any number of epochs up to the depth is at most the gain at the depth.

That gain is a tenth of the credits, the slack and the gain at the base stake. -/
private theorem ceiling_arith (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (P depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    (e0 + C) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) <
        e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
      (∀ k, k ≤ depth → k * ((e0 + C) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ≤
        Internal.gainOn preset depth P C + (depth * q + depth)) ∧
      Internal.gainOn preset depth P C = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * Internal.gainOn preset depth P C ≤ Cr' + W + depth * q + depth := by
  have closed := ceiling_closed_floor preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat F P e0 depth Cr Cr' S W C q hq incPos key hC start
  have alignedC : C % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  have credit := gain_credit_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    WEIGHT_DENOMINATOR.toNat F P depth C incPos alignedC key
  have rounded := Nat.mul_div_le (11 * (Cr' + W + depth * q + depth))
    (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
  have times : 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) =
        10 * C := by
    rw [hC]
    ring
  subst hF
  have alignedE : (e0 + C) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_of_mod_eq_zero alignedE0)
      (Nat.dvd_of_mod_eq_zero alignedC))
  refine ⟨alignedE, closed, fun k within => ?_, ?_, ?_⟩
  · have split := gain_split_flat preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      WEIGHT_DENOMINATOR.toNat (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 C k depth
      incPos within alignedE0 alignedC
    rw [← hq] at split
    exact split
  · unfold Internal.gainOn
    let I := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let u := 11 * (Cr' + W + depth * q + depth) / (10 * I)
    have quotient : (I * u + I - 1) / I = u := smul_ceilDiv (β := Nat) incPos u
    rw [hC, quotient]
  · unfold Internal.gainOn
    omega

/-- A key's balance along a run is at most a stake bound, its credits and the gain at the bound. -/
theorem c_ceiling_abstract {n y : ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P capHigh : ℕ)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ capHigh)
    (capCeil : ∀ z ∈ post.balancePath, PinTerms.capAt z i ≤ capHigh)
    (rate : ∀ z ∈ post.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    -- The stake above `e0` is the credits, the slack `W` and the gain at the base stake.
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt n i) capHigh ≤ S)
    (startEff : effectiveAt n i ≤ e0 + C)
    (credits : Internal.netScan i high post +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post) ≤ Cr)
    -- The rate premise is that of the low regime, at the depth of the call.
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    ∃ gc, gc = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      -- The gain on the rounded credits is at most a tenth of the stake above `e0`.
      10 * gc ≤ Cr' + W + depth * q + depth ∧
      (∀ z ∈ post.balancePath, min (actualBalanceAt z i) capHigh ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      -- Once the credits are rounded down to increments, the bound `e0` is closed.
      effectiveAt y i ≤ e0 + C := by
  obtain ⟨alignedE, closed, splitAll, hform, hten⟩ := ceiling_arith incPos P depth Cr Cr' e0 C S W F
    q hF hq alignedE0 hC key start
  subst hF
  have split := splitAll _ epochs
  have bound : Internal.creditBound post i high (e0 + C) P capHigh ≤
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) := by
    unfold Internal.creditBound
    exact le_trans (le_of_eq (by ring)) (Nat.add_le_add (Nat.add_le_add startBal credits) split)
  have fixpoint : max (effectiveAt n i) (min capHigh
      (Internal.creditBound post i high (e0 + C) P capHigh -
        Internal.creditBound post i high (e0 + C) P capHigh %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le startEff (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt bound closed)))
  obtain ⟨-, -, third, fourth⟩ := Internal.Run.effective_floor_pair post early fulu i inside 0 0
    capHigh high (e0 + C) P
  have balances := fourth alignedCap startCap capCeil (fun z member => .inr (rate z member))
    endEpoch fixpoint
  refine ⟨Internal.gainOn preset depth P C, hform, hten,
    fun z member => Nat.le_trans (balances z member) bound, ?_⟩
  · refine Nat.le_trans (third _ alignedCap startCap balances capCeil).1 ?_
    rw [Nat.min_comm]
    exact fixpoint

/-- A key's balance along a run that makes it compound has the ceiling of a run with one cap. -/
private theorem c_ceiling_abstract_flip {x m n y : ForkedBeaconState preset}
    -- The run splits at the step that makes the key compound.
    (pre : Run config checks x m) (step : Step config checks m n) (post : Run config checks n y)
    (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ x.fork)
    (i : ℕ) (inside : i < x.state.validators.data.size) (high P lo hi : ℕ)
    (alignedLo : lo % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (alignedHi : hi % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0) (loLe : lo ≤ hi)
    (startCap : effectiveAt x i ≤ lo)
    -- Before the step the balance counts up to `lo`, and after it up to `hi`.
    (capsPre : ∀ z ∈ pre.balancePath, PinTerms.capAt z i ≤ lo)
    (capsPost : ∀ z ∈ post.balancePath, PinTerms.capAt z i ≤ hi)
    (rate : ∀ z, z ∈ pre.balancePath ∨ z ∈ post.balancePath → ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth Cr Cr' e0 C S W F q : ℕ)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr' + W + depth * q + depth) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)))
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt x i) lo ≤ S)
    (startEff : effectiveAt x i ≤ e0 + C)
    -- The step leaves its balance within the smaller of its balance before it and `lo`.
    --
    -- The step's credits come on top of that.
    --
    -- So the balance after the step is at most the ceiling before it, plus the credits of the step.
    (junction : actualBalanceAt n i ≤ min (actualBalanceAt m i) lo +
      Internal.stepCredit (fun _ => true) (fun _ => true) i step)
    (keepEff : effectiveAt n i = effectiveAt m i)
    -- The ceiling includes the credits of the step.
    (credits : Internal.netScan i high pre + (Internal.creditScan (fun _ => false)
        (fun s => decide (s ≠ .rewards)) i high pre) +
      Internal.stepCredit (fun _ => true) (fun _ => true) i step + Internal.netScan i high post +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post) ≤ Cr)
    (key : 11 * depth * (P * F) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (start : S + Cr ≤ e0 + Cr' + W) :
    ∃ gc, gc = depth * (11 * (Cr' + W + depth * q + depth) /
        (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
          (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      10 * gc ≤ Cr' + W + depth * q + depth ∧
      (∀ z ∈ pre.balancePath, min (actualBalanceAt z i) lo ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      (∀ z ∈ post.balancePath, min (actualBalanceAt z i) hi ≤ S + Cr +
        (gc + (depth * q + depth))) ∧
      effectiveAt y i ≤ e0 + C := by
  obtain ⟨alignedE, closed, splitAll, hform, hten⟩ := ceiling_arith incPos P depth Cr Cr' e0 C S W F
    q hF hq alignedE0 hC key start
  subst hF
  -- Both parts take the same closed bound `e0 + C`.
  --
  -- Their epochs add up to those of the run.
  have epochStep := UInt64.le_iff_toNat_le.mp step.chainStep.currentEpoch_le
  have epochPre := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
  have epochPost := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  have forkM : m.fork < .glamsterdam := Nat.lt_of_le_of_lt
    (fork_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps) early
  have fuluN : .fusaka ≤ n.fork :=
    Nat.le_trans fulu (fork_le_of_chainSteps (pre.snoc step).chainSteps)
  have insideN : i < n.state.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps (pre.snoc step).chainSteps)
  have split := splitAll ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat +
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat)) (by omega)
  rw [Nat.add_mul] at split
  have boundPre : Internal.creditBound pre i high (e0 + C) P lo ≤
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) := by
    unfold Internal.creditBound
    omega
  have fixPre : max (effectiveAt x i) (min lo (Internal.creditBound pre i high (e0 + C) P lo -
      Internal.creditBound pre i high (e0 + C) P lo %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le startEff (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt boundPre closed)))
  obtain ⟨-, -, thirdPre, fourthPre⟩ := Internal.Run.effective_floor_pair pre
    forkM fulu i inside 0 0 lo high (e0 + C) P
  have balPre := fourthPre alignedLo startCap capsPre
    (fun z member => .inr (rate z (.inl member))) (by omega) fixPre
  obtain ⟨front, atLast⟩ := Run.balancePath_last pre
  have mPre : min (actualBalanceAt m i) lo ≤
      Internal.creditBound pre i high (e0 + C) P lo :=
    balPre m (by rw [atLast]; simp)
  have effM : effectiveAt m i ≤ e0 + C := by
    refine Nat.le_trans (thirdPre _ alignedLo startCap balPre capsPre).1 ?_
    rw [Nat.min_comm]
    exact fixPre
  have effLo : effectiveAt m i ≤ lo := by
    have := (thirdPre _ alignedLo startCap balPre capsPre).1
    omega
  have boundPost : Internal.creditBound post i high (e0 + C) P hi ≤
      S + Cr + (Internal.gainOn preset depth P C + (depth * q + depth)) := by
    unfold Internal.creditBound at mPre ⊢
    omega
  have fixPost : max (effectiveAt n i) (min hi (Internal.creditBound post i high (e0 + C) P hi -
      Internal.creditBound post i high (e0 + C) P hi %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤ e0 + C :=
    max_le (keepEff ▸ effM) (Nat.le_trans (Nat.min_le_right _ _)
      (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt boundPost closed)))
  obtain ⟨-, -, thirdPost, fourthPost⟩ := Internal.Run.effective_floor_pair post early fuluN i
    insideN 0 0 hi high (e0 + C) P
  have balPost := fourthPost alignedHi (by omega) capsPost
    (fun z member => .inr (rate z (.inr member))) endEpoch fixPost
  refine ⟨Internal.gainOn preset depth P C, hform, hten,
    fun z member => Nat.le_trans (balPre z member) boundPre,
    fun z member => Nat.le_trans (balPost z member) boundPost, ?_⟩
  refine Nat.le_trans (thirdPost _ alignedHi (by omega) balPost capsPost).1 ?_
  rw [Nat.min_comm]
  exact fixPost

open DirectSafety.Apriori.Internal in
/-- The rise bound uses the key's own cap when its gain is low and the largest cap otherwise. -/
theorem capFor_eq (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ) :
    (pinTerms config state ancestor finalizedState).capFor i =
      if (decide ((pinTerms config state ancestor finalizedState).depthFin *
            ((11 * (pinTerms config state ancestor finalizedState).gainRate i + 9) / 10 + 3) <
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) &&
          decide (11 * (pinTerms config state ancestor finalizedState).depth *
              ((pinTerms config state ancestor finalizedState).gainRate i + 1) ≤
            (pinTerms config state ancestor finalizedState).ebUp i)) = true then
        PinTerms.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i
      else preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := rfl

/-- The cap used for the rise bound is at least the key's own cap. -/
theorem capAt_le_capFor (config : Config)
    (state ancestor finalizedState : BeaconState preset fork) (i : ℕ)
    (capMax : PinTerms.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i ≤
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) :
    PinTerms.capAt (⟨fork, state⟩ : ForkedBeaconState preset) i ≤
      (pinTerms config state ancestor finalizedState).capFor i := by
  rw [Internal.capFor_eq]
  split
  · exact Nat.le_refl _
  · exact capMax

/-- The rise of a key on its kept arm is the least of its cap, its rounded top and its headroom.

The rounded top adds the downward band to `high`.

The headroom starts from the finalized balance.

The rise is that less the effective balance at R. -/
theorem rise_kept (config : Config) (pulled anc fin : BeaconState preset fork) (i : ℕ)
    {H : ℕ} (hH : H = (pinTerms config pulled anc fin).high i)
    (kept : (pinTerms config pulled anc fin).keptArm i = true) :
    (pinTerms config pulled anc fin).rise i =
      min ((pinTerms config pulled anc fin).capFor i)
        (min (H + preset.downwardBand - (H + preset.downwardBand) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          (max (balanceAt fin i) (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
        balanceAt pulled i := by
  have unfold : (pinTerms config pulled anc fin).rise i =
      if (pinTerms config pulled anc fin).keptArm i = true then
        min ((pinTerms config pulled anc fin).capFor i)
          (min (H + preset.downwardBand - (H + preset.downwardBand) %
                preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
            (max (balanceAt fin i) (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))) -
          balanceAt pulled i
      else (pinTerms config pulled anc fin).capFor i - balanceAt pulled i := by
    rw [hH]
    rfl
  rw [unfold]
  split
  · rfl
  · exact absurd kept ‹_›

/-- A key on its kept arm has an effective balance within its rise, the flows and their slack. -/
theorem rise_close (config : Config) (pulled anc fin : BeaconState preset fork) (i : ℕ)
    {H : ℕ} (hH : H = (pinTerms config pulled anc fin).high i)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (kept : (pinTerms config pulled anc fin).keptArm i = true)
    -- The bound starts from any state, and `start` bounds the effective balance there.
    {eC Bc S U start capHigh : ℕ}
    (alignedC : eC % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startLe : start ≤ max (balanceAt fin i)
      ((H + S) - (H + S) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    -- The key's effective balance stays at that of R, ends at its start, or is within the ceiling.
    (stay : eC = balanceAt pulled i ∨
      -- A key that ends at its start has `start` within the cap.
      --
      -- It also has `start` within the rounded top of `H`.
      (eC ≤ start ∧ start ≤ (pinTerms config pulled anc fin).capFor i + S + U ∧
        start ≤ (H + preset.downwardBand) -
          (H + preset.downwardBand) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat + S + U) ∨
      (eC ≤ Bc + preset.downwardBand ∧
        eC ≤ max start (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh)))
    (capped : eC ≤ (pinTerms config pulled anc fin).capFor i + S + U)
    -- The ceiling is within `high` and the flows.
    (ceiling : Bc ≤ H + S)
    -- The slack is paid when there are flows.
    (slack : S = 0 ∨ preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ U + 1 ∨
      (S < preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∧
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ S + U)) :
    eC ≤ balanceAt pulled i + (pinTerms config pulled anc fin).rise i + S + U := by
  rw [Internal.rise_kept config pulled anc fin i hH kept]
  have arith := Internal.rise_arith (finEB := max (balanceAt fin i)
      (H - H % preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (capFor := (pinTerms config pulled anc fin).capFor i) incPos
    stay (Nat.le_trans startLe (max_le_max (Nat.le_max_left _ _) (Nat.le_refl _))) alignedC
    capped ceiling slack
  rwa [max_assoc, max_self] at arith

/-- The effective-balance ceiling takes the largest of three values.

It takes the effective balance at R, the finalized one or the rounded top limited by the cap.

The top adds the leak at the cap, the net partials and a band to the balance at R.

It accounts for the queued partial withdrawals due by the cutoff. -/
theorem ebUp_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i t : ℕ)
    (ht : t = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (pinTerms config pulled anc fin).leakAt
          (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i +
      (PinTerms.dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
        PinTerms.dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1)) +
      preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) :
    (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  subst ht
  simp only [pinTerms, PinTerms.dueAmount, electra, ↓reduceDIte]
  rfl

/-- The least and the greatest of two whole numbers of increments are such numbers too. -/
theorem min_max_aligned {inc a b : ℕ} (ha : a % inc = 0) (hb : b % inc = 0) :
    min a b % inc = 0 ∧ max a b % inc = 0 :=
  ⟨by rcases min_choice a b with e | e <;> rw [e] <;> assumption,
    by rcases max_choice a b with e | e <;> rw [e] <;> assumption⟩

/-- A number rounded down to an increment is a whole number of increments. -/
theorem round_aligned (inc x : ℕ) : (x - x % inc) % inc = 0 :=
  Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

/-- The effective balances of a key at R and at the finalized state are aligned. -/
theorem balances_aligned (h : Setting config checks g split fin pulled anc counted V)
    (i : ℕ) : balanceAt pulled i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
      balanceAt fin i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  exact ⟨DirectSafety.Apriori.Internal.FloorTrace.effective_aligned
    (shared.append (fromFin.append toPulled)) h.genesis h.aligned i,
    DirectSafety.Apriori.Internal.FloorTrace.effective_aligned shared h.genesis h.aligned i⟩

/-- With aligned effective balances, the ceiling is a whole number of increments. -/
theorem ebUp_aligned (h : Setting config checks g split fin pulled anc counted V) (i : ℕ) :
    (pinTerms config pulled anc fin).ebUp i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨a1, a2⟩ := Internal.balances_aligned h i
  obtain ⟨t, ht⟩ : ∃ t, (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, Internal.ebUp_eq config pulled anc fin electra i _ rfl⟩
  have capAligned : PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    cases found : pulled.validators.data[i]? with
    | none => simp [PinTerms.capAt, found]
    | some w =>
      exact Internal.capAt_aligned h.aligned (z := (⟨fork, pulled⟩ : ForkedBeaconState preset))
        electra found
  rw [ht]
  exact (Internal.min_max_aligned (Internal.min_max_aligned a1 a2).2
    (Internal.min_max_aligned capAligned (Internal.round_aligned _ t)).1).2

/-- A call's cutoff is within the withdrawal delay of the finalized state. -/
theorem window_short (h : Setting config checks g split fin pulled anc counted V) :
    (getCurrentEpoch pulled).toNat + 1 <
      (getCurrentEpoch fin).toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat := by
  have shallow := h.shallow
  omega

/-- The due amounts of a key are those of the entries that name it and are due, in two filters. -/
private theorem dueAmount_eq (state : BeaconState preset fork) (electra : .pectra ≤ fork)
    (v : ValidatorIndex) (cutoff : ℕ) :
    PinTerms.dueAmount state electra v.toNat cutoff =
      ((((state.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ cutoff)).map (·.amount.toNat)).sum := by
  unfold PinTerms.dueAmount
  simp only [List.filter_filter]
  congr 3
  funext entry
  simp [Bool.decide_and, UInt64.toNat_inj, Bool.and_comm]

/-- The leak of the pin does not fall as the effective balance rises. -/
theorem leakAt_mono (config : Config) (pulled anc fin : BeaconState preset fork) {a b : ℕ}
    (i : ℕ) (le : a ≤ b) :
    (pinTerms config pulled anc fin).leakAt a i ≤ (pinTerms config pulled anc fin).leakAt b i := by
  unfold pinTerms
  dsimp only
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.div_le_div_right le)))
    (Nat.div_le_div_right (Nat.mul_le_mul_right _ le))

/-- The leak of the pin at the finalized state's score, spelled out.

The score is the key's inactivity score at the finalized state, or zero before Altair. -/
private theorem leakAt_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (eb i : ℕ) :
    (pinTerms config pulled anc fin).leakAt eb i =
      2 * (eb / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (pinTerms config pulled anc fin).perIncrement) +
      eb * ((if altair : .altair ≤ fork then
          (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) +
        (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
        (config.INACTIVITY_SCORE_BIAS.toNat *
          (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  unfold pinTerms
  rfl

/-- A key's inactivity score at the finalized state is at most the largest score there. -/
private theorem score_le_scoreMax (fin : BeaconState preset fork) (i : ℕ) :
    (if altair : .altair ≤ fork then
        (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) ≤
      (if altair : .altair ≤ fork then
        ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) := by
  split
  · rename_i altair
    cases found : (fin.inactivityScores altair).data[i]? with
    | none => simp
    | some x =>
      have mem : x.toNat ∈ (fin.inactivityScores altair).data.toList.map (·.toNat) :=
        List.mem_map_of_mem (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
      rw [List.foldl_max_eq_max (List.ne_nil_of_mem mem)]
      exact le_max_of_le_right (List.le_max_of_mem mem)
  · exact Nat.le_refl _

/-- Raising the balance by whole increments raises the leak by an amount in those increments.

The amount is the leak of the increments at the key's per-increment reward and the largest score.

It is rounded up once. -/
private theorem leakAt_add_le (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (i eb m : ℕ) :
    (pinTerms config pulled anc fin).leakAt (eb + preset.EFFECTIVE_BALANCE_INCREMENT.toNat * m) i ≤
      (pinTerms config pulled anc fin).leakAt eb i +
        2 * ((pinTerms config pulled anc fin).perIncrement * m) +
        (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * m *
          ((pinTerms config pulled anc fin).scoreMaxFin +
            (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) + 1) := by
  have scoreMax : (pinTerms config pulled anc fin).scoreMaxFin = (if altair : .altair ≤ fork then
      ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) := by
    unfold pinTerms
    rfl
  rw [leakAt_eq, leakAt_eq, scoreMax]
  have score := score_le_scoreMax fin i
  generalize (if altair : .altair ≤ fork then
    (((fin.inactivityScores altair).data[i]?).map (·.toNat)).getD 0 else 0) = S at score ⊢
  generalize (if altair : .altair ≤ fork then
    ((fin.inactivityScores altair).data.toList.map (·.toNat)).foldl max 0 else 0) = M at score ⊢
  generalize (pinTerms config pulled anc fin).perIncrement = P
  generalize (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat = B
  generalize config.INACTIVITY_SCORE_BIAS.toNat *
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat = Q
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = inc at incPos ⊢
  have quotient : (eb + inc * m) / inc = eb / inc + m := by
    rw [Nat.add_mul_div_left _ _ incPos]
  have rounded : (eb + inc * m) * (S + B) / Q ≤ eb * (S + B) / Q + inc * m * (S + B) / Q + 1 := by
    rw [Nat.add_mul]
    exact Nat.add_div_le_div_add_div_add_one _ _ _
  have larger : inc * m * (S + B) / Q ≤ inc * m * (M + B) / Q :=
    Nat.div_le_div_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right score _))
  have step : 2 * ((eb / inc + m) * P) = 2 * (eb / inc * P) + 2 * (P * m) := by ring
  rw [quotient, step]
  generalize eb / inc * P = x at *
  generalize (eb + inc * m) * (S + B) / Q = u at *
  generalize eb * (S + B) / Q = v at *
  generalize inc * m * (S + B) / Q = w at *
  generalize inc * m * (M + B) / Q = z at *
  omega

/-- Extra leak when debits and a penalty raise the bound on the earlier effective balance.

The debits cost the leak of their increments at the key's reward, and the penalty one increment.

A debited key pays one more for the rounding, which the reward of an increment covers. -/
theorem inducedR_le (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (perPos : 1 ≤ (pinTerms config pulled anc fin).perIncrement)
    {x y : ForkedBeaconState preset} (tail : Run config checks x y) (i a s : ℕ) (slack : s ≤ 1)
    (envelope : ∀ z ∈ tail.balancePath, effectiveAt z i ≤
      (pinTerms config pulled anc fin).ebUp i +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (a + s)) :
    Internal.inducedR (pinTerms config pulled anc fin) tail i ≤
      (pinTerms config pulled anc fin).depthFin *
          (3 * (pinTerms config pulled anc fin).perIncrement * a +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a *
              ((pinTerms config pulled anc fin).scoreMaxFin +
                (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
              (config.INACTIVITY_SCORE_BIAS.toNat *
                (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat)) +
        s * (pinTerms config pulled anc fin).slashLeak := by
  have fold : ∀ (l : List ℕ) (b c : ℕ), b ≤ c → (∀ x ∈ l, x ≤ c) → l.foldl max b ≤ c := by
    intro l
    induction l with
    | nil => exact fun _ _ le _ => le
    | cons x xs ih =>
      exact fun b c le all => ih _ c (max_le le (all x List.mem_cons_self))
        fun y m => all y (List.mem_cons_of_mem _ m)
  have mono := Internal.leakAt_mono config pulled anc fin i (fold _ 0 _ (Nat.zero_le _) fun v member
    => by
    obtain ⟨z, inPath, rfl⟩ := List.mem_map.mp member
    exact envelope z inPath)
  have first := leakAt_add_le config pulled anc fin incPos i
    ((pinTerms config pulled anc fin).ebUp i) a
  have second := leakAt_add_le config pulled anc fin incPos i
    ((pinTerms config pulled anc fin).ebUp i + preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a) s
  have rate : (pinTerms config pulled anc fin).perIncrement * a ≥ 1 ∨ a = 0 := by
    rcases Nat.eq_zero_or_pos a with zero | pos
    · exact .inr zero
    · exact .inl (Nat.mul_pos perPos pos)
  rw [Nat.mul_add, ← Nat.add_assoc] at mono
  by_cases withdrawn : (pinTerms config pulled anc fin).withdrawnRB i = true
  · rw [Internal.inducedR_of_withdrawn _ tail i withdrawn]
    exact Nat.zero_le _
  rw [Internal.inducedR_of_not_withdrawn _ tail i (by simpa using withdrawn)]
  have leakEq : (pinTerms config pulled anc fin).slashLeak =
      (pinTerms config pulled anc fin).depthFin *
        (2 * (pinTerms config pulled anc fin).perIncrement +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
              ((pinTerms config pulled anc fin).scoreMaxFin +
                (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
            (config.INACTIVITY_SCORE_BIAS.toNat *
              (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) + 1) := rfl
  rw [leakEq, Nat.mul_left_comm s, ← Nat.mul_add]
  refine Nat.mul_le_mul_left _ ?_
  have three : 3 * (pinTerms config pulled anc fin).perIncrement * a =
      3 * ((pinTerms config pulled anc fin).perIncrement * a) := by ring
  have n1 := Nat.zero_le (preset.EFFECTIVE_BALANCE_INCREMENT.toNat * a *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
  have n2 := Nat.zero_le (preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
    ((pinTerms config pulled anc fin).scoreMaxFin +
      (pinTerms config pulled anc fin).depthFin * config.INACTIVITY_SCORE_BIAS.toNat) /
    (config.INACTIVITY_SCORE_BIAS.toNat *
      (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp slack with rfl | rfl <;>
    rcases rate with rate | rfl <;>
    simp only [Nat.add_zero, Nat.zero_add, Nat.mul_zero, Nat.zero_mul, Nat.mul_one, Nat.one_mul,
      Nat.zero_div] at mono first second three n1 ⊢ <;>
    omega

/-- A key's cap does not fall along a run. -/
theorem cap_le_cap_of_run (caps : CapOrder preset) {z y : ForkedBeaconState preset}
    (post : Run config checks z y) (i : ℕ) :
    PinTerms.capAt z i ≤ PinTerms.capAt y i := by
  unfold PinTerms.capAt
  cases found : z.state.validators.data[i]? with
  | none => simp
  | some w =>
    obtain ⟨w', found', mono⟩ := post.validatorCap_mono caps i
      w found
    simp only [found', Option.map_some, Option.getD_some]
    exact UInt64.le_iff_toNat_le.mp mono

/-- A key's effective balance at the end of a run from genesis is at most its cap there.

The cap is the one at that state. -/
theorem effective_le_cap_at {g z : ForkedBeaconState preset}
    (shared : Run config checks g z)
    (genesis : Genesis (config := config) (checks := checks) g) (caps : CapOrder preset)
    (i : ℕ) : effectiveAt z i ≤ PinTerms.capAt z i := by
  cases found : z.state.validators.data[i]? with
  | none => simp [effectiveAt, found]
  | some w =>
    have capped := DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared genesis caps
      found
    simpa [PinTerms.capAt, found] using capped

/-- On R's branch a key's effective balance is at most its cap at R. -/
theorem effective_le_cap_pulled (h : Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, z⟩)
    (post : Run config checks ⟨fork, z⟩ ⟨fork, pulled⟩) (i : ℕ) :
    effectiveAt (⟨fork, z⟩ : ForkedBeaconState preset) i ≤
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
  obtain ⟨shared⟩ := h.toFin
  exact Nat.le_trans (Internal.effective_le_cap_at (shared.append toZ) h.genesis h.caps i)
    (Internal.cap_le_cap_of_run h.caps post i)

/-- Each state of the balance path of a run on the way to R has an effective balance within R's cap.

The run starts at a state that the finalized block's state reaches, and R follows its end. -/
theorem path_le_cap_pulled (h : Setting config checks g split fin pulled anc counted V)
    {zs : BeaconState preset fork} {m : ForkedBeaconState preset}
    (toZ : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩) (rp : Run config checks ⟨fork, zs⟩ m)
    (rest : Run config checks m ⟨fork, pulled⟩) (i : ℕ) :
    ∀ z ∈ rp.balancePath,
      effectiveAt z i ≤ PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := by
  intro z member
  obtain ⟨q1, q2, -⟩ := Internal.balancePath_endpoint rp rest (Nat.le_refl _) member
  obtain ⟨zf, zs'⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run q1 q2 (Nat.le_refl _)).symm
  subst same
  exact Internal.effective_le_cap_pulled h (toZ.append q1) q2 i

/-- A state of the balance path of a run between two states of one fork is a state of that fork.

It is the end of a run from the start and the start of a run to the end. -/
theorem balancePath_state {a b : BeaconState preset fork}
    (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩) {z : ForkedBeaconState preset}
    (member : z ∈ r.balancePath) :
    ∃ zs : BeaconState preset fork, z = ⟨fork, zs⟩ ∧
      Nonempty (Run config checks ⟨fork, a⟩ ⟨fork, zs⟩) ∧
      Nonempty (Run config checks ⟨fork, zs⟩ ⟨fork, b⟩) := by
  obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint r
    (Run.nil : Run config checks ⟨fork, b⟩ ⟨fork, b⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  exact ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩

/-- The cap of a key in the registry is the activation balance, or the largest balance.

Both are a whole number of increments, and the cap is too. -/
theorem capAt_kind (h : Setting config checks g split fin pulled anc counted V)
    {z : BeaconState preset fork} (i : ℕ) (within : i < z.validators.data.size) :
    (PinTerms.capAt (⟨fork, z⟩ : ForkedBeaconState preset) i =
        preset.MIN_ACTIVATION_BALANCE.toNat ∨
      PinTerms.capAt (⟨fork, z⟩ : ForkedBeaconState preset) i =
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat) ∧
    preset.MIN_ACTIVATION_BALANCE.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
    preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  obtain ⟨w, found⟩ : ∃ w, z.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem within⟩
  obtain ⟨aMin, aMax⟩ := Internal.cap_values_aligned h.aligned
  refine ⟨?_, aMin, aMax⟩
  rw [Internal.capAt_of_found (z := (⟨fork, z⟩ : ForkedBeaconState preset)) electra found]
  split
  · exact .inr rfl
  · exact .inl rfl

/-- The states of the parts of a run cut at a step are states of the run. -/
private theorem flip_path_mem {x m n y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    {tail : Run config checks x y} (cut : (pre.snoc step).append post = tail) :
    (∀ z ∈ pre.balancePath, z ∈ tail.balancePath) ∧
      ∀ z ∈ post.balancePath, z ∈ tail.balancePath := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [cut] at path
  obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
  refine ⟨fun z member => by rw [path]; simp [Run.balancePath, member], fun z member => ?_⟩
  rw [headPost] at member
  rw [path]
  rcases List.mem_cons.mp member with rfl | inRest
  · simp [Run.balancePath, List.mem_of_mem_getLast? (Step.balancePath_ends step).2]
  · simp [headPost, inRest]

/-- A state of a run cut at a block step is a state of one of the parts. -/
private theorem flip_path_cover {x m n y : ForkedBeaconState preset} (pre : Run config checks x m)
    (step : Step config checks m n) (post : Run config checks n y)
    (notSlot : ∀ ok, step ≠ Step.slot ok) {tail : Run config checks x y}
    (cut : (pre.snoc step).append post = tail) :
    ∀ z ∈ tail.balancePath, z ∈ pre.balancePath ∨ z ∈ post.balancePath := by
  have path := Run.balancePath_append (pre.snoc step) post
  rw [cut] at path
  have block : step.balancePath = [m, n] := by
    cases step with
    | slot ok => exact absurd rfl (notSlot ok)
    | block => rfl
  obtain ⟨front, atLast⟩ := Run.balancePath_last pre
  obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
  intro z member
  rw [path] at member
  simp only [Run.balancePath, block, headPost, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, List.tail_cons] at member
  rcases member with (inPre | rfl | rfl) | inRest
  · exact .inl inPre
  · exact .inl (by rw [atLast]; simp)
  · exact .inr (by rw [headPost]; exact List.mem_cons_self)
  · exact .inr (by rw [headPost]; exact List.mem_cons_of_mem _ inRest)

/-- The effective balance of a key along a run is bounded by its capped balance.

The cap of the key may rise once, at a step that makes it compound.

The cap of a key in the registry is the activation balance, or the largest balance if it compounds.

The balance counts up to the cap, so a ceiling on it holds before and after the rise. -/
theorem effective_ceiling_flip (h : Setting config checks g split fin pulled anc counted V)
    {x y : BeaconState preset fork} (tail : Run config checks ⟨fork, x⟩ ⟨fork, y⟩)
    (invariant : Invariant x) (i : ℕ) (inside : i < x.validators.data.size)
    (ceil capHigh : ℕ)
    (capped : ∀ z ∈ tail.balancePath, effectiveAt z i ≤ PinTerms.capAt z i)
    (capCeil : ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ capHigh)
    (balanceCeil : ∀ z ∈ tail.balancePath,
      min (actualBalanceAt z i) (PinTerms.capAt z i) ≤ ceil) :
    effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i ≤
        max (effectiveAt (⟨fork, x⟩ : ForkedBeaconState preset) i)
          (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
      ((getCurrentEpoch y).toNat ≤ (getCurrentEpoch x).toNat →
        effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i =
          effectiveAt (⟨fork, x⟩ : ForkedBeaconState preset) i) ∧
      ((getCurrentEpoch x).toNat < (getCurrentEpoch y).toNat →
        effectiveAt (⟨fork, y⟩ : ForkedBeaconState preset) i ≤ ceil + preset.downwardBand) ∧
      (getCurrentEpoch x).toNat ≤ (getCurrentEpoch y).toNat := by
  have capOrder := h.caps
  have minMax := UInt64.le_iff_toNat_le.mp capOrder.compounding
  obtain ⟨-, alignedMin, alignedMax⟩ := Internal.capAt_kind h i inside
  -- a run of constant cap `c0`, below `capHigh`, is the constant-cap case
  have seg : ∀ {a b : BeaconState preset fork}
      (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩) (c0 : ℕ),
      c0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 → c0 ≤ capHigh →
      i < a.validators.data.size →
      effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i ≤ c0 →
      (∀ z ∈ r.balancePath, PinTerms.capAt z i = c0) →
      (∀ z ∈ r.balancePath, min (actualBalanceAt z i) (PinTerms.capAt z i) ≤ ceil) →
      effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i)
            (min (ceil - ceil % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) capHigh) ∧
        ((getCurrentEpoch b).toNat ≤ (getCurrentEpoch a).toNat →
          effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i =
            effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i) ∧
        ((getCurrentEpoch a).toNat < (getCurrentEpoch b).toNat →
          effectiveAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤ ceil + preset.downwardBand) ∧
        (getCurrentEpoch a).toNat ≤ (getCurrentEpoch b).toNat := by
    intro a b r c0 aligned le insideA start cap bal
    obtain ⟨p1, p2, p3, p4⟩ := Internal.Run.effective_ceiling_of_balance_ceiling r h.early h.fulu
      i insideA ceil c0 aligned start
      (fun z member => by rw [← cap z member]; exact bal z member)
      (fun z member => (cap z member).le)
    exact ⟨le_trans p1 (max_le_max le_rfl (min_le_min le_rfl le)), p2, p3, p4⟩
  -- the cap of a key in the registry is one of two values
  have kind := fun (z : BeaconState preset fork) (within : i < z.validators.data.size) =>
    (Internal.capAt_kind h i within).1
  obtain ⟨rest, atHead⟩ := Run.balancePath_head tail
  have headMem : (⟨fork, x⟩ : ForkedBeaconState preset) ∈ tail.balancePath := by
    rw [atHead]
    exact List.mem_cons_self
  obtain ⟨last, atLast⟩ := Run.balancePath_last tail
  have lastMem : (⟨fork, y⟩ : ForkedBeaconState preset) ∈ tail.balancePath := by
    rw [atLast]
    simp
  -- a run that ends with the activation cap has the activation cap throughout
  have lowRun : ∀ {a b : BeaconState preset fork} (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩),
      i < a.validators.data.size →
      PinTerms.capAt (⟨fork, b⟩ : ForkedBeaconState preset) i ≤
        preset.MIN_ACTIVATION_BALANCE.toNat →
      ∀ z ∈ r.balancePath,
        PinTerms.capAt z i = preset.MIN_ACTIVATION_BALANCE.toNat :=
    fun r within atEnd z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, ⟨r2⟩⟩ := Internal.balancePath_state r member
      have hi := Internal.cap_le_cap_of_run h.caps r2 i
      rcases kind zs (Nat.lt_of_lt_of_le within (registryGrows_of_chainSteps r1.chainSteps)) with
        low | high
      · exact low
      · omega
  -- a run that starts above the activation cap has the largest cap throughout
  have highRun : ∀ {a b : BeaconState preset fork} (r : Run config checks ⟨fork, a⟩ ⟨fork, b⟩),
      i < a.validators.data.size →
      preset.MIN_ACTIVATION_BALANCE.toNat <
        PinTerms.capAt (⟨fork, a⟩ : ForkedBeaconState preset) i →
      ∀ z ∈ r.balancePath,
        PinTerms.capAt z i = preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat :=
    fun r within atStart z member => by
      obtain ⟨zs, rfl, ⟨r1⟩, ⟨-⟩⟩ := Internal.balancePath_state r member
      have lo := Internal.cap_le_cap_of_run h.caps r1 i
      rcases kind zs (Nat.lt_of_lt_of_le within (registryGrows_of_chainSteps r1.chainSteps)) with
        low | high
      · omega
      · exact high
  by_cases compoundsEnd : preset.MIN_ACTIVATION_BALANCE.toNat <
      PinTerms.capAt (⟨fork, y⟩ : ForkedBeaconState preset) i
  · by_cases compoundsStart : preset.MIN_ACTIVATION_BALANCE.toNat <
        PinTerms.capAt (⟨fork, x⟩ : ForkedBeaconState preset) i
    · -- the cap is the largest balance along the whole run
      have all := highRun tail inside compoundsStart
      have atX := all _ headMem
      exact seg tail _ alignedMax (by have := capCeil _ headMem; omega) inside
        (by have := capped _ headMem; omega) all balanceCeil
    · -- the cap is the activation balance until the step that makes the key compound
      obtain ⟨m, n, pre, step, post, cut, flatM, largeN, -, sameEpoch⟩ :=
        Internal.Run.flip_split tail h.early h.fulu invariant i
          (by omega) compoundsEnd
      obtain ⟨mf, ms⟩ := m
      obtain ⟨nf, ns⟩ := n
      have sameM : fork = mf :=
        (Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
      have sameN : fork = nf := (Internal.fork_eq_of_run (pre.snoc step) post (Nat.le_refl _)).symm
      subst sameM sameN
      have insideM : i < ms.validators.data.size :=
        Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)
      have insideN : i < ns.validators.data.size :=
        Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps (pre.snoc step).chainSteps)
      obtain ⟨preMem, postMem⟩ := flip_path_mem pre step post cut
      obtain ⟨restPost, headPost⟩ := Run.balancePath_head post
      have nMem := postMem (⟨fork, ns⟩ : ForkedBeaconState preset)
        (by rw [headPost]; exact List.mem_cons_self)
      have capsPre := lowRun pre inside flatM
      have capsPost := highRun post insideN largeN
      have atX := kind x inside
      have atY := kind y (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tail.chainSteps))
      have capX := capCeil _ headMem
      have capY := capCeil _ lastMem
      have effX := capped _ headMem
      have effN := capped _ nMem
      have capN := capsPost _ (by
        rw [headPost]
        exact List.mem_cons_self)
      have first := seg pre _ alignedMin (by omega) inside (by omega) capsPre
        (fun z member => balanceCeil z (preMem z member))
      have second := seg post _ alignedMax (by omega) insideN (by omega) capsPost
        (fun z member => balanceCeil z (postMem z member))
      have epochN : getCurrentEpoch ns = getCurrentEpoch ms :=
        UInt64.toNat_inj.mp (sameEpoch inside)
      have keep := step_same_epoch_effective step epochN i insideM
      have epochs : (getCurrentEpoch ns).toNat = (getCurrentEpoch ms).toNat := sameEpoch inside
      obtain ⟨f1, f2, f3, f4⟩ := first
      obtain ⟨s1, s2, s3, s4⟩ := second
      refine ⟨by omega, fun back => ?_, fun before => ?_, by omega⟩
      · have e1 := f2 (by omega)
        have e2 := s2 (by omega)
        omega
      · by_cases later : (getCurrentEpoch ns).toNat < (getCurrentEpoch y).toNat
        · exact s3 later
        · have e1 := f3 (by omega)
          have e2 := s2 (by omega)
          omega
  · -- the cap is the activation balance along the whole run
    have all := lowRun tail inside (Nat.le_of_not_lt compoundsEnd)
    have atX := all _ headMem
    exact seg tail _ alignedMin (by have := capCeil _ headMem; omega) inside
      (by have := capped _ headMem; omega) all balanceCeil

/-- The cap along the balance path of a run is at most the cap at its end. -/
theorem capCeil_path {c e : ForkedBeaconState preset} (tail : Run config checks c e)
    (caps : CapOrder preset) (back : e.fork ≤ c.fork) (i : ℕ) :
    ∀ z ∈ tail.balancePath, PinTerms.capAt z i ≤ PinTerms.capAt e i := by
  intro z member
  obtain ⟨-, r2, -⟩ := Internal.balancePath_endpoint tail (Run.nil : Run config checks e e) back
    member
  exact Internal.cap_le_cap_of_run caps r2 i

/-- The effective balance of a key is at most its cap at each state of a run from a state `c`.

The run from the finalized state reaches `c` first, and `c` holds the key. -/
private theorem effective_le_cap_run (h : Setting config checks g split fin pulled anc counted V)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) {y : BeaconState preset fork}
    (r : Run config checks ⟨fork, split⟩ ⟨fork, y⟩) (i : ℕ) :
    ∀ z ∈ (fromC.append r).balancePath, effectiveAt z i ≤ PinTerms.capAt z i := fun z member => by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨zs, rfl, ⟨r1⟩, -⟩ := Internal.balancePath_state (fromC.append r) member
  exact Internal.effective_le_cap_at (shared.append (toC.append r1)) h.genesis h.caps i

/-- A key's effective balance at a state of C's run is that at `c`, or within the ceiling.

The run of C starts at a state `c` of the shared segment, which holds the key, and ends at `e`.

The cap of the key may rise once on the run, and the balance counts up to its cap at each state.

The effective balance at `e` is that at `c` if `e` is no later than `c`. -/
theorem key_stay_to (h : Setting config checks g split fin pulled anc counted V)
    {c e : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, e⟩) (i : ℕ)
    (inside : i < c.validators.data.size) (Bc : ℕ)
    (balanceC : ∀ z ∈ (fromC.append tailC).balancePath,
      min (actualBalanceAt z i) (PinTerms.capAt z i) ≤ Bc) :
    ((getCurrentEpoch e).toNat ≤ (getCurrentEpoch c).toNat ∧
        effectiveAt (⟨fork, e⟩ : ForkedBeaconState preset) i =
          effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i) ∨
      ((getCurrentEpoch c).toNat < (getCurrentEpoch e).toNat ∧
        effectiveAt (⟨fork, e⟩ : ForkedBeaconState preset) i ≤ Bc + preset.downwardBand ∧
        effectiveAt (⟨fork, e⟩ : ForkedBeaconState preset) i ≤
          max (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) i)
            (min (Bc - Bc % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
              (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i))) := by
  obtain ⟨shared⟩ := h.toFin
  have invariant : Invariant c := Run.invariant h.genesis.invariant (shared.append toC)
  obtain ⟨c1, c2, c3, -⟩ := Internal.effective_ceiling_flip h (fromC.append tailC) invariant i
    inside Bc
    (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i)
    (effective_le_cap_run h toC fromC tailC i)
    (Internal.capCeil_path (fromC.append tailC) h.caps (Nat.le_refl _) i) balanceC
  by_cases flat : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch c).toNat
  · exact .inl ⟨flat, c2 flat⟩
  · exact .inr ⟨by omega, c3 (by omega), c1⟩

open DirectSafety.Apriori.Internal in
/-- A key's balance on C's branch is at most R's balance, its debits, its credits and the gains. -/
theorem c_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {e : BeaconState preset fork}
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, e⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch e).toNat ≤ highC + 1)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (v : ValidatorIndex) (inside : v.toNat < split.validators.data.size)
    {events eventsF eventsC : List (BalanceEvent preset)} (W : ℕ)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) (Cr : ℕ)
    -- The credit allowance `Cr` covers C's net credits, and the bound includes R's sync debits.
    (credits : Internal.netScan v.toNat highC tailC +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) v.toNat highC tailC) ≤
        Cr)
    -- If the cap rises on C's run, `Cr` must cover C's gross credits instead.
    (flipCover : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
        preset.MIN_ACTIVATION_BALANCE.toNat ∧ preset.MIN_ACTIVATION_BALANCE.toNat <
          PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) v.toNat →
      Internal.credC tailC highC v.toNat + Internal.whistC tailC highC v.toNat +
        (eventsC.map (Internal.syncCredit v.toNat)).sum ≤ Cr)
    (startEff : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum + W) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (floorR : min (actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
        (events.map (Internal.syncDebit v.toNat)).sum + W)
    (debits : (events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1)))
    -- The gain is small enough to use the key's effective balance envelope to bound its rewards.
    (rateLow : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRate v.toNat + 1) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat) :
    ∃ gc, gc = min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (11 * ((Cr +
            (events.map (Internal.syncDebit v.toNat)).sum + (eventsF.map (Internal.syncDebit
              v.toNat)).sum) + W +
          min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate v.toNat +
          min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) /
          (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) * P *
        (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) ∧
      -- The gain is at most a tenth of the credits, sync debits, slack and base gain.
      10 * gc ≤ (Cr +
            (events.map (Internal.syncDebit v.toNat)).sum + (eventsF.map (Internal.syncDebit
              v.toNat)).sum) + W +
        min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).gainRate v.toNat +
        min (pinTerms config pulled anc fin).depth
          ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) ∧
      ∀ z ∈ tailC.balancePath, min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤
        min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          ((events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum) +
          (events.map (Internal.syncDebit v.toNat)).sum + W)
          (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) v.toNat) +
          Cr +
          (gc + (min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate v.toNat +
            min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat))) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  have top : min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) +
        preset.downwardBand) ≤ (pinTerms config pulled anc fin).ebUp v.toNat := by
    have key : ∀ T : ℕ, T ≤ (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) -
        (T + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) %
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat := fun T => by
      rw [← Nat.mul_div_self_eq_mod_sub_self]
      exact le_smul_ceilDiv (β := Nat) incPos
    rw [Internal.ebUp_eq config pulled anc fin electra v.toNat _ rfl]
    exact le_trans (min_le_min le_rfl (key _)) (le_max_right _ _)
  obtain ⟨i, hi⟩ : ∃ i, i = v.toNat := ⟨_, rfl⟩
  rw [← hi] at inside startEff floorR debits rateLow top credits flipCover ⊢
  obtain ⟨capI, hcap0⟩ : ∃ capI, capI =
      PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i := ⟨_, rfl⟩
  rw [← hcap0] at debits top
  obtain ⟨pd, hpd⟩ : ∃ pd,
      pd = PinTerms.dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
      PinTerms.dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1) := ⟨_, rfl⟩
  rw [← hpd] at debits top
  obtain ⟨Dp, hDp⟩ : ∃ Dp, Dp =
      (events.map (penaltyDebit i)).sum + (events.map (floorPartialDebit v)).sum := ⟨_, rfl⟩
  obtain ⟨Ds, hDs⟩ : ∃ Ds, Ds = (events.map (Internal.syncDebit i)).sum := ⟨_, rfl⟩
  obtain ⟨DsF, hDsF⟩ : ∃ DsF, DsF = (eventsF.map (Internal.syncDebit i)).sum := ⟨_, rfl⟩
  rw [← hDp] at floorR debits ⊢
  rw [← hDs] at floorR startEff ⊢
  rw [← hDsF] at startEff ⊢
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  obtain ⟨Df, hDf⟩ : ∃ Df, Df =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := ⟨_, rfl⟩
  rw [← hDf] at debits top
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth Df := ⟨_, rfl⟩
  rw [← hDf, ← hD]
  obtain ⟨e0, he0⟩ : ∃ e0, e0 = (pinTerms config pulled anc fin).ebUp i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate i := ⟨_, rfl⟩
  rw [← he0] at top startEff rateLow
  rw [← hq] at rateLow ⊢
  have hq' : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
    rw [hq, he0, hP]
    rfl
  obtain ⟨C, hC⟩ : ∃ C, C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      (11 * (Cr + Ds + DsF + W + D * q + D) / (10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) :=
    ⟨_, rfl⟩
  have startEff' : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ e0 + C := by
    refine Nat.le_trans startEff (Nat.add_le_add_left ?_ _)
    rw [hC]
    refine Nat.mul_le_mul_left _ ?_
    have le := Nat.div_le_div_right (c := 10 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      (show 10 * (DsF + Ds + W) ≤ 11 * (Cr + Ds + DsF + W + D * q + D) by omega)
    rwa [Nat.mul_div_mul_left _ _ (by norm_num : 0 < 10)] at le
  have alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [he0]
    exact Internal.ebUp_aligned h i
  obtain ⟨P', hP', rateAll⟩ := Internal.key_rate_pre h tailC near
  rw [hP'.trans hP.symm] at rateAll
  have hDle : D ≤ (pinTerms config pulled anc fin).depth := hD ▸ min_le_left _ _
  have epochs : (getCurrentEpoch e).toNat - (getCurrentEpoch split).toNat ≤ D := by
    rw [hD]
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have sizeC : i < e.validators.data.size :=
    Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps tailC.chainSteps)
  have capSC := Internal.cap_le_cap_of_run h.caps tailC i
  have capSP : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ capI :=
    hcap0 ▸ Internal.cap_le_cap_of_run h.caps toPulled i
  have capCeil := Internal.capCeil_path tailC h.caps (Nat.le_refl _) i
  have effS := Internal.effective_le_cap_at (shared.append fromFin) h.genesis h.caps i
  have minMax := UInt64.le_iff_toNat_le.mp h.caps.compounding
  obtain ⟨kindS, aMin, -⟩ := Internal.capAt_kind h i inside
  obtain ⟨kindC, -, -⟩ := Internal.capAt_kind h i sizeC
  obtain ⟨wC, foundC⟩ : ∃ w, e.validators.data[i]? = some w :=
    ⟨_, Array.getElem?_eq_getElem sizeC⟩
  have alignedC := Internal.capAt_aligned h.aligned (z := (⟨fork, e⟩ : ForkedBeaconState preset))
    electra foundC
  have startKey : 11 * D * (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum) <
      WEIGHT_DENOMINATOR.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Internal.rate_per_increment preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 D incPos (by decide) alignedE0
      (by
        rw [← hq']
        exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 hDle)) rateLow)
  by_cases flipped : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤
      preset.MIN_ACTIVATION_BALANCE.toNat ∧ preset.MIN_ACTIVATION_BALANCE.toNat <
        PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i
  · -- the cap rises on C's branch, so the run splits at the step that makes the key compound
    have cover := flipCover flipped
    have invariantS := Run.invariant h.genesis.invariant (shared.append fromFin)
    obtain ⟨m, n, pre, step, post, cut, flatM, largeN, -, sameEpoch⟩ :=
      Internal.Run.flip_split tailC h.early h.fulu invariantS i flipped.1 flipped.2
    obtain ⟨mf, ms⟩ := m
    have sameM : fork = mf :=
      (Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)).symm
    subst sameM
    have insideM : i < ms.validators.data.size :=
      Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps pre.chainSteps)
    obtain ⟨preMem, postMem⟩ := flip_path_mem pre step post cut
    have notSlot := Internal.step_flip_not_slot step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps)) i insideM
      (Nat.not_lt.mpr flatM) largeN
    have junction := Internal.step_flip_min step
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early)
      (Nat.le_trans h.fulu (fork_le_of_chainSteps pre.chainSteps))
      (Run.invariant invariantS pre) i (Nat.not_lt.mpr flatM) largeN
    have capMin : PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i =
        preset.MIN_ACTIVATION_BALANCE.toNat := by omega
    clear kindS kindC
    have capsPre : ∀ z ∈ pre.balancePath, PinTerms.capAt z i ≤
        preset.MIN_ACTIVATION_BALANCE.toNat := fun z member => by
      obtain ⟨zs, rfl, -, ⟨r2⟩⟩ := Internal.balancePath_state pre member
      exact Nat.le_trans (Internal.cap_le_cap_of_run h.caps r2 i) flatM
    have epochM : (getCurrentEpoch ms).toNat ≤ highC + 1 := by
      have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps
        ((Run.nil.snoc step).append post).chainSteps)
      simp only at this
      omega
    have fc := Internal.flip_credits_le_sources (shared.append fromFin) h.genesis pre step post
      notSlot
      h.early electra i highC epochM (by rw [cut]; exact replayedC)
    rw [cut] at fc
    have minLe : preset.MIN_ACTIVATION_BALANCE.toNat ≤ capI := capMin ▸ capSP
    obtain ⟨gc, hform, hgc, bPre, bPost, -⟩ := c_ceiling_abstract_flip pre step post h.early
      h.fulu i inside highC P preset.MIN_ACTIVATION_BALANCE.toNat
      (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i) aMin alignedC
      (by omega) (by omega) capsPre (fun z member => capCeil z (postMem z member))
      (fun z member => rateAll z (member.elim (preMem z) (postMem z))) endEpochC incPos D Cr
      (Cr + Ds + DsF) e0 C
      (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
        preset.MIN_ACTIVATION_BALANCE.toNat) W
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq' alignedE0 hC epochs
      (le_min (by rw [← capMin]; exact floorR) (min_le_right _ _)) startEff' junction
      (step_same_epoch_effective step
        (UInt64.toNat_inj.mp (sameEpoch inside)) i insideM)
      (by omega) startKey (by omega)
    refine ⟨gc, hform, hgc, fun z member => ?_⟩
    rcases flip_path_cover pre step post notSlot cut z member with inPre | inPost
    · have := bPre z inPre
      have := capsPre z inPre
      rw [capMin]
      omega
    · have := bPost z inPost
      have := capCeil z member
      rw [capMin]
      omega
  · -- the cap of C's branch is the cap at the split throughout
    have same : PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i =
        PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i := by
      rcases kindS with s1 | s1 <;> rcases kindC with f | f <;> omega
    clear kindS kindC
    obtain ⟨gc, hform, hgc, bound, -⟩ := Internal.c_ceiling_abstract tailC h.early h.fulu i inside
      highC P
      (PinTerms.capAt (⟨fork, e⟩ : ForkedBeaconState preset) i) alignedC
      (by omega) capCeil rateAll endEpochC incPos D Cr (Cr + Ds + DsF) e0 C
      (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
        (PinTerms.capAt (⟨fork, split⟩ : ForkedBeaconState preset) i)) W
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q rfl hq' alignedE0 hC epochs
      (le_min (by rw [same]; exact floorR) (by rw [same]; exact min_le_right _ _)) startEff'
      credits startKey (by omega)
    refine ⟨gc, hform, hgc, fun z member => ?_⟩
    have := bound z member
    have := capCeil z member
    omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The debits of a key on R's branch that the pin charges at the top: its passes and its partials.

The passes cost at most the leak at `M` for each epoch from the finalized state's.

The bound `M` is at least the key's effective balance at each state of the run to R.

The partials paid are at most those queued at the finalized state less those still queued at R. -/
theorem debits_le_top (h : Setting config checks g split fin pulled anc counted V)
    {s : BeaconState preset fork} (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, s⟩)
    (tail : Run config checks ⟨fork, s⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (inside : v.toNat < s.validators.data.size) (M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, s⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), tail = pre.append post →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M) :
    (events.map (penaltyDebit v.toNat)).sum + (events.map (floorPartialDebit v)).sum ≤
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt M v.toNat +
        (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
            ((getCurrentEpoch pulled).toNat + 1)) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have passes : (events.map (penaltyDebit v.toNat)).sum ≤
      ((getCurrentEpoch pulled).toNat - (getCurrentEpoch s).toNat) *
        (pinTerms config pulled anc fin).leakAt M v.toNat :=
    Internal.Run.passDebit_le tail h.early altair high endEpoch inside
    ((pinTerms config pulled anc fin).leakAt M v.toNat)
    (fun {z} pre post cut before totals => by
      obtain ⟨T, perIncrement, totalOk, perOk⟩ := totals
      obtain ⟨zf, zs⟩ := z
      have same : zf = fork := Internal.fork_eq_of_run pre post (Nat.le_refl _)
      subst same
      have startE : (getCurrentEpoch zs).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
        simp only at before
        omega
      obtain ⟨pq, pqOk⟩ :=
        Internal.quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
      exact (Internal.passRate_le_leakAt h (fromFin.append pre) startE totalOk pqOk v.toNat).trans
        (Internal.leakAt_mono config pulled anc fin v.toNat (below pre post cut)))
    replayed
  have epochs : (getCurrentEpoch pulled).toNat - (getCurrentEpoch s).toNat ≤
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
    have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
    simp only at this
    omega
  have whole := Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  have net := Internal.Run.partialDebit_net (fromFin.append tail) electra h.early high
    ((getCurrentEpoch pulled).toNat + 1) (Nat.le_succ _) (Internal.window_short h) v whole
  simp only [List.map_append, List.sum_append] at net
  have part : (events.map (floorPartialDebit v)).sum +
      PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1) ≤
        PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) := by
    rw [dueAmount_eq, dueAmount_eq]
    omega
  have := Nat.mul_le_mul_right ((pinTerms config pulled anc fin).leakAt M v.toNat) epochs
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The balance of a key at a state of R's run from the finalized state has a ceiling.

The balance counts up to the key's cap at that state. -/
private theorem prefix_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (W M : ℕ)
    -- The bound `M` is at least the key's effective balance at each state of the run.
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append post = fromFin.append tail →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M)
    {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
    (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩) (cut : r1.append r2 = fromFin.append tail)
    (inside : v.toNat < zs.validators.data.size)
    -- The floor of the state gives the ceiling, with the debits of the run after the state.
    (floorAt : ∀ {evs : List (BalanceEvent preset)}, r2.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
        -- The ceiling is R's balance, the leak at `M` over the window and the net partials.
        (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).leakAt M v.toNat +
          (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1) -
            PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
              ((getCurrentEpoch pulled).toNat + 1))) +
        -- It adds the sync debits of the two runs and the slack `W`.
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
          v.toNat)).sum + W) := by
  have whole := Apriori.Internal.balanceEvents_append fromFin tail high replayedF replayed
  obtain ⟨e1, ok1⟩ := r1.balanceEvents_ok h.early high
  obtain ⟨e2, ok2⟩ := r2.balanceEvents_ok h.early high
  have app := Apriori.Internal.balanceEvents_append r1 r2 high ok1 ok2
  rw [cut, whole] at app
  have eq : eventsF ++ events = e1 ++ e2 := Except.ok.inj app
  have floor := floorAt ok2
  have debit := Internal.debits_le_top h r1 r2 high endEpoch ok1 ok2 v inside M
    (fun pre post same => below (r1.append pre) post
      (by rw [← Run.append_assoc, ← same]; exact cut))
  have sums : (e2.map (Internal.syncDebit v.toNat)).sum ≤
      (eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit v.toNat)).sum
        := by
    have := congrArg (fun L => (L.map (Internal.syncDebit v.toNat)).sum) eq
    simp only [List.map_append, List.sum_append] at this
    omega
  omega

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The ceiling holds at every state on the balance path from `c` to R.

The state `c` is on the shared segment, and the floor holds at each state after it. -/
theorem path_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    (v : ValidatorIndex) (W M : ℕ)
    (below : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, fin⟩ ⟨fork, zs⟩)
      (post : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append post = fromFin.append tail →
      effectiveAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat ≤ M)
    {c : BeaconState preset fork} (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (fromC : Run config checks ⟨fork, c⟩ ⟨fork, split⟩) (cutC : toC.append fromC = fromFin)
    (inside : v.toNat < c.validators.data.size)
    (floorAt : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (after : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append after = fromC.append tail →
      ∀ {evs : List (BalanceEvent preset)}, after.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    ∀ z ∈ (fromC.append tail).balancePath,
      min (actualBalanceAt z v.toNat) (PinTerms.capAt z v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
              (pinTerms config pulled anc fin).leakAt M v.toNat +
            (PinTerms.dueAmount fin (Nat.le_trans (by decide) h.fulu) v.toNat
                ((getCurrentEpoch pulled).toNat + 1) -
              PinTerms.dueAmount pulled (Nat.le_trans (by decide) h.fulu) v.toNat
                ((getCurrentEpoch pulled).toNat + 1))) +
          ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum + W) := by
  intro z member
  obtain ⟨r1, r2, cutZ'⟩ := Internal.balancePath_endpoint (fromC.append tail)
    (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  have cutZ : (toC.append r1).append r2 = fromFin.append tail := by
    rw [← Run.append_assoc]
    exact (congrArg toC.append cutZ').trans (by
      show toC.append (fromC.append tail) = fromFin.append tail
      rw [← cutC, Run.append_assoc])
  exact prefix_ceiling h fromFin tail high endEpoch replayedF replayed v W M below (toC.append r1)
    r2 cutZ (Nat.le_trans inside (registryGrows_of_chainSteps r1.chainSteps)) (floorAt r1 r2 cutZ')

open DirectSafety.Apriori DirectSafety.Apriori.Internal in
/-- The effective balance of a key at each state of R's run from a state `c` is bounded. -/
theorem prefix_envelope (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tail : Run config checks ⟨fork, split⟩ ⟨fork, pulled⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    {events : List (BalanceEvent preset)} (replayed : tail.balanceEvents high = .ok events)
    -- The run from `c` is the rest of the run from the finalized state to R's, cut at `c`.
    --
    -- The finalized state is `c` for a key of the finalized registry.
    --
    -- A key that R's run creates has its first state `c` after the split.
    (v : ValidatorIndex) {c : BeaconState preset fork}
    (toC : Run config checks ⟨fork, fin⟩ ⟨fork, c⟩)
    (rest : Run config checks ⟨fork, c⟩ ⟨fork, pulled⟩)
    (cutC : toC.append rest = fromFin.append tail)
    (inside : v.toNat < c.validators.data.size) (W : ℕ)
    -- At `c` use the ceiling from the finalized balance or the floor of the actual balance there.
    (start : (effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        (pinTerms config pulled anc fin).ebUp v.toNat ∧
        effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ balanceAt fin v.toNat) ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    -- R's balance and debits bound the balance at each state, which gives the ceiling.
    (floorAt : ∀ {zs : BeaconState preset fork} (pre : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (after : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), pre.append after = rest →
      ∀ {evs : List (BalanceEvent preset)}, after.balanceEvents high = .ok evs →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
          (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤
        actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
          (evs.map (penaltyDebit v.toNat)).sum + (evs.map (Internal.syncDebit v.toNat)).sum +
          (evs.map (floorPartialDebit v)).sum + W) :
    -- After `c` add the whole increments of the sync debits and the slashing allowance `W`.
    ∀ z ∈ rest.balancePath, effectiveAt z v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          (((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
            v.toNat)).sum + W) /
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  have incPos := h.bands.1
  obtain ⟨shared⟩ := h.toFin
  -- the top of `ebUp`, `A`, and the balance ceiling, `B`, which adds the sync debits and `W` to it
  obtain ⟨A, hA⟩ : ∃ A, A = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          (pinTerms config pulled anc fin).leakAt
            (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) v.toNat +
        (PinTerms.dueAmount fin electra v.toNat ((getCurrentEpoch pulled).toNat + 1) -
          PinTerms.dueAmount pulled electra v.toNat ((getCurrentEpoch pulled).toNat + 1)) :=
      ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = A +
      ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit
        v.toNat)).sum + W) :=
    ⟨_, rfl⟩
  -- the balance ceiling at each state of that run
  have ceiling : ∀ {zs : BeaconState preset fork} (r1 : Run config checks ⟨fork, c⟩ ⟨fork, zs⟩)
      (r2 : Run config checks ⟨fork, zs⟩ ⟨fork, pulled⟩), r1.append r2 = rest →
      min (actualBalanceAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat)
        (PinTerms.capAt (⟨fork, zs⟩ : ForkedBeaconState preset) v.toNat) ≤ B := by
    intro zs r1 r2 cut
    have := prefix_ceiling h fromFin tail high endEpoch replayedF replayed v W
      (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (fun pre post _ => Internal.effective_le_cap_pulled h pre post v.toNat) (toC.append r1) r2
      (by rw [← Run.append_assoc, cut, cutC])
      (Nat.lt_of_lt_of_le inside (registryGrows_of_chainSteps r1.chainSteps))
      (fun {evs} ev => floorAt r1 r2 cut ev)
    omega
  intro z member
  obtain ⟨r1, r2, cutZ⟩ := Internal.balancePath_endpoint rest
    (Run.nil : Run config checks ⟨fork, pulled⟩ ⟨fork, pulled⟩) (Nat.le_refl _) member
  obtain ⟨zf, zs⟩ := z
  have same : fork = zf := (Internal.fork_eq_of_run r1 r2 (Nat.le_refl _)).symm
  subst same
  -- every state of the run to `zs` is the end of a run from `c` to R's
  have atPath : ∀ z' ∈ r1.balancePath, ∃ (zs' : BeaconState preset fork)
      (s1 : Run config checks ⟨fork, c⟩ ⟨fork, zs'⟩)
      (s2 : Run config checks ⟨fork, zs'⟩ ⟨fork, pulled⟩),
      z' = ⟨fork, zs'⟩ ∧ s1.append s2 = rest := by
    intro z' member'
    obtain ⟨s1, s2, cutS⟩ := Internal.balancePath_endpoint r1 r2 (Nat.le_refl _) member'
    obtain ⟨zf', zs'⟩ := z'
    have same' : fork = zf' := (Internal.fork_eq_of_run s1 s2 (Nat.le_refl _)).symm
    subst same'
    exact ⟨zs', s1, s2, rfl, cutS.trans cutZ⟩
  have bound := Internal.effective_ceiling_flip h r1
    (Run.invariant h.genesis.invariant (shared.append toC)) v.toNat inside B
    (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, -⟩ := atPath z' member'
      exact Internal.effective_le_cap_at (shared.append (toC.append s1)) h.genesis h.caps
        v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, -⟩ := atPath z' member'
      exact Internal.cap_le_cap_of_run h.caps s2 v.toNat)
    (fun z' member' => by
      obtain ⟨zs', s1, s2, rfl, cut⟩ := atPath z' member'
      exact ceiling s1 s2 cut)
  obtain ⟨origin, -⟩ := bound
  -- a start within the floor of the balance at `c` is within the floor of the balance ceiling
  have startLe : effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
      (pinTerms config pulled anc fin).ebUp v.toNat ∨
      effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤
        min (B - B % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
          (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat) := by
    rcases start with ⟨within, -⟩ | floorC
    · exact Or.inl within
    · refine Or.inr (Nat.le_min.mpr ⟨?_, ?_⟩)
      · have atC := ceiling (Run.nil : Run config checks ⟨fork, c⟩ ⟨fork, c⟩) rest
          (Run.nil_append _)
        have capped := Internal.effective_le_cap_at (shared.append toC) h.genesis h.caps
          v.toNat
        have aligned := FloorTrace.effective_aligned (shared.append toC) h.genesis h.aligned v.toNat
        have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
          (show effectiveAt (⟨fork, c⟩ : ForkedBeaconState preset) v.toNat ≤ B by omega)
        omega
      · have capped := Internal.effective_le_cap_at (shared.append toC) h.genesis h.caps
          v.toNat
        have rise := Internal.cap_le_cap_of_run h.caps rest v.toNat
        omega
  -- the envelope `ebUp` and the rounding
  obtain ⟨t, ht⟩ :
      ∃ t, t = A + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 := ⟨_, rfl⟩
  have up := Internal.ebUp_eq config pulled anc fin electra v.toNat t (by omega)
  have floorRound := rounded_add_floor_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat A
    ((eventsF.map (Internal.syncDebit v.toNat)).sum + (events.map (Internal.syncDebit v.toNat)).sum
      + W) incPos
  have rounded := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (show A + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1 ≤ t by omega)
  have upper : min (PinTerms.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) v.toNat)
      (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        (pinTerms config pulled anc fin).ebUp v.toNat := by
    rw [up]
    exact Nat.le_max_right _ _
  rw [← hB] at floorRound
  omega

/-- A cap at a state of the Electra forks is at most the largest cap. -/
theorem capAt_le_capMax {z : ForkedBeaconState preset} (caps : CapOrder preset)
    (electra : .pectra ≤ z.fork) (i : ℕ) :
    PinTerms.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := by
  cases found : z.state.validators.data[i]? with
  | none => simp [PinTerms.capAt, found]
  | some w =>
    have compounding := UInt64.le_iff_toNat_le.mp caps.compounding
    rw [Internal.capAt_of_found electra found]
    split <;> omega

/-- A key with an assigned exit epoch is inactive at every epoch from the exit on, along a run.

The run keeps an assigned exit epoch. -/
theorem inactive_from_exit {x y : ForkedBeaconState preset} (tail : Run config checks x y)
    {i : ℕ} {v : Validator} (found : x.state.validators.data[i]? = some v)
    (assigned : v.exitEpoch ≠ FAR_FUTURE_EPOCH) {e : Epoch} (reached : v.exitEpoch ≤ e) :
    isActiveAt y.state e i = false := by
  obtain ⟨later, foundLater, kept⟩ := tail.registryLifecycle.validators i v found
  have inactive : isActiveValidator later e = false := by
    unfold isActiveValidator
    simp
    exact fun _ => by rw [kept.exitEpoch assigned]; exact reached
  simp [isActiveAt, foundLater, inactive]

/-- A key that exited before the finalized epoch stays within its finalized balance and credits. -/
theorem exited_ceiling (h : Setting config checks g split fin pulled anc counted V)
    {a : BeaconState preset fork} (run : Run config checks ⟨fork, fin⟩ ⟨fork, a⟩) (high : ℕ)
    (endEpoch : (getCurrentEpoch a).toNat ≤ high + 1) (i : ℕ) {w : Validator}
    (found : fin.validators.data[i]? = some w)
    -- The key is idle from the finalized block on.
    --
    -- Its exit is kept, and the previous epoch of each later state is at or past it.
    (exited : w.exitEpoch.toNat + 1 ≤ (getCurrentEpoch fin).toNat) (Cr : ℕ)
    (credits : Internal.netScan i high run +
      (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high run) ≤ Cr) :
    -- The ceiling on the balance is the finalized balance and the credits of the run.
    --
    -- Rounding adds the whole increments that cover the credits.
    effectiveAt (⟨fork, a⟩ : ForkedBeaconState preset) i ≤
      max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        ((actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i %
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
            ((Cr + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  have incPos := h.bands.1
  have inside : i < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  obtain ⟨shared⟩ := h.toFin
  have alignedMax := (Internal.cap_values_aligned h.aligned).2
  have startCap := Internal.effectiveAt_le_capMax shared h.genesis h.caps i
  have capCeil : ∀ z ∈ run.balancePath,
      PinTerms.capAt z i ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat := fun z member => by
    obtain ⟨r1, -, -⟩ := Internal.balancePath_endpoint run
      (Run.nil : Run config checks ⟨fork, a⟩ ⟨fork, a⟩) (Nat.le_refl _) member
    exact Internal.capAt_le_capMax h.caps (Nat.le_trans (Nat.le_trans (by decide) h.fulu)
      (fork_le_of_chainSteps r1.chainSteps)) i
  have notFar : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  -- An idle key earns no epoch reward, so the credit ceiling of the run needs no rate.
  have idle : ∀ z ∈ run.balancePath,
      i.toUInt64 ∉ getActiveValidatorIndices z.state (getPreviousEpoch z.state) := by
    intro z member active
    obtain ⟨r1, r2, -⟩ := Internal.balancePath_endpoint run
      (Run.nil : Run config checks ⟨fork, a⟩ ⟨fork, a⟩) (Nat.le_refl _) member
    obtain ⟨zf, zs⟩ := z
    have within := BeaconState.registryWithinLimit_of_lt
      (Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early) zs
    have index : i.toUInt64.toNat = i := toNat_toUInt64_of_lt within
      (Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp found).1 r1.registryLifecycle.size_le)
    have previous := getPreviousEpoch_toNat zs
    have epochs := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps r1.chainSteps)
    simp only at epochs
    have inactive := Internal.inactive_from_exit r1 found notFar (e := getPreviousEpoch zs)
      (UInt64.le_iff_toNat_le.mpr (by omega))
    obtain ⟨v, foundV, isActive⟩ := (mem_getActiveValidatorIndices within).mp active
    rw [index] at foundV
    have := isActiveAt_eq_true_iff.mpr ⟨v, foundV, isActive⟩
    rw [inactive] at this
    exact Bool.false_ne_true this
  obtain ⟨cb, hcb⟩ : ∃ cb, cb = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat + (Internal.netScan i high run +
        (Internal.creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high run)) := ⟨_,
          rfl⟩
  have cbE : ∀ E, Internal.creditBound run i high E 0
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat = cb := fun E => by
    rw [hcb]
    unfold Internal.creditBound
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.zero_div, Nat.add_zero]
    omega
  obtain ⟨E, hE⟩ : ∃ E, E = max (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
      (min preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
        (cb - cb % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := ⟨_, rfl⟩
  have ceiling := Internal.key_credit_ceiling run h.early h.fulu i inside high 0 E alignedMax
    startCap
    capCeil (fun z member => .inl (idle z member)) endEpoch
    (by rw [cbE]; exact le_of_eq hE.symm)
  rw [cbE] at ceiling
  have mono := rounded_mono preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (show cb ≤ actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i + Cr by
      have := Nat.min_le_left (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat
      omega)
  have split := rounded_add_ceil_le preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i) Cr incPos
  exact Nat.le_trans ceiling (max_le_max (Nat.le_refl _)
    (Nat.le_trans (Nat.min_le_left _ _) (Nat.le_trans mono split)))

/-- A step that charges a key has it without an exit at its start and with one at its end. -/
theorem charge_exits {m n : ForkedBeaconState preset} (step : Step config checks m n)
    {v : ℕ} (charged : step.departureCharges.any (·.index == v) = true) :
    ∃ u w, m.state.validators.data[v]? = some u ∧ n.state.validators.data[v]? = some w ∧
      (∀ u', m.state.validators.data[v]? = some u' → u'.exitEpoch = FAR_FUTURE_EPOCH) ∧
      w.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  obtain ⟨c, member, same⟩ := List.any_eq_true.mp charged
  obtain ⟨⟨u, j⟩, found, picked⟩ := List.mem_filterMap.mp member
  have found : m.state.validators.data[j]? = some u := by
    simpa only [List.mem_zipIdx_iff_getElem?, Array.getElem?_toList] using found
  dsimp only at picked
  split at picked
  · cases picked
  · rename_i w located
    split at picked
    · rename_i assigned
      cases Option.some.inj picked
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at assigned
      have : j = v := by simpa using same
      subst this
      refine ⟨u, w, found, located, ?_, assigned.2⟩
      intro u' read
      obtain rfl := Option.some.inj (found.symm.trans read)
      exact assigned.1
    · cases picked

/-- A step that charges a key has it in the registry at its start. -/
private theorem charge_inside {m n : ForkedBeaconState preset} (step : Step config checks m n)
    {v : ℕ} (charged : step.departureCharges.any (·.index == v) = true) :
    v < m.state.validators.data.size :=
  let ⟨_, _, found, _⟩ := Internal.charge_exits step charged
  (Array.getElem?_eq_some_iff.mp found).1

/-- The epoch rewards of a key over a run are at most the rate for each epoch of the run.

The steps from the key's departure charge on count, and the key is in the registry from then.

So the bound is needed for a step only when the key is in the registry at its start. -/
private theorem riseScan_snd_le (v high R : ℕ) {x : ForkedBeaconState preset}
    {y : ForkedBeaconState preset} (tail : Run config checks x y)
    (bound : ∀ {m n : ForkedBeaconState preset} (step : Step config checks m n),
      tail.Contains step → v < m.state.validators.data.size →
        Internal.epochRewards v step ≤
          ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) * R) :
    (Internal.riseScan (config := config) (checks := checks) v high tail).2 ≤
      ((getCurrentEpoch y.state).toNat - (getCurrentEpoch x.state).toNat) * R := by
  induction tail with
  | nil => simp [Internal.riseScan]
  | @snoc m n pre step ih =>
    have prior := ih fun inner member inside => bound inner (.earlier member step) inside
    have xm := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have mn := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (Run.nil.snoc step : Run config checks m n).chainSteps)
    simp only [Internal.riseScan]
    split
    · rename_i cond
      have inside : v < m.state.validators.data.size := by
        rcases cond.1 with seen | charged
        · obtain ⟨c, member, same⟩ := (Internal.riseScan_fst v high pre).mp seen
          obtain ⟨w, found, -, -⟩ := pre.departure_charge_exit c member
          rw [same] at found
          exact (Array.getElem?_eq_some_iff.mp found).1
        · exact charge_inside step charged
      have one := bound step (.last pre step) inside
      have split : (getCurrentEpoch n.state).toNat - (getCurrentEpoch x.state).toNat =
          ((getCurrentEpoch m.state).toNat - (getCurrentEpoch x.state).toNat) +
            ((getCurrentEpoch n.state).toNat - (getCurrentEpoch m.state).toNat) := by omega
      rw [split, Nat.add_mul]
      omega
    · exact prior.trans (Nat.mul_le_mul_right _ (by omega))

/-- The rise of a charged key on C's branch is one band and the depth's gains at the largest rate.

The gains are the epoch rewards of the key after its exit starts, over the epochs of the run. -/
theorem riseQ_le (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC v : ℕ) :
    Internal.riseQ tailC highC v ≤ preset.upwardBand + (pinTerms config pulled anc fin).depth *
      (pinTerms config pulled anc fin).gainRateMax := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨fromFin⟩ := h.fromFin
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have called := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have near := h.near
  unfold Internal.riseQ
  split
  swap
  · exact Nat.zero_le _
  obtain ⟨P, -, gainLe, rateAll⟩ := Internal.pin_rate_exists h
  have scan := riseScan_snd_le (config := config) (checks := checks) v highC
    (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) tailC
    (fun {m n} step member inside => by
      obtain ⟨pre, post, _, mEarly, mEpoch⟩ :=
        DirectSafety.Apriori.Internal.Run.contains_step_facts member h.early
      have same := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
      obtain ⟨mf, ms⟩ := m
      obtain rfl : mf = fork := same
      have nEarly : n.fork < .glamsterdam :=
        Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
      exact Internal.epochRewards_le step altair nEarly v (Or.inl inside)
        preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat P
        (.inr (Internal.effectiveAt_le_capMax (shared.append (fromFin.append pre)) h.genesis
          h.caps v))
        (.inr (rateAll (fromFin.append pre) (by simp only at mEpoch ⊢; omega))))
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  have epochs : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤
      (pinTerms config pulled anc fin).depth := by omega
  calc _ ≤ preset.upwardBand + (pinTerms config pulled anc fin).depth *
        (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
          P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) :=
        Nat.add_le_add_left (scan.trans (Nat.mul_le_mul_right _ epochs)) _
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ gainLe) _

/-- A low key is in the registry. -/
theorem lowB_found (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ} (low : (pinTerms config state ancestor finalizedState).lowB i = true) :
    ∃ w, state.validators.data[i]? = some w := by
  refine Internal.validator_of_flag (f := fun v =>
    decide (ancestor.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat) &&
      decide (v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat)) (.inl ?_)
  exact (of_decide_eq_true low).1

/-- A key is low if it is activated, not withdrawable at R, and its low bound is below the floor. -/
theorem lowB_intro (config : Config)
    (state ancestor finalizedState : BeaconState preset fork)
    {i : ℕ}
    (first : ((state.validators.data[i]?).any fun v =>
      decide (ancestor.finalizedCheckpoint.epoch.toNat < v.withdrawableEpoch.toNat) &&
        decide (v.activationEpoch.toNat ≤ (getCurrentEpoch state).toNat)) = true)
    (low : (pinTerms config state ancestor finalizedState).lowEB i <
      (pinTerms config state ancestor finalizedState).newKeyFloor) :
    (pinTerms config state ancestor finalizedState).lowB i = true :=
  decide_eq_true ⟨first, low⟩

/-- A key whose exit starts on a run is activated at the start of the step that starts it.

The hypothesis `site` is the split of the run at the step that assigns the charged exit.

The transition can assign an exit only after activation has been assigned. -/
theorem charge_activated {x y : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (tail : Run config checks x y) (charge : DepartureCharge)
    (site : ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧
          v.exitEpoch = FAR_FUTURE_EPOCH ∧ w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat) :
    ∃ a b, ∃ pre : Run config checks x a, ∃ step : Step config checks a b,
      ∃ post : Run config checks b y, (pre.snoc step).append post = tail ∧
        ∃ v w, a.state.validators.data[charge.index]? = some v ∧
          b.state.validators.data[charge.index]? = some w ∧ v.exitEpoch = FAR_FUTURE_EPOCH ∧
          w.exitEpoch ≠ FAR_FUTURE_EPOCH ∧ v.activationEpoch ≤ getCurrentEpoch a.state ∧
          charge.amount = v.effectiveBalance.toNat ∧ charge.epoch = w.exitEpoch.toNat := by
  obtain ⟨a, b, pre, step, post, split, v, w, found, later, unset, set, amount, epoch⟩ := site
  exact ⟨a, b, pre, step, post, split, v, w, found, later, unset, set,
    step.chainStep.exit_assigned_activated
      (Nat.le_trans electra (fork_le_of_chainSteps pre.chainSteps))
      found later unset set, amount, epoch⟩

/-- A charged key activated at the finalized state, and by R's epoch at C, is active at R.

Its activation at R is that of C: an assigned activation does not change.

It is not withdrawable by the finalized epoch at R, since then it would be exited on both branches.

The split fixes its exit and withdrawable epochs. -/
theorem activated_key_at_pulled (h : Setting config checks g split fin pulled anc counted V)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (v : ValidatorIndex)
    (activatedBy : ∀ c, counted.validators.data[v.toNat]? = some c →
      c.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat) {w : Validator}
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (found : fin.validators.data[v.toNat]? = some w)
    (activated : w.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ((pulled.validators.data[v.toNat]?).any fun u =>
      decide (anc.finalizedCheckpoint.epoch.toNat < u.withdrawableEpoch.toNat) &&
        decide (u.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat)) = true := by
  classical
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have near := h.near
  -- the key at the split, at R and at C, with the activation of the finalized state
  obtain ⟨x, foundSplit, lifeFin⟩ := fromFin.registryLifecycle.validators v.toNat w found
  obtain ⟨u, foundPulled, lifeSplit⟩ := toPulled.registryLifecycle.validators v.toNat x foundSplit
  have actSplit : x.activationEpoch = w.activationEpoch := lifeFin.activationEpoch activated
  have actPulled : u.activationEpoch = w.activationEpoch :=
    (lifeSplit.activationEpoch (actSplit ▸ activated)).trans actSplit
  obtain ⟨c, foundCounted, lifeAll⟩ :=
    (fromFin.append tailC).registryLifecycle.validators v.toNat w found
  have actCounted : c.activationEpoch = w.activationEpoch := lifeAll.activationEpoch activated
  have atPulled : u.activationEpoch.toNat ≤ (getCurrentEpoch pulled).toNat := by
    rw [actPulled, ← actCounted]
    exact activatedBy c foundCounted
  -- the key is not withdrawable by the finalized epoch at R, since it has a charge on C's run
  have settled : anc.finalizedCheckpoint.epoch.toNat < u.withdrawableEpoch.toNat := by
    by_contra not
    obtain ⟨d, member, index⟩ := charged
    exact Internal.no_charge_of_settled h tailC
      (Array.getElem?_eq_some_iff.mp foundSplit).1 foundPulled (by omega) d member index
  simp [foundPulled, settled, atPulled]

end Internal

section LowBound

open DirectSafety.Apriori DirectSafety.Apriori.Internal

namespace Internal

/-- The penalties of one key in one step fit a rate read at the start of the step. -/
private theorem step_passDebit_le {m n : ForkedBeaconState preset} (step : Step config checks m n)
    (early : n.fork < .glamsterdam) (altair : .altair ≤ m.fork) (high : ℕ)
    (endEpoch : (getCurrentEpoch n.state).toNat ≤ high + 1)
    (startEpoch : (getCurrentEpoch m.state).toNat ≤ high + 1) {v : ℕ}
    (inside : v < m.state.validators.data.size) (pen : ℕ)
    (rate : (getCurrentEpoch m.state).toNat < (getCurrentEpoch n.state).toNat →
      (∃ total perIncrement, getTotalActiveBalance m.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) →
      Internal.passPenaltyRate config m v ≤ pen)
    {evs : List (BalanceEvent preset)} (replayed : step.balanceEvents = .ok evs) :
    (evs.map (penaltyDebit v)).sum ≤ pen := by
  have run : (Run.nil.snoc step : Run config checks m n).balanceEvents high = .ok evs := by
    simp [Run.balanceEvents, startEpoch, replayed, bind, Except.bind, pure, Except.pure]
  have bound := Internal.segment_passDebit_le_guarded (Run.nil.snoc step : Run config checks m n)
    early
    altair high endEpoch
    (fun {u w} step' member => by
      cases member with
      | last => rfl
      | earlier inner _ => cases inner)
    inside pen
    (fun {z} pre ok split before total => by
      injection split with middle _ _ _
      subst middle
      exact rate before total) run
  refine bound.trans ?_
  split <;> simp

/-- A rate that is linear in the effective balance bounds the two terms of a leak.

It bounds the leak of an aligned balance, and the leak of any balance an increment above, less one.
-/
private theorem leak_linear (inc pi score depth bias quotient : ℕ) (incPos : 0 < inc) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧
      (∀ eb : ℕ, inc ∣ eb →
        2 * (eb / inc * pi) + eb * (score + depth * bias) / (bias * quotient) ≤ ρn * eb / ρd) ∧
      ∀ x : ℕ, ρn * x ≤ ρd * (2 * ((x + inc) / inc * pi) +
        (x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by
  have under : ∀ x : ℕ, x ≤ inc * ((x + inc) / inc) := fun x => by
    rw [Nat.add_div_right _ incPos]
    exact (Nat.lt_mul_div_succ x incPos).le
  by_cases zero : bias * quotient = 0
  · refine ⟨2 * pi, inc, incPos, fun eb aligned => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := aligned
      simp only [zero, Nat.div_zero, Nat.add_zero]
      rw [Nat.mul_div_cancel_left _ incPos, show 2 * pi * (inc * u) = inc * (2 * pi * u) by ring,
        Nat.mul_div_cancel_left _ incPos]
      ring_nf
      exact le_refl _
    · simp only [zero, Nat.div_zero, Nat.add_zero]
      calc 2 * pi * x ≤ 2 * pi * (inc * ((x + inc) / inc)) := Nat.mul_le_mul_left _ (under x)
        _ = inc * (2 * ((x + inc) / inc * pi)) := by ring
        _ ≤ inc * (2 * ((x + inc) / inc * pi) + 1) := Nat.mul_le_mul_left _ (by omega)
  · have positive : 0 < bias * quotient := Nat.pos_of_ne_zero zero
    refine ⟨2 * pi * (bias * quotient) + (score + depth * bias) * inc, inc * (bias * quotient),
      Nat.mul_pos incPos positive, fun eb aligned => ?_, fun x => ?_⟩
    · obtain ⟨u, rfl⟩ := aligned
      have lhs : 2 * (inc * u / inc * pi) + inc * u * (score + depth * bias) / (bias * quotient) =
          2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
        rw [Nat.mul_div_cancel_left _ incPos]
        congr 2
        ring
      have rhs : (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) /
          (inc * (bias * quotient)) =
          2 * (u * pi) + (score + depth * bias) * inc * u / (bias * quotient) := by
        rw [show (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * (inc * u) =
          inc * ((bias * quotient) * (2 * (u * pi)) + (score + depth * bias) * inc * u) by ring,
          Nat.mul_div_mul_left _ _ incPos, Nat.mul_add_div positive]
      rw [lhs, rhs]
    · have first := Nat.mul_le_mul_left (bias * quotient * (2 * pi)) (under x)
      have second : (score + depth * bias) * x ≤
          bias * quotient * ((x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by
        have := Nat.lt_mul_div_succ ((x + inc) * (score + depth * bias)) positive
        have mono : (score + depth * bias) * x ≤ (x + inc) * (score + depth * bias) :=
          calc (score + depth * bias) * x = x * (score + depth * bias) := Nat.mul_comm _ _
            _ ≤ (x + inc) * (score + depth * bias) :=
              Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
        omega
      have third := Nat.mul_le_mul_left inc second
      calc (2 * pi * (bias * quotient) + (score + depth * bias) * inc) * x
          = bias * quotient * (2 * pi) * x + inc * ((score + depth * bias) * x) := by ring
        _ ≤ bias * quotient * (2 * pi) * (inc * ((x + inc) / inc)) +
            inc * (bias * quotient *
              ((x + inc) * (score + depth * bias) / (bias * quotient) + 1)) :=
          Nat.add_le_add first third
        _ = inc * (bias * quotient) * (2 * ((x + inc) / inc * pi) +
            (x + inc) * (score + depth * bias) / (bias * quotient) + 1) := by ring

/-- The pass premise of the potential floor, from a rate that is linear in aligned balances. -/
private theorem pass_of_leak (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    (i : ValidatorIndex) (initial : ∃ val, fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = whole → ∀ evs, step.balanceEvents = .ok evs →
      (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨val, initial⟩ := initial
  have altair : .altair ≤ fork := Nat.le_trans (by decide) h.fulu
  intro m n pre step post cut evs ok
  have same := Internal.fork_eq_of_run pre ((Run.nil.snoc step).append post) (Nat.le_refl _)
  have startE : (getCurrentEpoch m.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps ((Run.nil.snoc step).append post).chainSteps)
    simp only at this
    omega
  have endE : (getCurrentEpoch n.state).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
    have := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
    simp only at this
    omega
  have nEarly : n.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps post.chainSteps) h.early
  have mSize := registryGrows_of_chainSteps pre.chainSteps
  obtain ⟨mf, ms⟩ := m
  obtain rfl : mf = fork := same
  have inside : i.toNat < ms.validators.data.size :=
    Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp initial).1 mSize
  refine step_passDebit_le step nEarly altair (getCurrentEpoch pulled).toNat endE startE inside
    (ρn * effectiveAt ⟨mf, ms⟩ i.toNat / ρd) (fun _ total => ?_) ok
  obtain ⟨T, perIncrement, totalOk, perOk⟩ := total
  obtain ⟨pq, pqOk⟩ :=
    Internal.quarter_base_ok h.facts perOk ((getTotalActiveBalance pulled).toOption.getD 0)
  have rate := Internal.passRate_le_leakAt h pre startE totalOk pqOk i.toNat
  exact rate.trans (leaky _ (Nat.dvd_of_mod_eq_zero
    (FloorTrace.effective_aligned (shared.append pre) h.genesis h.aligned i.toNat)))

/-- The floor of the potential, in naturals.

It is the closed form less the debits, the band and the carried shortfall. -/
private def potentialFloor (ρn ρd K X band slack cost : ℕ) : ℕ :=
  ((ρd - ρn * K) * (X + band) - ρn * slack) / ρd - (band + cost)

/-- The partial withdrawal allowance covers the key's finalized queue entries due by the cutoff. -/
private theorem partials_le_due (electra : .pectra ≤ fork) (v : ValidatorIndex) :
    ((((fin.pendingPartialWithdrawals electra).data.toList.filter
        fun entry => decide (entry.validatorIndex = v)).filter
          (fun entry => entry.withdrawableEpoch.toNat ≤ (getCurrentEpoch pulled).toNat + 1)).map
            (·.amount.toNat)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  rw [← dueAmount_eq fin electra v]
  refine le_trans ?_ (le_max_left (_ : ℕ) _)
  dsimp only
  simp only [PinTerms.dueAmount, electra, ↓reduceDIte]
  exact le_rfl

/-- The partials paid to a key over a run from the finalized state are at most those due.

The run ends by the call's cutoff, which is within the withdrawal delay of the finalized state. -/
private theorem run_partials_le_due (h : Setting config checks g split fin pulled anc counted V)
    {e : BeaconState preset fork} (whole : Run config checks ⟨fork, fin⟩ ⟨fork, e⟩)
    (near : (getCurrentEpoch e).toNat ≤ (getCurrentEpoch pulled).toNat + 1) (v : ValidatorIndex)
    {events : List (BalanceEvent preset)}
    (replayed : whole.balanceEvents (getCurrentEpoch pulled).toNat = .ok events) :
    (events.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat := by
  have electra : .pectra ≤ fork := Nat.le_trans (by decide) h.fulu
  exact (Internal.Run.partialDebit_le whole electra h.early (getCurrentEpoch pulled).toNat
    ((getCurrentEpoch pulled).toNat + 1) near (Internal.window_short h) v replayed).trans
    (partials_le_due electra v)

/-- The charge of a key on C's run is its effective balance at a state where its exit is unset.

The state is the stop of the charge.

The runs to it and from it make C's run from the finalized block. -/
private theorem exit_stop (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (v : ℕ)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v →
      c.epoch ≤ (getCurrentEpoch counted).toNat) :
    ∃ (sd : ForkedBeaconState preset) (pre : Run config checks ⟨fork, fin⟩ sd)
        (post : Run config checks sd ⟨fork, counted⟩),
      pre.append post = fromFin.append tailC ∧
      (∀ w, sd.state.validators.data[v]? = some w → w.exitEpoch = FAR_FUTURE_EPOCH) ∧
      Internal.exitQ tailC v = effectiveAt sd v := by
  classical
  obtain ⟨c0, member0, index0, -, amount0⟩ : ∃ c ∈ tailC.departureCharges,
      c.index = v ∧ c.epoch ≤ (getCurrentEpoch counted).toNat ∧ Internal.exitQ tailC v = c.amount :=
        by
    obtain ⟨c, mem, idx⟩ := charged
    rcases Internal.exitQ_cases tailC v with ⟨none, -⟩ | found
    · exact absurd (epochLe c mem idx) (none c mem idx)
    · exact found
  obtain ⟨stop, chosen⟩ := Internal.stop_of_charge fromFin tailC member0 index0
  have selected := stop.selected
  rw [chosen] at selected
  obtain ⟨-, -, amount, next, assignedStep, rest, -, -, vv, w, atStop, -,
    unset, -, -⟩ := selected
  refine ⟨stop.state, stop.pre, stop.post, stop.split, fun w' found => ?_, by rw [amount0, amount]⟩
  have same := Option.some.inj (found.symm.trans atStop)
  subst same
  exact unset

/-- The key's effective balance at its exit call, from the potential floor of the run to the call.

The key is activated at the finalized state, charged on the run from the split, and exits by C. -/
private theorem exitQ_potential (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat)
    (ρn ρd : ℕ)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb v.toNat ≤ ρn * eb / ρd) :
    min (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (min (withdrawalMaxEffectiveBalance preset fork val).toNat
          (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (Internal.syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) -
            potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
              (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
                (withdrawalMaxEffectiveBalance preset fork val).toNat)
              preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
                actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              ((events.map (Internal.syncDebit v.toNat)).sum +
                (pinTerms config pulled anc fin).partialsDue v.toNat) %
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      Internal.exitQ tailC v.toNat := by
  obtain ⟨sd, pre, post, cut, far, amount⟩ := exit_stop fromFin tailC v.toNat charged epochLe
  rw [amount]
  have nearC := h.near
  have same := Internal.fork_eq_of_run pre post (Nat.le_refl _)
  obtain ⟨sf, se⟩ := sd
  obtain rfl : fork = sf := same.symm
  have toCounted := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps post.chainSteps)
  simp only at toCounted
  have near : (getCurrentEpoch se).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by omega
  obtain ⟨before, beforeOk, isPrefix⟩ := Run.balanceEvents_prefix pre post
    (getCurrentEpoch pulled).toNat events (by rw [cut]; exact replayed)
  have clean : ∀ w, se.validators.data[v.toNat]? = some w → w.slashed = false := by
    obtain ⟨shared⟩ := h.toFin
    intro w found
    by_contra slashed
    exact run_slashed_exit_assigned (shared.append pre) h.genesis h.caps (Internal.Setting.delay h)
        v.toNat w found (by simpa using slashed)
        (far w found)
  have retained : ∀ {m n : ForkedBeaconState preset} (b : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (a : Run config checks n ⟨fork, se⟩),
      (b.snoc step).append a = pre → ∀ w, n.state.validators.data[v.toNat]? = some w →
      (getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat := by
    intro m n b step a _ w found
    obtain ⟨last, located, kept⟩ := a.registryLifecycle.validators v.toNat w found
    by_cases e : w.exitEpoch = FAR_FUTURE_EPOCH
    · rw [e]
      exact .inl (getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled)
    · exact absurd ((kept.exitEpoch e).symm.trans (far last located)) e
  have syncLe : (before.map (Internal.syncDebit v.toNat)).sum ≤ (events.map (Internal.syncDebit
    v.toNat)).sum :=
    (isPrefix.sublist.map (Internal.syncDebit v.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
  have partialLe : (before.map (floorPartialDebit v)).sum ≤
      (pinTerms config pulled anc fin).partialsDue v.toNat :=
    run_partials_le_due h pre near v beforeOk
  have final := Internal.cfloor_endpoint h se pre near beforeOk v val initial clean retained
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) ρn ρd
    (potentialFloor ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat)
      preset.downwardBand (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      ((before.map (Internal.syncDebit v.toNat)).sum + (before.map (floorPartialDebit v)).sum))
    (by omega)
    (pass_of_leak h pre near v ⟨val, initial⟩ ρn ρd leaky)
    (fun a D k hk hD closed => by
      have mono : ρd - ρn * ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat) ≤
          ρd - ρn * k :=
        Nat.sub_le_sub_left (Nat.mul_le_mul_left _ (hk.trans (Nat.sub_le_sub_right toCounted _))) _
      have step2 := (Nat.mul_le_mul_right _ mono).trans closed
      have step3 := Nat.div_le_of_le_mul (Nat.sub_le_of_le_add step2)
      unfold potentialFloor
      omega)
    pre Run.nil rfl
  refine le_trans (min_le_min le_rfl (min_le_min le_rfl (rounded_mono _ ?_))) final
  unfold potentialFloor
  omega

/-- The leak of an aligned effective balance is at most a rate times it.

The rate times any balance is at most the leak an increment above, plus one. -/
private theorem leak_rate (config : Config) (pulled anc fin : BeaconState preset fork)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) (v : ℕ) :
    ∃ ρn ρd : ℕ, 0 < ρd ∧
      (∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
        (pinTerms config pulled anc fin).leakAt eb v ≤ ρn * eb / ρd) ∧
      ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
        (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v + 1) := by
  obtain ⟨ρn, ρd, positive, bound, above⟩ := leak_linear preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat
    (if altair : .altair ≤ fork then
      (((fin.inactivityScores altair).data[v]?).map (·.toNat)).getD 0 else 0)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    config.INACTIVITY_SCORE_BIAS.toNat
    (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat incPos
  exact ⟨ρn, ρd, positive, fun eb aligned => bound eb aligned, fun x => above x⟩

/-- The rate times the epochs and the base is at most the leak for each epoch, plus one.

The leak is read an increment above the base. -/
private theorem rate_cost (ρn ρd K L Y : ℕ) (first : ρn * Y ≤ ρd * (L + 1)) :
    ρn * K * Y ≤ ρd * (K * (L + 1)) :=
  calc ρn * K * Y = K * (ρn * Y) := by ring
    _ ≤ K * (ρd * (L + 1)) := Nat.mul_le_mul_left _ first
    _ = ρd * (K * (L + 1)) := by ring

/-- The leak at a base, for each epoch of the depth, covers the base's share of the closed form.

The rate bounds the base by the leak an increment above it, plus one.

The closed form takes the rate for each epoch from the base, and its rest is the base's share. -/
private theorem rate_step (ρn ρd K L Y : ℕ) (first : ρn * Y ≤ ρd * (L + 1)) :
    ρd * Y ≤ (ρd - ρn * K) * Y + ρd * (K * (L + 1)) := by
  have rate := rate_cost ρn ρd K L Y first
  have cover : ρd ≤ (ρd - ρn * K) + ρn * K := by omega
  calc ρd * Y ≤ ((ρd - ρn * K) + ρn * K) * Y := Nat.mul_le_mul_right _ cover
    _ = (ρd - ρn * K) * Y + ρn * K * Y := by ring
    _ ≤ (ρd - ρn * K) * Y + ρd * (K * (L + 1)) := Nat.add_le_add_left rate _

/-- The arithmetic of the low bound of an existing key.

The potential floor, rounded down to an increment, is at least the bound less the sync debits. -/
private theorem low_arith (inc band ρn ρd K depth X s R pd sync L1 L2 E0 cap : ℕ)
    (positive : 0 < ρd) (incPos : 0 < inc)
    -- `L1` and `L2` are the leaks an increment above the base and above the shortfall.
    --
    -- The rate bounds the base and the shortfall by them, plus one each.
    (first : ρn * X ≤ ρd * (L1 + 1)) (second : ρn * s ≤ ρd * (L2 + 1)) (epochs : K ≤ depth)
    -- `R` is the bound before its drop, and it is at most the base less the partials due.
    (baseLe : R ≤ X - pd) (effLe : R ≤ E0) (capLe : E0 ≤ cap) :
    R - ((L2 + 1) + depth * (L1 + 1) + band + inc) ≤
      min E0 (min cap
        (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) -
          (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd))) % inc)) + sync := by
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ epochs
  suffices rounded : R - ((L2 + 1) + depth * (L1 + 1) + band + inc) ≤
      (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) -
        (((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd))) % inc) + sync by
    omega
  generalize hF : ((ρd - ρn * K) * (X + band) - ρn * s) / ρd - (band + (sync + pd)) = F
  have modLt := Nat.mod_lt F incPos
  have modLe := Nat.mod_le F inc
  by_cases big : ρd ≤ ρn * K
  · -- the closed form is vacuous, and the leak already covers the base
    have zero : ρd - ρn * K = 0 := Nat.sub_eq_zero_of_le big
    rw [zero, Nat.zero_mul, Nat.zero_sub, Nat.zero_div, Nat.zero_sub] at hF
    have step := rate_step ρn ρd K L1 X first
    rw [zero, Nat.zero_mul, Nat.zero_add] at step
    have base := Nat.le_of_mul_le_mul_left step positive
    omega
  · have step := rate_step ρn ρd K L1 X first
    have mono : (ρd - ρn * K) * X ≤ (ρd - ρn * K) * (X + band) :=
      Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    have bound := Nat.lt_mul_div_succ
      ((ρd - ρn * K) * (X + band) - ρn * s) positive
    have total : ρd * (X + band) ≤ ((ρd - ρn * K) * (X + band) - ρn * s) + ρn * s +
        ρd * (K * (L1 + 1)) + ρd * band := by
      have split : ρd * (X + band) = ρd * X + ρd * band := by ring
      omega
    have lt : ρd * (X + band) < ρd * (((ρd - ρn * K) * (X + band) - ρn * s) / ρd + 1 +
        (L2 + 1) + K * (L1 + 1) + band) := by
      calc ρd * (X + band) ≤ _ := total
        _ < ρd * (((ρd - ρn * K) * (X + band) - ρn * s) / ρd + 1) + ρd * (L2 + 1) +
              ρd * (K * (L1 + 1)) + ρd * band := by omega
        _ = _ := by ring
    have cancel := Nat.lt_of_mul_lt_mul_left lt
    generalize ((ρd - ρn * K) * (X + band) - ρn * s) / ρd = W at cancel hF
    omega

/-- The reserve's lower balance estimate for an existing key allows for losses.

The bound is its effective balance at the call, less its sync debits. -/
theorem existing_low_explicit
    (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex)
    -- The key is activated at the finalized state, and charged on the run from the split.
    --
    -- It exits by C.
    (epochLe : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
      c.epoch ≤ (getCurrentEpoch counted).toNat) (val : Validator)
    (initial : fin.validators.data[v.toNat]? = some val)
    (charged : ∃ c ∈ tailC.departureCharges, c.index = v.toNat) :
    min (min (min (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
          (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) -
        (pinTerms config pulled anc fin).partialsDue v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat -
      -- The loss allowance counts the shortfall below the stored effective balance once.
      (((pinTerms config pulled anc fin).leakAt
          (balanceAt fin v.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        -- It carries the leak at the base for each epoch of the depth.
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
        preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      Internal.exitQ tailC v.toNat + (events.map (Internal.syncDebit v.toNat)).sum := by
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin h.bands.1 v.toNat
  have potential := exitQ_potential h fromFin tailC replayed v epochLe val initial charged ρn ρd
    leaky
  have finEB : balanceAt fin v.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat := rfl
  have capped : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared h.genesis h.caps
      initial
  have toCounted := UInt64.le_iff_toNat_le.mp h.later
  have nearC := h.near
  have arith := low_arith preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand ρn ρd
    ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
    (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (min (min (min (balanceAt pulled v.toNat) (balanceAt fin v.toNat))
          (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat) -
        (pinTerms config pulled anc fin).partialsDue v.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat)
    ((pinTerms config pulled anc fin).partialsDue v.toNat) (events.map (Internal.syncDebit
      v.toNat)).sum
    ((pinTerms config pulled anc fin).leakAt
      (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
        (withdrawalMaxEffectiveBalance preset fork val).toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat)
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
    (withdrawalMaxEffectiveBalance preset fork val).toNat positive h.bands.1 (above _) (above _)
    (by omega) (by omega) (by omega) capped
  simp only [potentialFloor] at potential
  exact le_trans arith (Nat.add_le_add_right potential _)

/-- The relaxed closed form, read at `a + X / M`, is the unslashed one with one more pass.

`Y` stands for `max finEB base0`.

The flagged-key charge estimates the slashing loss at effective balance `X`. -/
private theorem bridge (ρn ρd M k B0 DOWN slack a D X Y inc : Nat) (hM : 2 ≤ M)
    (closed : (M - 1) * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) ≤
      M * (ρd * (a + D + DOWN) + ρn * slack) + ρd * (DOWN + slack))
    (hB : B0 + slack ≤ Y) (hX : Y + inc ≤ X) (hinc : M + 2 * DOWN ≤ inc + 1) :
    (ρd - ρn * (k + 1)) * (B0 + DOWN) ≤ ρd * (a + X / M + D + DOWN) + ρn * slack := by
  have hMpos : 0 < M := by omega
  have hq : X < M * (X / M + 1) := by
    have := Nat.lt_mul_div_succ X hMpos
    simpa [Nat.mul_comm] using this
  have hV : ρd - ρn * (k + 1) ≤ ρd := Nat.sub_le _ _
  have hP : (ρd - ρn * (k + 1)) * (B0 + DOWN) ≤ ρd * (B0 + DOWN) :=
    Nat.mul_le_mul_right _ hV
  have hsplit : M * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) =
      (M - 1) * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) +
        (ρd - ρn * (k + 1)) * (B0 + DOWN) := by
    obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
    simp [Nat.add_mul]
  have hfit : B0 + 2 * DOWN + slack ≤ M * (X / M) := by
    have : M * (X / M + 1) = M * (X / M) + M := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hρ : ρd * (B0 + 2 * DOWN + slack) ≤ ρd * (M * (X / M)) := Nat.mul_le_mul_left _ hfit
  have hlhs : M * ((ρd - ρn * (k + 1)) * (B0 + DOWN)) ≤
      M * (ρd * (a + D + DOWN) + ρn * slack) + ρd * (M * (X / M)) := by
    have e1 : ρd * (B0 + 2 * DOWN + slack) = ρd * (B0 + DOWN) + ρd * (DOWN + slack) := by
      rw [← Nat.mul_add]; congr 1; omega
    omega
  have hrhs : M * (ρd * (a + X / M + D + DOWN) + ρn * slack) =
      M * (ρd * (a + D + DOWN) + ρn * slack) + ρd * (M * (X / M)) := by
    have e2 : ρd * (a + X / M + D + DOWN) = ρd * (a + D + DOWN) + ρd * (X / M) := by
      rw [← Nat.mul_add]; congr 1; omega
    rw [e2, Nat.add_right_comm (ρd * (a + D + DOWN)), Nat.mul_add, Nat.mul_add,
      Nat.mul_left_comm M ρd (X / M)]
  exact Nat.le_of_mul_le_mul_left (by omega) hMpos

/-- The arithmetic of the margin of the floor of a key on C's run.

The closed form of the potential floor, less the sync debits, is at least the base less the fall. -/
private theorem margin_arith (ρn ρd K depth B band s L1 L2 pd sync D a X : ℕ)
    -- `L1` is the leak an increment above the base with the band.
    --
    -- `L2` is the leak an increment above the shortfall.
    --
    -- The rate bounds the base with the band and the shortfall by them, plus one each.
    (positive : 0 < ρd) (first : ρn * (B + band) ≤ ρd * (L1 + 1))
    (second : ρn * s ≤ ρd * (L2 + 1)) (epochs : K ≤ depth)
    -- The fall holds the leak at the base and the band for each epoch of the depth, and the carry.
    (fall : (L2 + 1) + depth * (L1 + 1) + pd ≤ X) (debit : D ≤ sync + pd)
    (closed : (ρd - ρn * K) * (B + band) ≤ ρd * (a + D + band) + ρn * s) :
    B - X - sync ≤ a := by
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ epochs
  have step := rate_step ρn ρd K L1 (B + band) first
  have spread : ρd * (a + D + band + (L2 + 1) + K * (L1 + 1)) =
      ρd * (a + D + band) + ρd * (L2 + 1) + ρd * (K * (L1 + 1)) := by ring
  have total : ρd * (B + band) ≤ ρd * (a + D + band + (L2 + 1) + K * (L1 + 1)) := by omega
  have cancel := Nat.le_of_mul_le_mul_left total positive
  omega

/-- The arithmetic of the stay of the effective balance of a key on C's run.

A segment of the run that starts above `M` in effective balance ends at a balance of at least `M`.

Here `M` is the finalized effective balance. -/
private theorem stay_arith (ρn ρd K k depth inc band B M Bw X pd D bal L1 L2 : ℕ)
    -- A quarter of an increment bounds the band, as the preset requires.
    (positive : 0 < ρd) (incPos : 0 < inc) (quarter : 4 * band ≤ inc) (big : inc ≤ M)
    -- The key has no sync debits, and the test of its floor holds.
    --
    -- The rate bounds the base with the band by the leak, and the test bounds the fall by the band.
    (testB : M ≤ B + band) (fallX : X ≤ band) (first : ρn * (B + band) ≤ ρd * (L1 + 1))
    -- The segment loses the rate of the leak for each epoch and the partials due.
    (fall : (L2 + 1) + depth * (L1 + 1) + pd ≤ X) (epochs : k ≤ K) (depthK : K ≤ depth)
    -- An effective balance above the finalized one is at least an increment above it.
    (start : M + inc ≤ Bw) (debit : D ≤ pd)
    (closed : (ρd - ρn * k) * (Bw + band) ≤ ρd * (bal + D + band)) : M ≤ bal := by
  have cost := rate_cost ρn ρd K L1 (B + band) first
  have depthMul : K * (L1 + 1) ≤ depth * (L1 + 1) := Nat.mul_le_mul_right _ depthK
  have rate : ρn * K * (B + band) + ρd * pd ≤ ρd * X := by
    have fits : ρd * (K * (L1 + 1) + pd) ≤ ρd * X := Nat.mul_le_mul_left ρd (by omega)
    rw [Nat.mul_add] at fits
    omega
  have yPos : 0 < B + band := by omega
  have bound : ρn * K * (B + band) ≤ ρd * (B + band) :=
    calc ρn * K * (B + band) ≤ ρd * X := by omega
      _ ≤ ρd * band := Nat.mul_le_mul_left _ fallX
      _ ≤ ρd * (B + band) := Nat.mul_le_mul_left _ (by omega)
  have under : ρn * K ≤ ρd := Nat.le_of_mul_le_mul_right bound yPos
  have fewer : ρn * k ≤ ρd := Nat.le_trans (Nat.mul_le_mul_left ρn epochs) under
  have mono : (ρd - ρn * k) * (M + inc + band) ≤ (ρd - ρn * k) * (Bw + band) :=
    Nat.mul_le_mul_left _ (by omega)
  have split : ρd * (M + inc + band) =
      (ρd - ρn * k) * (M + inc + band) + ρn * k * (M + inc + band) :=
    calc ρd * (M + inc + band) = ((ρd - ρn * k) + ρn * k) * (M + inc + band) := by
          rw [Nat.sub_add_cancel fewer]
      _ = _ := by ring
  have loss : ρn * k * (M + inc + band) ≤ 3 * (ρn * K * (B + band)) :=
    calc ρn * k * (M + inc + band) ≤ ρn * K * (M + inc + band) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left ρn epochs)
      _ ≤ ρn * K * (3 * (B + band)) := Nat.mul_le_mul_left _ (by omega)
      _ = 3 * (ρn * K * (B + band)) := by ring
  have left : ρd * (M + inc + band + 3 * pd) = ρd * (M + inc + band) + 3 * (ρd * pd) := by ring
  have right : ρd * (bal + D + band + 3 * X) = ρd * (bal + D + band) + 3 * (ρd * X) := by ring
  have total : ρd * (M + inc + band + 3 * pd) ≤ ρd * (bal + D + band + 3 * X) := by omega
  have cancel := Nat.le_of_mul_le_mul_left total positive
  omega

/-- The margin of the floor of a key on C's run, from a rate of its leak. -/
private theorem floorC_margin (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ) (positive : 0 < ρd)
    -- The rate bounds the key's penalties in one rewards pass.
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    -- `low` is the base less `X`.
    (hlow : low = base0 - X)
    -- `X` is at least the fall.
    --
    -- The fall is the carry, the leak for each epoch of the depth, and the partials due.
    --
    -- The leak is read at the base with the band.
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X) :
    -- From the finalized block, the key's balance is above the closed form of the potential floor.
    --
    -- The balance floor uses the rate of the leak and the balance shortfall.
    ∃ slack : ℕ,
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          (preset.downwardBand + slack) ∧
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
        (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
        (before.snoc step).append after = fromFin.append tailC → ∀ evs,
        step.balanceEvents = .ok evs →
        (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd) ∧
      ∀ a D k : ℕ, k ≤ (getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat →
        D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
        (ρd - ρn * k) * (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
            (withdrawalMaxEffectiveBalance preset fork val).toNat +
          preset.downwardBand) ≤ ρd * (a + D + preset.downwardBand) + ρn * slack →
        low - (events.map (Internal.syncDebit i.toNat)).sum ≤ a := by
  have nearC := h.near
  -- The floor also reads the debits of the run, which are its sync debits and its partials.
  --
  -- The partials are at most those due.
  have partialLe := run_partials_le_due h (fromFin.append tailC) nearC i replayed
  refine ⟨effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
    actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat, by omega,
    pass_of_leak h (fromFin.append tailC) nearC i ⟨val, initial⟩ ρn ρd leaky,
    fun a D k hk hD closed => ?_⟩
  rw [← hbase0] at closed
  have bound := margin_arith ρn ρd k
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) base0
    preset.downwardBand
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).partialsDue i.toNat)
    (events.map (Internal.syncDebit i.toNat)).sum D a X
    positive (above _) (above _) (by omega) fall (by omega) closed
  omega

/-- The arithmetic of the margin of the floor of a slashed key on C's run.

The bound allows one more epoch of penalties. -/
private theorem floorC_margin_slash (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low Xs : ℕ)
    -- `Xs` is the effective balance that the slash is read at.
    --
    -- It is at least the finalized one and an increment.
    (hXs : max (balanceAt fin i.toNat) base0 + preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ Xs)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    -- The fall counts leak at the base balance and includes a rounding band in `X`.
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        preset.downwardBand + (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X) :
    ∃ slack : ℕ,
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          (preset.downwardBand + slack) ∧
      (∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
        (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
        (before.snoc step).append after = fromFin.append tailC → ∀ evs,
        step.balanceEvents = .ok evs →
        (evs.map (penaltyDebit i.toNat)).sum ≤ ρn * effectiveAt m i.toNat / ρd) ∧
      ∀ a D k : ℕ, k ≤ (getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat →
        D ≤ (events.map (Internal.syncDebit i.toNat)).sum + (events.map (floorPartialDebit i)).sum →
        ((EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat - 1) *
        ((ρd - ρn * (k + 1)) *
            (min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
              (withdrawalMaxEffectiveBalance preset fork val).toNat + preset.downwardBand)) ≤
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat *
            (ρd * (a + D + preset.downwardBand) + ρn * slack) +
            ρd * (preset.downwardBand + slack) →
        -- The floor deducts the initial slashing penalty at the fork's quotient.
        --
        -- The resulting floor uses the key's balance and the initial slashing penalty `Xs / M`.
        low - (events.map (Internal.syncDebit i.toNat)).sum ≤ a + Xs /
          (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat := by
  have nearC := h.near
  have partialLe := run_partials_le_due h (fromFin.append tailC) nearC i replayed
  have fusaka := Internal.parameters_of_fusaka (preset := preset) h.fulu h.early
  have two := h.facts.quotient
  have slashFact := h.facts.slash
  have quarter := h.facts.quarterBand
  rw [← fusaka] at two slashFact
  refine ⟨effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
    actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat, by omega,
    pass_of_leak h (fromFin.append tailC) nearC i ⟨val, initial⟩ ρn ρd leaky,
    fun a D k hk hD closed => ?_⟩
  rw [← hbase0] at closed
  have finEq : balanceAt fin i.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := rfl
  have bridged := bridge ρn ρd
    (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat k base0
    preset.downwardBand
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    a D Xs (max (balanceAt fin i.toNat) base0) preset.EFFECTIVE_BALANCE_INCREMENT.toNat two
    closed (by rw [hbase0, finEq]; omega) hXs (by omega)
  have finSplit := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
  have splitPulled := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  simp only at finSplit
  have epochs : k + 1 ≤ (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := by
    omega
  have mono : (ρd - ρn * (k + 1)) * (base0 + 0) ≤
      (ρd - ρn * (k + 1)) * (base0 + preset.downwardBand) :=
    Nat.mul_le_mul_left _ (by omega)
  have closed0 : (ρd - ρn * (k + 1)) * (base0 + 0) ≤ ρd * ((a + Xs /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat +
        preset.downwardBand) + D + 0) + ρn * (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset)
        i.toNat - actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat) := by
    refine mono.trans (bridged.trans (le_of_eq ?_))
    congr 2
    omega
  have bound := margin_arith ρn ρd (k + 1)
    ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) base0 0
    (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (base0 + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).leakAt
      (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
        actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
    ((pinTerms config pulled anc fin).partialsDue i.toNat)
    (events.map (Internal.syncDebit i.toNat)).sum D
    (a + Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat +
      preset.downwardBand) (X - preset.downwardBand)
    positive (by simpa using above base0) (above _) epochs (by omega) (by omega) closed0
  have downLe : preset.downwardBand ≤ X := by omega
  rw [hlow]
  exact (fun (B X S q a dn : ℕ) (le : dn ≤ X) (b : B - (X - dn) - S ≤ a + q + dn) =>
    show B - X - S ≤ a + q by omega) _ _ _ _ _ _ downLe bound

/-- The fall `X` leaves the rounded balance floor above the reserve's lower estimate.

The drop has the increment where the fall has the partials due.

A key whose bound is zero needs no floor. -/
private theorem slash_low_arith (R pd dropV X base0 m sy G r inc A P dn : ℕ)
    (hX : X = A + P + dn + pd) (hD : dropV = A + P + dn + inc)
    (hR : 0 < R → R + pd ≤ base0) (hG : base0 - X - sy - m = G) (hr : r < inc) :
    R - dropV - m - sy ≤ G - r := by
  omega

/-- The effective balance at C stays above the reserve's lower estimate less the slashing loss.

The sync debits of the key are added to it. -/
theorem lowEB_slashed (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    -- The key is unslashed at the finalized block, and it may be slashed at C.
    (unslashed : val.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat)) :
    -- The slashing loss uses the same effective balance as the flagged-key charge.
    --
    -- The lower estimate includes a band and an increment to cover rounding the floor.
    (pinTerms config pulled anc fin).lowEB i.toNat -
        max ((pinTerms config pulled anc fin).ebUp i.toNat)
          (max (balanceAt fin i.toNat) ((pinTerms config pulled anc fin).base0 i.toNat) +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) /
        (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat ≤
      balanceAt counted i.toNat + (events.map (Internal.syncDebit i.toNat)).sum := by
  classical
  obtain ⟨shared⟩ := h.toFin
  have incPos := h.bands.1
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin incPos i.toNat
  have capped : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax shared h.genesis h.caps
      initial
  have finEq : balanceAt fin i.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := rfl
  have base0Eq := Internal.base0_of_found config pulled anc fin initial
  have dropEq := Internal.drop_of_found config pulled anc fin initial
  obtain ⟨X, hX⟩ : ∃ X, X = ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            ((pinTerms config pulled anc fin).base0 i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        preset.downwardBand + (pinTerms config pulled anc fin).partialsDue i.toNat := ⟨_, rfl⟩
  obtain ⟨Xs, hXsEq⟩ : ∃ Xs, Xs = max ((pinTerms config pulled anc fin).ebUp i.toNat)
      (max (balanceAt fin i.toNat) ((pinTerms config pulled anc fin).base0 i.toNat) +
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := ⟨_, rfl⟩
  obtain ⟨slack, start, pass, arithS⟩ := floorC_margin_slash h fromFin tailC replayed i val initial
    ρn ρd positive leaky above ((pinTerms config pulled anc fin).base0 i.toNat) X
    ((pinTerms config pulled anc fin).base0 i.toNat - X) Xs
    (by rw [hXsEq]; exact Nat.le_max_right _ _) base0Eq rfl (by omega)
  have endpoint := Internal.cfloor_endpoint_slash h counted (fromFin.append tailC) h.near replayed i
    val
    initial unslashed retained slack ρn ρd
    ((pinTerms config pulled anc fin).base0 i.toNat - X -
      (events.map (Internal.syncDebit i.toNat)).sum)
    (Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat) start pass
    arithS (fromFin.append tailC) (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) rfl
  have actEq : ((fin.balances.data[i.toNat]?).map (·.toNat)).getD 0 =
      actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := rfl
  rw [Internal.lowEB_unfold, actEq]
  have effC : balanceAt counted i.toNat =
      effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) i.toNat := rfl
  rw [effC, ← hXsEq]
  obtain ⟨m1, hm1⟩ : ∃ m1, m1 = min (min (balanceAt pulled i.toNat) (balanceAt fin i.toNat))
      (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat) := ⟨_, rfl⟩
  rw [← hm1]
  have m1Eff : m1 ≤ balanceAt fin i.toNat := by
    rw [hm1]
    exact Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)
  have m1Act : m1 ≤ actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat := by
    rw [hm1]
    exact Nat.min_le_right _ _
  obtain ⟨R, hR⟩ : ∃ R, R = min (m1 - (pinTerms config pulled anc fin).partialsDue i.toNat)
      preset.MIN_ACTIVATION_BALANCE.toNat := ⟨_, rfl⟩
  rw [← hR]
  have hRle : R ≤ m1 - (pinTerms config pulled anc fin).partialsDue i.toNat := by
    rw [hR]
    exact Nat.min_le_left _ _
  have capped' : balanceAt fin i.toNat ≤ (withdrawalMaxEffectiveBalance preset fork val).toNat := by
    rw [finEq]
    exact capped
  have baseLe : 0 < R → R + (pinTerms config pulled anc fin).partialsDue i.toNat ≤
      (pinTerms config pulled anc fin).base0 i.toNat := fun positive => by
    rw [base0Eq]
    exact Nat.le_min.mpr ⟨by omega, by omega⟩
  have underM : R ≤ m1 := Nat.le_trans hRle (Nat.sub_le _ _)
  generalize hG : (pinTerms config pulled anc fin).base0 i.toNat - X -
    (events.map (Internal.syncDebit i.toNat)).sum - Xs /
      (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat = G at endpoint
  have modLt := Nat.mod_lt G incPos
  generalize G % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = r at endpoint modLt
  rw [← finEq] at endpoint
  have bounded : R - (pinTerms config pulled anc fin).drop i.toNat -
      Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        (events.map (Internal.syncDebit i.toNat)).sum ≤ G - r :=
    slash_low_arith _ _ _ _ _ _ _ _ _ _ _ _ _ hX dropEq baseLe hG modLt
  have atMin : R - (pinTerms config pulled anc fin).drop i.toNat -
      Xs / (EthLib.Consensus.parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat -
        (events.map (Internal.syncDebit i.toNat)).sum ≤
      min (balanceAt fin i.toNat) (min (withdrawalMaxEffectiveBalance preset fork val).toNat
        (G - r)) :=
    Nat.le_min.mpr ⟨Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _)
      (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans underM m1Eff))),
      Nat.le_min.mpr ⟨Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans (Nat.sub_le _ _)
        (Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans underM (Nat.le_trans m1Eff capped')))),
        bounded⟩⟩
  omega

/-- The effective balance of a key on C's run stays at its finalized value when the test holds.

The key has no sync debits on the run, and the test of its floor holds.

A downward update fires only at a step whose balance after it is at least the finalized balance. -/
private theorem floorC_stay (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (i : ValidatorIndex) (val : Validator) (initial : fin.validators.data[i.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[i.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    (ρn ρd : ℕ) (positive : 0 < ρd)
    (leaky : ∀ eb : ℕ, preset.EFFECTIVE_BALANCE_INCREMENT.toNat ∣ eb →
      (pinTerms config pulled anc fin).leakAt eb i.toNat ≤ ρn * eb / ρd)
    (above : ∀ x : ℕ, ρn * x ≤ ρd * ((pinTerms config pulled anc fin).leakAt
      (x + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1))
    (base0 X low finEB : ℕ)
    (hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat)
    (hlow : low = base0 - X)
    (hfin : finEB = effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat)
    (fall : ((pinTerms config pulled anc fin).leakAt
          (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
            actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
              preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
          ((pinTerms config pulled anc fin).leakAt
            (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat + 1) +
        (pinTerms config pulled anc fin).partialsDue i.toNat ≤ X)
    (sync : (events.map (Internal.syncDebit i.toNat)).sum = 0)
    (test : max finEB base0 ≤ low + preset.downwardBand)
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC) :
    finEB ≤ effectiveAt z i.toNat := by
  obtain ⟨toFin⟩ := h.toFin
  have incPos := h.bands.1
  have alignedFin := FloorTrace.effective_aligned toFin h.genesis h.aligned i.toNat
  have aligned : finEB % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hfin]
    exact alignedFin
  by_cases small : finEB < preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  · have zero : finEB = 0 := by rw [← Nat.mod_eq_of_lt small]; exact aligned
    omega
  have big : preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ finEB := Nat.le_of_not_lt small
  have quarter := h.facts.quarterBand
  have fallX : X ≤ preset.downwardBand := by omega
  have testB : finEB ≤ base0 + preset.downwardBand := by omega
  have first := above (base0 + preset.downwardBand)
  have partialLe := run_partials_le_due h (fromFin.append tailC) h.near i replayed
  obtain ⟨slack, start, pass, arith⟩ := floorC_margin h fromFin tailC replayed i val initial ρn ρd
    positive leaky above base0 X low hbase0 hlow fall
  have floorAt : ∀ {p : ForkedBeaconState preset} (r1 : Run config checks ⟨fork, fin⟩ p)
      (r2 : Run config checks p ⟨fork, counted⟩), r1.append r2 = fromFin.append tailC →
      low - (events.map (Internal.syncDebit i.toNat)).sum ≤ actualBalanceAt p i.toNat :=
    fun r1 r2 whole => Internal.cfloor_balance h counted (fromFin.append tailC) h.near replayed i
      val
      initial clean retained slack ρn ρd (low - (events.map (Internal.syncDebit i.toNat)).sum) start
        pass
      arith r1 r2 whole
  have forkEnd : ∀ {p : ForkedBeaconState preset} (r2 : Run config checks p ⟨fork, counted⟩),
      p.fork < .glamsterdam := fun r2 =>
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps r2.chainSteps) h.early
  have inside : i.toNat < fin.validators.data.size := (Array.getElem?_eq_some_iff.mp initial).1
  have cappedFin : effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax toFin h.genesis h.caps
      initial
  rw [hfin]
  refine (Internal.Run.effective_floor_pair rp (forkEnd rest) h.fulu i.toNat inside 0 0 0 0 0
    0).2.1 alignedFin ?_ ?_
  · intro m n before step after cut' below
    have nSame := Internal.fork_eq_of_run (before.snoc step) (after.append rest) (Nat.le_refl _)
    have mSame := Internal.fork_eq_of_run before ((Run.nil.snoc step).append (after.append rest))
      (Nat.le_refl _)
    obtain ⟨mF, mS⟩ := m
    obtain ⟨nF, nS⟩ := n
    obtain rfl : fork = nF := nSame.symm
    obtain rfl : fork = mF := mSame.symm
    have eqn : (before.snoc step).append (after.append rest) = fromFin.append tailC := by
      rw [Run.append_assoc, cut', cut]
    have atN := floorAt (before.snoc step) (after.append rest) eqn
    by_cases down : effectiveAt (⟨fork, mS⟩ : ForkedBeaconState preset) i.toNat ≤ finEB
    · omega
    have alignedM := FloorTrace.effective_aligned (toFin.append before) h.genesis h.aligned i.toNat
    have gap := add_le_of_lt_of_aligned alignedM aligned (by omega)
    have origin := Internal.cfloor_origin h counted (fromFin.append tailC) h.near replayed i val
      initial
      clean retained before ((Run.nil.snoc step).append (after.append rest))
      (by rw [Run.append_assoc]; exact eqn)
    rcases origin with same | ⟨w, pre, post, hpre, hm, hle, -⟩
    · omega
    have wSame := Internal.fork_eq_of_run pre post (Nat.le_refl _)
    obtain ⟨wF, wS⟩ := w
    obtain rfl : fork = wF := wSame.symm
    obtain ⟨valW, initialW, -⟩ := pre.registryLifecycle.validators i.toNat val initial
    have hwhole : (pre.append (post.snoc step)).append (after.append rest) =
        fromFin.append tailC := by
      show ((pre.append post).snoc step).append (after.append rest) = _
      rw [hpre]
      exact eqn
    have lift : ∀ {m' n' : ForkedBeaconState preset} (before' : Run config checks ⟨fork, wS⟩ m')
        (step' : Step config checks m' n') (after' : Run config checks n' ⟨fork, nS⟩),
        (before'.snoc step').append after' = post.snoc step →
        ((pre.append before').snoc step').append (after'.append (after.append rest)) =
          fromFin.append tailC := by
      intro m' n' before' step' after' cut''
      have shift : ((pre.append before').snoc step').append after' =
          pre.append ((before'.snoc step').append after') :=
        (Run.append_assoc pre (before'.snoc step') after').symm
      rw [Run.append_assoc, shift, cut'']
      exact hwhole
    obtain ⟨segEv, segOk⟩ := Run.balanceEvents_ok (post.snoc step) h.early
      (getCurrentEpoch pulled).toNat
    obtain ⟨preEv, preOk⟩ := Run.balanceEvents_ok pre h.early (getCurrentEpoch pulled).toNat
    obtain ⟨D, split, closed⟩ := Internal.segment_potential h h.near i clean pre (post.snoc step)
      (after.append rest) valW initialW
      (fun before' step' after' cut'' w found => retained (pre.append before') step'
        (after'.append (after.append rest)) (lift before' step' after' cut'') w found)
      0 ρn ρd (by omega)
      (fun before' step' after' cut'' evs ok => pass (pre.append before') step'
        (after'.append (after.append rest)) (lift before' step' after' cut'') evs ok)
      segOk
    have app := balanceEvents_append pre (post.snoc step) (getCurrentEpoch pulled).toNat preOk
      segOk
    obtain ⟨b, hb, isPrefix⟩ := Run.balanceEvents_prefix (pre.append (post.snoc step))
      (after.append rest) (getCurrentEpoch pulled).toNat events (by rw [hwhole]; exact replayed)
    have sameEv : b = preEv ++ segEv := Except.ok.inj (hb.symm.trans app)
    have sub : segEv.Sublist events := by
      rw [sameEv] at isPrefix
      exact (List.sublist_append_right _ _).trans isPrefix.sublist
    have syncLe : (segEv.map (Internal.syncDebit i.toNat)).sum ≤ (events.map (Internal.syncDebit
      i.toNat)).sum :=
      (sub.map (Internal.syncDebit i.toNat)).sum_le_sum fun _ _ => Nat.zero_le _
    have partialSeg : (segEv.map (floorPartialDebit i)).sum ≤
        (events.map (floorPartialDebit i)).sum :=
      (sub.map (floorPartialDebit i)).sum_le_sum fun _ _ => Nat.zero_le _
    have splitDebit := Internal.floorPenaltyDebit_sum i.toNat segEv
    have cappedW : effectiveAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat ≤
        (withdrawalMaxEffectiveBalance preset fork valW).toNat :=
      DirectSafety.Apriori.Internal.effectiveAt_le_withdrawalMax (toFin.append pre) h.genesis
        h.caps initialW
    have preEpoch := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps pre.chainSteps)
    have restEpoch := UInt64.le_iff_toNat_le.mp
      (currentEpoch_le_of_chainSteps (after.append rest).chainSteps)
    simp only at preEpoch restEpoch
    have kept := stay_arith ρn ρd ((getCurrentEpoch counted).toNat - (getCurrentEpoch fin).toNat)
      ((getCurrentEpoch nS).toNat - (getCurrentEpoch wS).toNat)
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat preset.downwardBand base0 finEB
      (min (actualBalanceAt (⟨fork, wS⟩ : ForkedBeaconState preset) i.toNat)
        (withdrawalMaxEffectiveBalance preset fork valW).toNat) X
      ((pinTerms config pulled anc fin).partialsDue i.toNat)
      D (actualBalanceAt (⟨fork, nS⟩ : ForkedBeaconState preset) i.toNat)
      ((pinTerms config pulled anc fin).leakAt
        (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
      ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) i.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) i.toNat)
      positive incPos h.facts.quarterBand big testB fallX first fall (by omega)
      (by have := h.near; omega) (by omega) (by omega) (by simpa using closed)
    omega
  · intro p member
    obtain ⟨r1, r2, -⟩ : ∃ (r1 : Run config checks ⟨fork, fin⟩ p)
        (r2 : Run config checks p ⟨fork, counted⟩), r1.append r2 = rp.append rest := by
      obtain ⟨r1, r2, whole⟩ := Internal.balancePath_endpoint rp rest (Nat.le_refl _) member
      exact ⟨r1, r2, whole⟩
    obtain ⟨w, found, mono⟩ := r1.validatorCap_mono h.caps
      i.toNat val initial
    have := UInt64.le_iff_toNat_le.mp mono
    simp only [PinTerms.capAt, found, Option.map_some, Option.getD_some]
    exact cappedFin.trans this

/-- A key whose exit comes late stays out of its withdrawal along a run from the finalized block.

Its exit epoch is constant from the state where it is set.

The withdrawable epoch is the delay after it, so it is after the horizon `high` of the call.

A key with no exit has the withdrawable epoch that no epoch reaches, since it exits no later. -/
theorem retained_of_exit (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {e : BeaconState preset fork} (tail : Run config checks ⟨fork, split⟩ ⟨fork, e⟩)
    (high : ℕ) (highLe : high ≤ (getCurrentEpoch pulled).toNat) (i : ValidatorIndex)
    {wE : Validator} (foundE : e.validators.data[i.toNat]? = some wE)
    (late : high + 1 < wE.exitEpoch.toNat + config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat) :
    ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, e⟩),
      (before.snoc step).append after = fromFin.append tail → ∀ w,
      n.state.validators.data[i.toNat]? = some w →
      (high + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[i.toNat]? = some u →
          high + 1 < u.withdrawableEpoch.toNat) := by
  obtain ⟨toFin⟩ := h.toFin
  intro m n before step after _ w _
  refine .inr fun u foundU => ?_
  have holds := Run.invariant (Genesis.invariant h.genesis) (toFin.append before)
  obtain ⟨last, located, kept⟩ := ((Run.nil.snoc step).append after).registryLifecycle.validators
    i.toNat u foundU
  by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
  · have ordered := holds.exitsOrdered u (Array.mem_of_getElem? foundU)
    rw [unset] at ordered
    have := UInt64.le_iff_toNat_le.mp ordered
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
    omega
  · have same := congrArg UInt64.toNat (kept.exitEpoch unset)
    have lastEq : last = wE := Option.some.inj (located.symm.trans foundE)
    have delayed := (toFin.append before).exit_withdrawable_delay h.genesis i.toNat u foundU unset
    subst lastEq
    omega

/-- A key whose exit at R is at or before the finalized epoch has that exit at the finalized state.

A key absent from the finalized registry was created after it, and its exit is assigned after it.

An exit assigned after the finalized state is at least the seed lookahead past its epoch.

An exit assigned before it is kept along the run. -/
theorem exit_kept_of_le_fin (h : Setting config checks g split fin pulled anc counted V)
    {i : ℕ} {w : Validator} (foundPulled : pulled.validators.data[i]? = some w)
    (exited : w.exitEpoch.toNat ≤ (getCurrentEpoch fin).toNat) :
    ∃ u, fin.validators.data[i]? = some u ∧ u.exitEpoch = w.exitEpoch := by
  obtain ⟨fromFin⟩ := h.fromFin
  obtain ⟨toPulled⟩ := h.toPulled
  have assigned : w.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
    have := getCurrentEpoch_succ_lt_farFuture h.twoSlots fin
    have := congrArg UInt64.toNat far
    omega
  have late : ∀ c ∈ (fromFin.append toPulled).departureCharges,
      (getCurrentEpoch fin).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat ≤ c.epoch :=
    DirectSafety.Run.departureCharges_epoch_ge_start (fromFin.append toPulled)
      (Nat.le_trans (by decide) h.fulu) h.early
  cases foundFin : fin.validators.data[i]? with
  | none =>
    obtain ⟨charge, member, -, epoch⟩ := Internal.Run.charge_of_exit (fromFin.append toPulled)
      (Nat.le_trans (by decide) h.fulu) h.early i (fun v hv => nomatch hv.symm.trans foundFin) w
      foundPulled assigned
    have := late charge member
    omega
  | some u =>
    refine ⟨u, rfl, ?_⟩
    by_cases unset : u.exitEpoch = FAR_FUTURE_EPOCH
    · obtain ⟨charge, member, -, epoch⟩ := (fromFin.append toPulled).departure_charge_of_assigned
        i u w foundFin foundPulled unset assigned
      have := late charge member
      omega
    · obtain ⟨last, located, kept⟩ :=
        (fromFin.append toPulled).registryLifecycle.validators i u foundFin
      have lastEq : last = w := Option.some.inj (located.symm.trans foundPulled)
      rw [← lastEq]
      exact (kept.exitEpoch unset).symm

/-- The events of C's run from the finalized block are those of its two parts.

They are read at R's epoch. -/
theorem V_events (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat =
      .ok (eventsF ++ eventsC) := by
  have calledNat := UInt64.le_iff_toNat_le.mp (Internal.Setting.called h)
  have nearC := h.near
  refine balanceEvents_append fromFin tailC _ ?_ ?_
  · rw [balanceEvents_eq_of_endpoint_le fromFin (localHigh := high) (by simp only; omega)
      (by simp only; omega)]
    exact replayedF
  · rw [balanceEvents_eq_of_endpoint_le tailC (localHigh := highC) (by simp only; omega)
      (by simp only; omega)]
    exact replayedC

/-- The voter charge covers the key's sync debits over both runs. -/
private theorem V_sync_le (eventsF eventsC : List (BalanceEvent preset)) (v : ℕ) :
    ((eventsF ++ eventsC).map (Internal.syncDebit v)).sum ≤
      (eventsF.map (Internal.syncDebit v)).sum + Internal.syncF eventsC v := by
  have := Internal.sum_syncDebit_eq eventsC v
  unfold Internal.syncF
  rw [List.map_append, List.sum_append]
  omega

/-- A key falls by at least its effective balance at R, less any bound of its floor.

A key that is not in the finalized registry has the floor zero. -/
private theorem fall_floor (h : Setting config checks g split fin pulled anc counted V)
    (v : ValidatorIndex) (X : ℕ)
    (bound : fin.validators.data[v.toNat]? = none ∨
      (pinTerms config pulled anc fin).floorC v.toNat ≤ X) :
    (pulledBalance pulled v : ℤ) ≤ ((pinTerms config pulled anc fin).fall v.toNat : ℤ) + X := by
  have fallEq := Internal.fall_eq config pulled anc fin v.toNat
  simp only [h.shallow, ↓reduceIte] at fallEq
  have eRdef : pulledBalance pulled v = balanceAt pulled v.toNat := rfl
  rcases bound with none | le
  · obtain ⟨low, base, shape⟩ : ∃ low base : ℕ, (pinTerms config pulled anc fin).floorC v.toNat =
        if max (balanceAt fin v.toNat) base ≤ low + preset.downwardBand then balanceAt fin v.toNat
        else min (balanceAt fin v.toNat) (low - low % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :=
      ⟨_, _, rfl⟩
    have zero : balanceAt fin v.toNat = 0 := by simp [balanceAt, none]
    have : (pinTerms config pulled anc fin).floorC v.toNat = 0 := by
      rw [shape]
      split
      · exact zero
      · rw [zero]
        exact Nat.zero_min _
    omega
  · omega

/-- C's floor of a key is below its effective balance at each state of C's run, with its debits.

The debits are the key's sync debits over the run and their rounding band.

The key is in the finalized registry, unslashed at C's end, and kept out of withdrawal. -/
private theorem V_floor (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {events : List (BalanceEvent preset)}
    (replayed : (fromFin.append tailC).balanceEvents (getCurrentEpoch pulled).toNat = .ok events)
    (v : ValidatorIndex) (val : Validator) (initial : fin.validators.data[v.toNat]? = some val)
    (clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false)
    (retained : ∀ {m n : ForkedBeaconState preset} (before : Run config checks ⟨fork, fin⟩ m)
      (step : Step config checks m n) (after : Run config checks n ⟨fork, counted⟩),
      (before.snoc step).append after = fromFin.append tailC → ∀ w,
      n.state.validators.data[v.toNat]? = some w →
      ((getCurrentEpoch pulled).toNat + 1 < w.exitEpoch.toNat ∨
        ∀ u, m.state.validators.data[v.toNat]? = some u →
          (getCurrentEpoch pulled).toNat + 1 < u.withdrawableEpoch.toNat))
    {z : ForkedBeaconState preset} (rp : Run config checks ⟨fork, fin⟩ z)
    (rest : Run config checks z ⟨fork, counted⟩) (cut : rp.append rest = fromFin.append tailC) :
    (pinTerms config pulled anc fin).floorC v.toNat ≤ effectiveAt z v.toNat +
      (events.map (Internal.syncDebit v.toNat)).sum + Internal.bandR events v.toNat := by
  obtain ⟨ρn, ρd, positive, leaky, above⟩ := leak_rate config pulled anc fin h.bands.1 v.toNat
  obtain ⟨base0, hbase0def⟩ : ∃ b, b = (pinTerms config pulled anc fin).base0 v.toNat := ⟨_, rfl⟩
  have hbase0 : base0 = min (actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat)
      (withdrawalMaxEffectiveBalance preset fork val).toNat :=
    hbase0def.trans (Internal.base0_of_found config pulled anc fin initial)
  obtain ⟨X, hX⟩ : ∃ X, X = ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        ((pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat +
            (pinTerms config pulled anc fin).gainRate v.toNat + 1) +
      (pinTerms config pulled anc fin).partialsDue v.toNat := ⟨_, rfl⟩
  have hfall : ((pinTerms config pulled anc fin).leakAt
        (effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat -
          actualBalanceAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat +
            preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        ((pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1) +
      (pinTerms config pulled anc fin).partialsDue v.toNat ≤ X := by
    rw [hX]
    have := Nat.mul_le_mul_left ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)
      (show (pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat + 1 ≤
        (pinTerms config pulled anc fin).leakAt
          (base0 + preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) v.toNat +
            (pinTerms config pulled anc fin).gainRate v.toNat + 1 by omega)
    omega
  have hfloorC : (pinTerms config pulled anc fin).floorC v.toNat =
      if max (balanceAt fin v.toNat) base0 ≤ (base0 - X) + preset.downwardBand
      then balanceAt fin v.toNat
      else min (balanceAt fin v.toNat)
        ((base0 - X) - (base0 - X) % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    rw [hX, hbase0def]
    rfl
  have hfin : balanceAt fin v.toNat =
      effectiveAt (⟨fork, fin⟩ : ForkedBeaconState preset) v.toNat := rfl
  obtain ⟨slack, margin⟩ := floorC_margin h fromFin tailC replayed v val initial ρn ρd positive
    leaky above base0 X (base0 - X) hbase0 rfl hfall
  exact Internal.floorC_at h fromFin tailC replayed v val initial clean retained base0 X (base0 - X)
    (balanceAt fin v.toNat) ((pinTerms config pulled anc fin).floorC v.toNat) hbase0 rfl hfin
    hfloorC rp rest cut ⟨slack, ρn, ρd, margin⟩
    (fun test sync => floorC_stay h fromFin tailC replayed v val initial clean retained
      ρn ρd positive leaky above base0 X (base0 - X) (balanceAt fin v.toNat)
      hbase0 rfl hfin hfall sync test rp rest cut)

/-- An active V key's loss at C fits the reserve's fall charge and the losses C's floor omits.

C's floor is below the key's effective balance at C's end, plus its sync debits and their band.

The fall is the key's effective balance at R, less that floor, within the delay. -/
private theorem V_active (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ v ∈ V, v ∈ countedActiveVoters counted → (pulledBalance pulled v : ℤ) - countedBalance counted
        v ≤
      ((pinTerms config pulled anc fin).fall v.toNat : ℤ) +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
          Internal.bandR (eventsF ++ eventsC) v.toNat := by
  intro v member act
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have delay := (Internal.Setting.delay h)
  obtain ⟨wC, foundC, isActive⟩ := Internal.active_of_activeVoters h.early (s := counted) act
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActive
  have exitAfter := UInt64.lt_iff_toNat_lt.mp isActive.2
  have clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
    intro w found
    rw [foundC] at found
    cases found
    simpa [slashedFlagAt, foundC] using (h.voting v member).2
  have sync := V_sync_le eventsF eventsC v.toNat
  have := fall_floor h v (balanceAt counted v.toNat + ((eventsF.map (Internal.syncDebit
    v.toNat)).sum +
      Internal.syncF eventsC v.toNat) + Internal.bandR (eventsF ++ eventsC) v.toNat) (by
    cases initial : fin.validators.data[v.toNat]? with
    | none => exact .inl rfl
    | some val =>
      have floor := V_floor h fromFin tailC
        (Internal.V_events h fromFin tailC high highC endEpoch endEpochC replayedF replayedC) v val
          initial
        clean (Internal.retained_of_exit h fromFin tailC _ (Nat.le_refl _) v foundC (by omega))
          (fromFin.append tailC)
        Run.nil rfl
      exact .inr (by
        have : effectiveAt (⟨fork, counted⟩ : ForkedBeaconState preset) v.toNat =
          balanceAt counted v.toNat := rfl
        omega))
  have eCdef : countedBalance counted v = balanceAt counted v.toNat := rfl
  omega

/-- A V key that left C's active set is charged by its exit, its late activation or its floor. -/
private theorem V_left (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩)
    {eventsF eventsC : List (BalanceEvent preset)} (high highC : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    ∀ v ∈ countedInactiveVoters counted V, (pulledBalance pulled v : ℤ) ≤
      ((pinTerms config pulled anc fin).fall v.toNat +
        ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC v.toNat) +
        Internal.bandR (eventsF ++ eventsC) v.toNat + Internal.exitQ tailC v.toNat +
        (if (pinTerms config pulled anc fin).exitingB v.toNat = true then pulledBalance pulled v
          else 0) +
        (if (pinTerms config pulled anc fin).lateB v.toNat = true then pulledBalance pulled v
          else 0) : ℕ) := by
  intro v hv
  obtain ⟨member, notAC⟩ := Finset.mem_filter.mp hv
  obtain ⟨toFin⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  -- The key's activation is at most R's epoch.
  obtain ⟨w, foundW, activeWb⟩ := Internal.active_of_activeVoters h.early (h.voting v member).1
  have activeW := activeWb
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
    UInt64.lt_iff_toNat_lt] at activeW
  have farEpoch := getCurrentEpoch_succ_lt_farFuture h.twoSlots pulled
  have finSplit := UInt64.le_iff_toNat_le.mp h.finalized
  have laterNat := UInt64.le_iff_toNat_le.mp h.later
  have nearC := h.near
  -- Its activation may be within the seed lookahead of the split.
  --
  -- Then the two branches agree on its activity there.
  --
  -- R's registry may hold a key that C's does not, since the registries differ by position.
  --
  -- Then the voting hypothesis holds with the unslashed flag read as false.
  --
  -- Such a key activates late at R, so it is in the second case.
  by_cases early : w.activationEpoch.toNat ≤
      (getCurrentEpoch split).toNat + preset.MAX_SEED_LOOKAHEAD.toNat
  · -- the key's activity at its activation epoch is shared, so C holds it
    have atAct : isActiveAt counted w.activationEpoch v.toNat = true := by
      rw [← Internal.activity_shared h (e := w.activationEpoch) early v.toNat]
      exact isActiveAt_eq_true_iff.mpr ⟨w, foundW, by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
          UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
        omega⟩
    obtain ⟨u, foundU, activeU⟩ := isActiveAt_eq_true_iff.mp atAct
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt] at activeU
    -- Then C's record exits the key by C's epoch, which R reads as exiting or C charges.
    have exited : u.exitEpoch.toNat ≤ (getCurrentEpoch counted).toNat := by
      by_contra later
      apply notAC
      simpa [countedActiveVoters, activeVoters] using mem_getActiveValidatorIndices_of_isActiveAt
        (isActiveAt_eq_true_iff.mpr ⟨u, foundU, by
          simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq,
            UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]
          omega⟩)
    have assigned : u.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at exited
      omega
    have unslashed : u.slashed = false := by
      simpa [slashedFlagAt, foundU] using (h.voting v member).2
    by_cases ex : (pinTerms config pulled anc fin).exitingB v.toNat = true
    · simp only [ex, ↓reduceIte]
      omega
    · obtain ⟨c, mem, idx⟩ := Internal.exit_charged h tailC foundU assigned exited unslashed
        (fun w' found _ => by
          obtain rfl : w' = w := Option.some.inj (found.symm.trans foundW)
          exact .inr (isActiveAt_eq_true_iff.mpr ⟨w', foundW, activeWb⟩))
        (by simpa using ex)
      have exitOf : ∀ c ∈ tailC.departureCharges, c.index = v.toNat →
          u.exitEpoch.toNat = c.epoch := by
        intro c' mem' idx'
        obtain ⟨x, found, -, epoch⟩ := Run.departure_charge_exit tailC c' mem'
        rw [idx'] at found
        obtain rfl : x = u := Option.some.inj (found.symm.trans foundU)
        exact epoch
      have startC := DirectSafety.Run.departureCharges_epoch_ge_start tailC
        (Nat.le_trans (by decide) h.fulu) h.early c mem
      simp only at startC
      have exitC := exitOf c mem idx
      have shallow := h.shallow
      have finOrder := UInt64.le_iff_toNat_le.mp (currentEpoch_le_of_chainSteps fromFin.chainSteps)
      simp only at finOrder
      obtain ⟨sd, pre, post, cut, -, amount⟩ := exit_stop fromFin tailC v.toNat ⟨c, mem, idx⟩
        (fun c' mem' idx' => by have := exitOf c' mem' idx'; omega)
      have sync := V_sync_le eventsF eventsC v.toNat
      have clean : ∀ w, counted.validators.data[v.toNat]? = some w → w.slashed = false := by
        intro w found
        rw [foundU] at found
        cases found
        exact unslashed
      have := fall_floor h v (Internal.exitQ tailC v.toNat + ((eventsF.map (Internal.syncDebit
        v.toNat)).sum +
          Internal.syncF eventsC v.toNat) + Internal.bandR (eventsF ++ eventsC) v.toNat) (by
        cases initial : fin.validators.data[v.toNat]? with
        | none => exact .inl rfl
        | some val =>
          have floor := V_floor h fromFin tailC
            (Internal.V_events h fromFin tailC high highC endEpoch endEpochC replayedF replayedC) v
              val
            initial clean
            (Internal.retained_of_exit h fromFin tailC _ (Nat.le_refl _) v foundU (by omega)) pre
              post cut
          exact .inr (by omega))
      omega
  · -- R activated the key after finalizing the split, so it reads the key as late
    have farAct : w.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
      rw [far] at activeW
      omega
    have eligible := Run.eligibility_le_finalized ((toFin.append fromFin).append toPulled)
      h.genesis v.toNat w foundW farAct
    have finCur := UInt64.le_iff_toNat_le.mp (Internal.finalized_le_current h)
    have late := (Internal.lateB_iff config pulled anc fin v.toNat).mpr ⟨w, foundW, by
      have := UInt64.le_iff_toNat_le.mp eligible
      simp only at this
      omega, by omega⟩
    simp only [late, ↓reduceIte]
    omega

/-- The fall of the V keys, and the stake of the V keys that left C's active set. -/
theorem cV_le (h : Setting config checks g split fin pulled anc counted V) (high : ℕ)
    (endEpoch : (getCurrentEpoch pulled).toNat ≤ high + 1) (events : List (BalanceEvent preset))
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    {eventsF : List (BalanceEvent preset)} (replayedF : fromFin.balanceEvents high = .ok eventsF)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1)
    {eventsC : List (BalanceEvent preset)} (replayedC : tailC.balanceEvents highC = .ok eventsC) :
    voterFallCost pulled counted V + inactiveVoterCost pulled counted V ≤
      ((∑ v ∈ V, (pinTerms config pulled anc fin).fall v.toNat) +
        (∑ v ∈ V, Internal.bandR (eventsF ++ eventsC) v.toNat) +
        (∑ v ∈ V, (Internal.syncD eventsF v.toNat + (Internal.syncF events v.toNat + Internal.syncF
          eventsC v.toNat))) +
        (∑ v ∈ V, Internal.credDepR events v.toNat) +
        (∑ v ∈ V, Internal.consAmt events v.toNat) + preset.upwardBand * Internal.dueAt fin high V +
        (∑ v ∈ (countedInactiveVoters counted V), Internal.exitQ tailC v.toNat) +
        (∑ v ∈ (countedInactiveVoters counted V) with
            (pinTerms config pulled anc fin).exitingB v.toNat = true,
          pulledBalance pulled v) +
        (∑ v ∈ (countedInactiveVoters counted V) with
            (pinTerms config pulled anc fin).lateB v.toNat = true,
          pulledBalance pulled v) : ℕ) := by
  have base := Internal.cV_le_of h tailC
    (V_active h fromFin tailC high highC endEpoch endEpochC replayedF replayedC)
    (V_left h fromFin tailC high highC endEpoch endEpochC replayedF replayedC)
  have sync : ∑ v ∈ V, ((eventsF.map (Internal.syncDebit v.toNat)).sum + Internal.syncF eventsC
    v.toNat) ≤
      ∑ v ∈ V, (Internal.syncD eventsF v.toNat + (Internal.syncF events v.toNat + Internal.syncF
        eventsC v.toNat)) :=
    Finset.sum_le_sum fun v _ => by unfold Internal.syncD; omega
  refine le_trans base (Int.ofNat_le.mpr ?_)
  simp only [Internal.syncD, Finset.sum_add_distrib] at sync ⊢
  omega

end Internal

end LowBound

end Terms
end PinDrift
end EthLib.Consensus.Models.Network
