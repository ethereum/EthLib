module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The closure test of the credit ceiling is arithmetic in the rate, the credits and the stake. -/
private theorem ceiling_closed (I WD F P e0 D Df Cr Cr' S W C q r : ℕ) (hDf : D ≤ Df)
    (hq : q = e0 / I * P * F / WD) (hr : r = P * F / WD) (hI : 0 < I)
    (hWD : 0 < WD) (alignedE : e0 % I = 0) (alignedC : C % I = 0)
    (hC : (11 * Cr' + 9) / 10 ≤ C)
    (small : Df * ((11 * q + 9) / 10 + 3) < I) (rateLow : 11 * D * (q + 1) ≤ e0)
    (start : S + Cr ≤ e0 + Cr' + W) (hW : W ≤ I) :
    S + Cr + (D * ((C + I - 1) / I * P * F / WD) + (D * q + D * (r + 2))) <
      e0 + C + I + I := by
  subst hq hr
  have key : 11 * D * (P * F) < WD * I := by
    rcases Nat.eq_zero_or_pos D with zero | pos
    · subst zero
      simpa using Nat.mul_pos hWD hI
    · obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero alignedE
      have e : e0 / I = m := by rw [hm, Nat.mul_div_cancel_left _ hI]
      have rate' := rateLow
      rw [e] at rate'
      have big : 11 ≤ e0 := Nat.le_trans (by
        have := Nat.mul_le_mul (show 11 ≤ 11 * D by omega)
          (Nat.le_add_left 1 (m * P * F / WD))
        simpa using this) rate'
      have mPos : 0 < m := Nat.pos_of_ne_zero (fun z => by rw [z] at hm; omega)
      have a : m * P * F < WD * (m * P * F / WD + 1) := Nat.lt_mul_div_succ _ hWD
      have b := Nat.mul_lt_mul_of_pos_left a (show 0 < 11 * D by omega)
      have d := Nat.mul_le_mul_left WD rate'
      have f : (11 * D * (P * F)) * m < (WD * I) * m := by
        calc (11 * D * (P * F)) * m = 11 * D * (m * P * F) := by ring
          _ < 11 * D * (WD * (m * P * F / WD + 1)) := b
          _ = WD * (11 * D * (m * P * F / WD + 1)) := by ring
          _ ≤ WD * e0 := d
          _ = (WD * I) * m := by rw [hm]; ring
      exact Nat.lt_of_mul_lt_mul_right f
  have gain : ∀ k, 11 * (D * (k * P * F / WD)) ≤ I * k := fun k => by
    have fl : WD * (k * P * F / WD) ≤ k * P * F := Nat.mul_div_le _ _
    have h1 : WD * (11 * (D * (k * P * F / WD))) ≤ WD * (I * k) := by
      calc WD * (11 * (D * (k * P * F / WD))) = 11 * D * (WD * (k * P * F / WD)) := by ring
        _ ≤ 11 * D * (k * P * F) := Nat.mul_le_mul_left _ fl
        _ = k * (11 * D * (P * F)) := by ring
        _ ≤ k * (WD * I) := Nat.mul_le_mul_left _ key.le
        _ = WD * (I * k) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hWD
  have cdiv : (C + I - 1) / I = C / I := by
    obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero alignedC
    rw [hu, Nat.mul_div_cancel_left _ hI,
      show I * u + I - 1 = I * u + (I - 1) by omega, Nat.mul_add_div hI,
      Nat.div_eq_of_lt (by omega)]
    simp
  have credit : 11 * (D * ((C + I - 1) / I * P * F / WD)) ≤ C := by
    rw [cdiv]
    have := gain (C / I)
    have e : I * (C / I) = C := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero alignedC)
    omega
  have base : 11 * (D * (e0 / I * P * F / WD)) + 30 * Df + 10 ≤ 10 * I := by
    have h1 : 11 * (e0 / I * P * F / WD) ≤ 10 * ((11 * (e0 / I * P * F / WD) + 9) / 10) := by
      omega
    have h2 : 11 * (D * (e0 / I * P * F / WD)) ≤
        10 * (D * ((11 * (e0 / I * P * F / WD) + 9) / 10)) :=
      calc 11 * (D * (e0 / I * P * F / WD)) = D * (11 * (e0 / I * P * F / WD)) := by ring
        _ ≤ D * (10 * ((11 * (e0 / I * P * F / WD) + 9) / 10)) := Nat.mul_le_mul_left _ h1
        _ = 10 * (D * ((11 * (e0 / I * P * F / WD) + 9) / 10)) := by ring
    have := small
    rw [Nat.mul_add] at this
    have mono : D * ((11 * (e0 / I * P * F / WD) + 9) / 10) ≤
        Df * ((11 * (e0 / I * P * F / WD) + 9) / 10) := Nat.mul_le_mul_right _ hDf
    omega
  have unit : 11 * (D * (P * F / WD)) < I := by
    have fl : WD * (P * F / WD) ≤ P * F := Nat.mul_div_le _ _
    have h1 : WD * (11 * (D * (P * F / WD))) < WD * I := by
      calc WD * (11 * (D * (P * F / WD))) = 11 * D * (WD * (P * F / WD)) := by ring
        _ ≤ 11 * D * (P * F) := Nat.mul_le_mul_left _ fl
        _ < WD * I := key
    exact Nat.lt_of_mul_lt_mul_left h1
  have split : D * (P * F / WD + 2) = D * (P * F / WD) + 2 * D := by ring
  rw [split]
  omega

/-- A bound that adds a start, a gain and the credits of a run, from a bound on each. -/
private theorem credit_sum_le {a k g N Cs S Cr G : ℕ} (start : a ≤ S) (credits : N + Cs ≤ Cr)
    (gain : k * g ≤ G) : a + k * g + N + Cs ≤ S + Cr + G := by omega

/-- A number below an aligned bound by less than an increment rounds down to at most the bound. -/
private theorem floor_le_of_lt {B E I : ℕ} (hI : 0 < I) (aligned : E % I = 0)
    (lt : B < E + I) : B - B % I ≤ E := by
  obtain ⟨u, hu⟩ := Nat.dvd_of_mod_eq_zero aligned
  have qlt : B / I < u + 1 := (Nat.div_lt_iff_lt_mul hI).mpr (by
    have : (u + 1) * I = E + I := by rw [hu]; ring
    omega)
  have mul : I * (B / I) ≤ I * u := Nat.mul_le_mul_left _ (by omega)
  have div := Nat.div_add_mod B I
  omega

/-- A key's balance along a run from a stake bound, the credits and the gain at the bound. -/
private theorem c_ceiling_abstract {n y : ForkedBeaconState preset}
    (post : Run config checks n y) (early : y.fork < .glamsterdam) (fulu : .fusaka ≤ n.fork)
    (i : ℕ) (inside : i < n.state.validators.data.size) (high P capHigh : ℕ)
    (alignedCap : capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt n i ≤ capHigh)
    (capCeil : ∀ z ∈ post.balancePath, PinSplit2.capAt z i ≤ capHigh)
    (rate : ∀ z ∈ post.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
    (endEpoch : (getCurrentEpoch y.state).toNat ≤ high + 1)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (depth depthFin Cr Cr' e0 C S W F q r : ℕ) (hDf : depth ≤ depthFin)
    (hF : F = (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum)
    (hq : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P * F / WEIGHT_DENOMINATOR.toNat)
    (hr : r = P * F / WEIGHT_DENOMINATOR.toNat)
    (alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (alignedC : C % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (hC : (11 * Cr' + 9) / 10 ≤ C)
    (epochs : (getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat ≤ depth)
    (startBal : min (actualBalanceAt n i) capHigh ≤ S)
    (startEff : effectiveAt n i ≤ e0 + C)
    (credits : netScan i high post +
      (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i high post).1 ≤ Cr)
    (small : depthFin * ((11 * q + 9) / 10 + 3) < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (rateLow : 11 * depth * (q + 1) ≤ e0)
    (start : S + Cr ≤ e0 + Cr' + W) (hW : W ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    ∀ z ∈ post.balancePath, min (actualBalanceAt z i) capHigh ≤ S + Cr +
      (gainOn preset depth P C + (depth * q + depth * (r + 2))) := by
  have weight : 0 < WEIGHT_DENOMINATOR.toNat := by decide
  have closed := ceiling_closed preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
    F P e0 depth depthFin Cr Cr' S W C q r hDf hq hr incPos weight alignedE0 alignedC hC small rateLow
    start hW
  subst hF
  have alignedE : (e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) %
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
    Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_add (Nat.dvd_of_mod_eq_zero alignedE0)
      (Nat.dvd_of_mod_eq_zero alignedC)) (Nat.dvd_refl _))
  have split := gain_split preset.EFFECTIVE_BALANCE_INCREMENT.toNat WEIGHT_DENOMINATOR.toNat
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum P e0 C
    ((getCurrentEpoch y.state).toNat - (getCurrentEpoch n.state).toNat) depth incPos epochs
  rw [← hq, ← hr] at split
  have bound : PinSplit2.creditBound post i high (e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      P capHigh ≤ S + Cr + (gainOn preset depth P C + (depth * q + depth * (r + 2))) := by
    unfold PinSplit2.creditBound
    exact credit_sum_le startBal credits split
  have fixpoint : max (effectiveAt n i) (min capHigh
      (PinSplit2.creditBound post i high (e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) P
          capHigh -
        PinSplit2.creditBound post i high (e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) P
          capHigh % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) ≤
      e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    max_le (Nat.le_trans startEff (Nat.le_add_right _ _))
      (Nat.le_trans (Nat.min_le_right _ _)
        (floor_le_of_lt incPos alignedE (Nat.lt_of_le_of_lt bound closed)))
  obtain ⟨-, -, -, fourth⟩ := PinSplit2.Run.effective_floor_pair post early fulu i inside 0 0
    capHigh high (e0 + C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat) P
  have balances := fourth alignedCap startCap capCeil rate endEpoch fixpoint
  intro z member
  exact Nat.le_trans (balances z member) bound


section Concrete

variable {g : ForkedBeaconState preset} {split fin pulled anc counted : BeaconState preset fork}
  {V : Finset ValidatorIndex}

/-- Rounding a credit up to an increment leaves its gain unchanged. -/
private theorem gainOn_round (depth P C : ℕ)
    (incPos : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat) :
    gainOn preset depth P (preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        ((C + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) = gainOn preset depth P C := by
  unfold gainOn
  generalize preset.EFFECTIVE_BALANCE_INCREMENT.toNat = I at *
  have : (I * ((C + I - 1) / I) + I - 1) / I = (C + I - 1) / I := by
    rw [show I * ((C + I - 1) / I) + I - 1 = I * ((C + I - 1) / I) + (I - 1) by omega,
      Nat.mul_add_div incPos, Nat.div_eq_of_lt (show I - 1 < I by omega)]
    simp
  rw [this]


open DirectSafety.Apriori.Internal in
/-- A key's balance on C's branch is at most R's balance, its debits, its credits and the gains. -/
private theorem c_ceiling (h : Setting config checks g split fin pulled anc counted V)
    (fromFin : Run config checks ⟨fork, fin⟩ ⟨fork, split⟩)
    (tailC : Run config checks ⟨fork, split⟩ ⟨fork, counted⟩) (highC : ℕ)
    (endEpochC : (getCurrentEpoch counted).toNat ≤ highC + 1) (P : ℕ)
    (hP : P = ((getBaseRewardPerIncrement preset
      (if 18 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
          ((getTotalActiveBalance pulled).toOption.getD 0).toNat then
        (getTotalActiveBalance pulled).toOption.getD 0 / 4
      else preset.EFFECTIVE_BALANCE_INCREMENT / 5)).toOption.getD 0).toNat)
    (i : ℕ) (inside : i < split.validators.data.size) (capI Dp Ds DsF W pd : ℕ)
    (hcap : capI = ((pulled.validators.data[i]?).map fun v =>
      (withdrawalMaxEffectiveBalance preset fork v).toNat).getD 0)
    (alignedCap : capI % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0)
    (startCap : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤ capI)
    (capCeil : ∀ z ∈ tailC.balancePath, PinSplit2.capAt z i ≤ capI)
    (startEff : effectiveAt (⟨fork, split⟩ : ForkedBeaconState preset) i ≤
      (pinTerms config pulled anc fin).ebUp i + DsF)
    (floorR : min (actualBalanceAt (⟨fork, split⟩ : ForkedBeaconState preset) i) capI ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
    (hW : W ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (debits : Dp ≤ ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
      (pinTerms config pulled anc fin).leakAt capI i + pd)
    (top : min capI (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (pinTerms config pulled anc fin).leakAt capI i + pd + preset.downwardBand) ≤
      (pinTerms config pulled anc fin).ebUp i)
    (small : ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
      ((11 * (pinTerms config pulled anc fin).gainRate i + 9) / 10 + 3) <
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (rateLow : 11 * (pinTerms config pulled anc fin).depth *
      ((pinTerms config pulled anc fin).gainRate i + 1) ≤ (pinTerms config pulled anc fin).ebUp i) :
    ∀ z ∈ tailC.balancePath, min (actualBalanceAt z i) capI ≤
      actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W +
        (netScan i highC tailC +
          (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tailC).1) +
        (gainOn preset (min (pinTerms config pulled anc fin).depth
            ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat)) P
          ((11 * (netScan i highC tailC +
            (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tailC).1 + Ds +
              DsF) + 9) / 10) +
          (min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (pinTerms config pulled anc fin).gainRate i +
          min (pinTerms config pulled anc fin).depth
              ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
            (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat + 2))) := by
  classical
  obtain ⟨shared⟩ := h.toFin
  obtain ⟨toPulled⟩ := h.toPulled
  have incPos := h.bands.1
  have near := h.near
  have finalized := UInt64.le_iff_toNat_le.mp h.finalized
  have finSplit : (getCurrentEpoch fin).toNat ≤ (getCurrentEpoch split).toNat :=
    epoch_le_of_slot_le fin.slot split.slot (Run.slot_le fromFin)
  have depthEq : (pinTerms config pulled anc fin).depth =
      (getCurrentEpoch pulled).toNat + 2 - anc.finalizedCheckpoint.epoch.toNat := rfl
  obtain ⟨Df, hDf⟩ : ∃ Df, Df =
      (getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat := ⟨_, rfl⟩
  rw [← hDf] at debits top small
  obtain ⟨D, hD⟩ : ∃ D, D = min (pinTerms config pulled anc fin).depth Df := ⟨_, rfl⟩
  rw [← hDf, ← hD]
  obtain ⟨e0, he0⟩ : ∃ e0, e0 = (pinTerms config pulled anc fin).ebUp i := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = (pinTerms config pulled anc fin).gainRate i := ⟨_, rfl⟩
  obtain ⟨Cr, hCr⟩ : ∃ Cr, Cr = netScan i highC tailC +
    (creditScan (fun _ => false) (fun s => decide (s ≠ .rewards)) i highC tailC).1 := ⟨_, rfl⟩
  rw [← he0] at top startEff rateLow
  rw [← hq] at small rateLow ⊢
  rw [← hCr]
  have hq' : q = e0 / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * P *
      (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat := by
    rw [hq, he0, hP]
    rfl
  obtain ⟨C, hC⟩ : ∃ C, C = preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
      ((((11 * (Cr + Ds + DsF) + 9) / 10) + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := ⟨_, rfl⟩
  have alignedC : C % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    rw [hC]
    exact Nat.mul_mod_right _ _
  have coverC : (11 * (Cr + Ds + DsF) + 9) / 10 ≤ C := by
    have div := Nat.div_add_mod (((11 * (Cr + Ds + DsF) + 9) / 10) +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    have lt := Nat.mod_lt (((11 * (Cr + Ds + DsF) + 9) / 10) +
      preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) incPos
    rw [hC]
    omega
  have alignedE0 : e0 % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
    obtain ⟨t, ht⟩ : ∃ t, (pinTerms config pulled anc fin).ebUp i =
        max (max (balanceAt pulled i) (balanceAt fin i))
          (min capI (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
      subst hcap
      exact ⟨_, rfl⟩
    have a1 : balanceAt pulled i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
      FloorTrace.effective_aligned (shared.append (fromFin.append toPulled)) h.genesis h.aligned i
    have a2 : balanceAt fin i % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 :=
      FloorTrace.effective_aligned shared h.genesis h.aligned i
    have a3 : (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) %
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := by
      have := Nat.div_add_mod t preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      rw [show t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat =
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat * (t / preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
        by omega]
      exact Nat.mul_mod_right _ _
    have pair : ∀ a b : ℕ, a % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
        b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 →
        max a b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 ∧
          min a b % preset.EFFECTIVE_BALANCE_INCREMENT.toNat = 0 := fun a b ha hb => by
      rcases le_total a b with l | l
      · rw [max_eq_right l, min_eq_left l]
        exact ⟨hb, ha⟩
      · rw [max_eq_left l, min_eq_right l]
        exact ⟨ha, hb⟩
    rw [he0, ht]
    exact (pair _ _ (pair _ _ a1 a2).1 ((pair _ _ alignedCap a3).2)).1
  have rateAll : ∀ z ∈ tailC.balancePath, ∀ total perIncrement : Gwei,
      getTotalActiveBalance z.state = .ok total →
      getBaseRewardPerIncrement preset total = .ok perIncrement →
      perIncrement.toNat * ((∑ j ∈ (getActiveValidatorIndices z.state
        (getPreviousEpoch z.state)).toFinset, effectiveAt z j.toNat) /
          preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
        P * (total.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    intro z member total perIncrement totalOk perOk
    by_cases anyOk : ∃ total perIncrement : Gwei,
        getBaseRewardPerIncrement preset total = .ok perIncrement
    swap
    · exact absurd ⟨total, perIncrement, perOk⟩ anyOk
    obtain ⟨t0, p0, p0ok⟩ := anyOk
    obtain ⟨pq, pqOk⟩ := quarter_base_ok h.facts p0ok
      ((getTotalActiveBalance pulled).toOption.getD 0)
    have Pq : P = pq.toNat := by
      rw [hP, pqOk]
      rfl
    obtain ⟨r1, r2, -⟩ := balancePath_endpoint tailC
      (Run.nil : Run config checks ⟨fork, counted⟩ ⟨fork, counted⟩) (Nat.le_refl _) member
    obtain ⟨mf, ms⟩ := z
    have above : fork ≤ mf := fork_le_of_chainSteps r1.chainSteps
    have below : mf ≤ fork := fork_le_of_chainSteps r2.chainSteps
    have same : mf = fork := Fork.ctorIdx_injective (Nat.le_antisymm below above)
    subst same
    have zEpoch : (getCurrentEpoch ms).toNat ≤ (getCurrentEpoch pulled).toNat + 1 := by
      have : (getCurrentEpoch ms).toNat ≤ (getCurrentEpoch counted).toNat :=
        epoch_le_of_slot_le ms.slot counted.slot (Run.slot_le r2)
      omega
    rw [Pq]
    exact rate_of_guard h (fromFin.append r1) zEpoch pqOk total perIncrement totalOk perOk
  have hDle : D ≤ (pinTerms config pulled anc fin).depth := hD ▸ min_le_left _ _
  have hDDf : D ≤ Df := hD ▸ min_le_right _ _
  have epochs : (getCurrentEpoch counted).toNat - (getCurrentEpoch split).toNat ≤ D := by
    rw [hD]
    refine Nat.le_min.mpr ⟨?_, ?_⟩
    · omega
    · omega
  have core := c_ceiling_abstract tailC h.early h.fulu i inside highC P capI alignedCap startCap
    capCeil rateAll endEpochC incPos D Df Cr (Cr + Ds + DsF) e0 C
    (min (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W) capI) W
    (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum q
    (P * (PARTICIPATION_FLAG_WEIGHTS.map (·.toNat)).sum / WEIGHT_DENOMINATOR.toNat) hDDf rfl hq'
    rfl alignedE0 alignedC coverC epochs (le_min floorR (min_le_right _ _)) (by omega)
    hCr.ge small (Nat.le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 11 hDle)) rateLow)
    (by omega) hW
  have rounded : gainOn preset D P C =
      gainOn preset D P ((11 * (Cr + Ds + DsF) + 9) / 10) := by
    rw [hC]
    exact gainOn_round D P _ incPos
  intro z member
  have bound := core z member
  rw [rounded] at bound
  have := min_le_left (actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i + Dp + Ds + W)
    capI
  omega

end Concrete

end PinSum
end EthLib.Consensus.Models.Network
