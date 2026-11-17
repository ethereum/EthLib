module

public import EthLib.Consensus.Proofs.DirectSafety.Apriori.Branch

/-!
# The proposer and sync credits of one epoch

The proposer rewards and the sync rewards of an epoch fit the issuance envelope of its total.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety.Apriori.Internal

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

noncomputable section

/-! ## The proposer and sync credits of one epoch

From Altair, an attestation pays its proposer for each flag that it newly sets.

Each flag of one validator and one epoch is set at most once, since no step clears it.

So the proposer credits of an epoch are bounded by a potential over two sets of keys.

The keys active at the previous epoch of a start `r`, and those active at its current epoch.

Each key weighs its base reward times the weights of the flags it holds.

A missing entry counts as every flag set, so that no step can lower the potential.

An attestation raises it by at least its numerator, which is `448` times its proposer credit.

Every other step keeps or raises it, and it never exceeds `54` times the base rewards.

The sync aggregate of each block pays at most the issuance envelope over `28` per slot.

A slot holds at most one block, so an epoch pays at most the envelope over `28` for sync.
-/

/-- The weights of the flags that are set. -/
def flagWeight (flags : ParticipationFlags) : Nat :=
  ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
    if hasFlag flags flag.val.toUInt64 then PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum

/-- The weight of an entry of the flags, with a missing entry counted as every flag set. -/
def entryWeight (entry : Option ParticipationFlags) : Nat :=
  (entry.map flagWeight).getD 54

/-- The flag potential of a state: the weighted flags of the two sets of keys.

Each key counts its base reward, in the flags of the previous epoch or of the current one. -/
def flagPotential (previous current : Finset ValidatorIndex) (base : ValidatorIndex → Nat)
    (u : ForkedBeaconState preset) : Nat :=
  if altair : .altair ≤ u.fork then
    ∑ i ∈ previous,
        entryWeight ((u.state.previousEpochParticipation altair).data[i.toNat]?) * base i +
      ∑ i ∈ current,
        entryWeight ((u.state.currentEpochParticipation altair).data[i.toNat]?) * base i
  else 0

/-- The credit limits of the events of one source. -/
def sourceCredits (source : BalanceSource) (events : List (BalanceEvent preset)) : Nat :=
  (events.map fun e => if e.source = source then e.creditLimit else 0).sum

theorem sourceCredits_append (source : BalanceSource)
    (first second : List (BalanceEvent preset)) :
    sourceCredits source (first ++ second) =
      sourceCredits source first + sourceCredits source second := by
  simp [sourceCredits]

/-- The debit limits of the events of one source. -/
def sourceDebits (source : BalanceSource) (events : List (BalanceEvent preset)) : Nat :=
  (events.map fun e => if e.source = source then e.debitLimit else 0).sum

theorem sourceDebits_append (source : BalanceSource)
    (first second : List (BalanceEvent preset)) :
    sourceDebits source (first ++ second) =
      sourceDebits source first + sourceDebits source second := by
  simp [sourceDebits]

private theorem finRange_flags :
    List.finRange PARTICIPATION_FLAG_WEIGHTS.length =
      [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩] := rfl

private theorem flagWeights_sum :
    PARTICIPATION_FLAG_WEIGHTS[(⟨0, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨1, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat +
      PARTICIPATION_FLAG_WEIGHTS[(⟨2, by decide⟩ : Fin PARTICIPATION_FLAG_WEIGHTS.length)].toNat =
      54 := rfl

/-- An entry weighs at most `54`, the sum of the weights. -/
private theorem entryWeight_le (entry : Option ParticipationFlags) : entryWeight entry ≤ 54 := by
  cases entry with
  | none => exact Nat.le_refl _
  | some flags =>
    have weights := flagWeights_sum
    simp only [entryWeight, Option.map_some, Option.getD_some, flagWeight, finRange_flags,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    split <;> split <;> split <;> omega

/-- Setting the earned flags raises the weight by the weights of the newly set ones. -/
private theorem flagWeight_set {old new : ParticipationFlags} {earned : List UInt64}
    (set : ∀ flag : Fin PARTICIPATION_FLAG_WEIGHTS.length, hasFlag new flag.val.toUInt64 =
      (hasFlag old flag.val.toUInt64 || decide (flag.val.toUInt64 ∈ earned))) (base : Nat) :
    flagWeight new * base = flagWeight old * base +
      ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
        if flag.val.toUInt64 ∈ earned ∧ hasFlag old flag.val.toUInt64 = false then
          base * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum := by
  -- Each flag adds its weight once set, and it is newly set when earned and not held before.
  have term (held : Bool) (earnedFlag : Prop) [Decidable earnedFlag] (weight : Nat) :
      (if (held || decide earnedFlag) = true then weight else 0) * base =
        (if held = true then weight else 0) * base +
          (if earnedFlag ∧ held = false then base * weight else 0) := by
    cases held <;> by_cases chosen : earnedFlag <;> simp [chosen, Nat.mul_comm]
  have zero := set ⟨0, by decide⟩
  have one := set ⟨1, by decide⟩
  have two := set ⟨2, by decide⟩
  simp only [flagWeight, finRange_flags, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.add_mul]
  rw [zero, one, two, term, term, term]
  ring

/-- Setting the flags of some attesters raises the weighted flags of a set of keys.

The rise is at least the numerator of the attestation.

The keys must hold every attester.

Each base reward that the attestation reads must be at most the key's own. -/
private theorem participation_gain {f : Fork} {s : BeaconState preset f} {total : Gwei}
    {earned : List UInt64} {attesters : List ValidatorIndex}
    {participation : EpochParticipation preset f} {result : EpochParticipation preset f × Gwei}
    (distinct : (attesters.map UInt64.toNat).Nodup)
    (computed : attesters.foldlM (addAttesterFlags s total earned) (participation, 0) =
      .ok result)
    (keys : Finset ValidatorIndex) (base : ValidatorIndex → Nat)
    (among : ∀ a ∈ attesters, a ∈ keys)
    (based : ∀ a ∈ attesters, ∀ reward, getBaseReward s total a = .ok reward →
      reward.toNat ≤ base a) :
    ∑ i ∈ keys, entryWeight (participation.data[i.toNat]?) * base i + result.2.toNat ≤
      ∑ i ∈ keys, entryWeight (result.1.data[i.toNat]?) * base i := by
  classical
  obtain ⟨keptOthers, shares, named, facts, sum⟩ := foldlM_addAttesterFlags distinct computed
  have flagsAfter := foldlM_addAttesterFlags_hasFlag distinct computed
  -- The weights of the flags that the attestation sets for one attester.
  let gain (a : ValidatorIndex) : Nat :=
    ((List.finRange PARTICIPATION_FLAG_WEIGHTS.length).map fun flag =>
      if flag.val.toUInt64 ∈ earned ∧
          hasFlag ((participation.data[a.toNat]?).getD 0) flag.val.toUInt64 = false then
        base a * PARTICIPATION_FLAG_WEIGHTS[flag].toNat else 0).sum
  -- The numerator reads a base reward only for a newly set flag, so it is at most the gain.
  have shared : result.2.toNat ≤ ∑ a ∈ attesters.toFinset, gain a := by
    rw [sum, List.sum_toFinset _ (List.Nodup.of_map _ distinct), ← named, List.map_map]
    simp only [UInt64.toNat_zero, Nat.zero_add]
    apply List.sum_le_sum
    intro share member
    obtain ⟨found, reads⟩ := facts share member
    have inside : share.1 ∈ attesters := named ▸ List.mem_map_of_mem member
    simp only [Function.comp, gain, found, Option.getD_some, newFlagsNumerator]
    apply List.sum_le_sum
    intro flag _
    split_ifs with newly
    · exact Nat.mul_le_mul_right _ (based share.1 inside _ (reads flag newly.1 newly.2))
    · exact Nat.le_refl _
  -- Each attester gains exactly its newly set flags, and every other key keeps its entry.
  have each (i : ValidatorIndex) : entryWeight (participation.data[i.toNat]?) * base i +
      (if i ∈ attesters.toFinset then gain i else 0) ≤
      entryWeight (result.1.data[i.toNat]?) * base i := by
    split_ifs with chosen
    · obtain ⟨old, new, found, after, set⟩ := flagsAfter i (List.mem_toFinset.mp chosen)
      simp only [entryWeight, found, after, Option.map_some, Option.getD_some, gain]
      rw [flagWeight_set set]
    · rw [keptOthers i.toNat fun a member same =>
        chosen (List.mem_toFinset.mpr (UInt64.toNat_inj.mp same ▸ member)), Nat.add_zero]
  calc ∑ i ∈ keys, entryWeight (participation.data[i.toNat]?) * base i + result.2.toNat
      ≤ ∑ i ∈ keys, entryWeight (participation.data[i.toNat]?) * base i +
          ∑ i ∈ keys, (if i ∈ attesters.toFinset then gain i else 0) := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr fun a member =>
          among a (List.mem_toFinset.mp member)]
        exact Nat.add_le_add_left shared _
    _ = ∑ i ∈ keys, (entryWeight (participation.data[i.toNat]?) * base i +
          (if i ∈ attesters.toFinset then gain i else 0)) := Finset.sum_add_distrib.symm
    _ ≤ _ := Finset.sum_le_sum fun i _ => each i

/-- An attestation raises the flag potential by at least `448` times its proposer credit.

Its attesters are active at its target, the previous or the current epoch of its state.

So they lie in the sets of keys, if those hold the active keys of the two epochs. -/
private theorem attestation_flagPotential {f : Fork} {u u' : BeaconState preset f}
    (early : f < .glamsterdam) (altair : .altair ≤ f)
    {att : Attestation preset f} {parent : Slot} {credit : Nat}
    (ok : processAttestation config checks u parent att = .ok u')
    (credited : attestationCredit u att parent = .ok credit)
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (previousActive : ∀ i ∈ getActiveValidatorIndices u (getPreviousEpoch u), i ∈ previous)
    (currentActive : ∀ i ∈ getActiveValidatorIndices u (getCurrentEpoch u), i ∈ current)
    (based : ∀ total i reward, i ∈ previous ∨ i ∈ current →
      getTotalActiveBalance u = .ok total → getBaseReward u total i = .ok reward →
      reward.toNat ≤ base i) :
    flagPotential previous current base ⟨f, u⟩ + 448 * credit ≤
      flagPotential previous current base ⟨f, u'⟩ := by
  rw [processAttestation_of_altair altair] at ok
  simp only [processAttestationAltair, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, recent, _, slotEpoch, _, _, _, _, _, _, _, _, earned, earnedOk, _, _, _, _, _, _,
    total, totalOk, attesters, attestersOk, pair, flagsOk, proposer, _, raisedState, raised,
    final⟩ := ok
  rw [ensure_ok_iff] at recent slotEpoch
  have notGloas : ¬ .glamsterdam ≤ f := Nat.not_le_of_lt early
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at final
  subst final
  -- The credit is the numerator over `448`, rounding down.
  have value : attestationCredit u att parent = .ok (pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat := by
    simp only [attestationCredit, altair, ↓reduceDIte, liftAccessor, earnedOk, totalOk,
      attestersOk, Except.mapError, bind, Except.bind, flagsOk]
    rfl
  obtain rfl := Except.ok.inj (credited.symm.trans value)
  have scaled : 448 * (pair.2 /
      ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR / PROPOSER_WEIGHT)).toNat ≤
      pair.2.toNat := by
    rw [UInt64.toNat_div, show ((WEIGHT_DENOMINATOR - PROPOSER_WEIGHT) * WEIGHT_DENOMINATOR /
      PROPOSER_WEIGHT : UInt64).toNat = 448 from rfl, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  obtain ⟨_, set⟩ := increaseBalance_ok raised
  obtain ⟨_, rfl⟩ := setBalance_ok set
  have distinct := getAttestingIndices_nodup attestersOk
  -- Each attester is in a committee of the target, so it is active at the target.
  have active (a : ValidatorIndex) (member : a ∈ attesters) :
      a ∈ getActiveValidatorIndices u att.data.target.epoch := by
    obtain ⟨_, _, _, committeeOk, inCommittee⟩ :=
      exists_mem_getBeaconCommittee_of_getAttestingIndices attestersOk member
    rw [slotEpoch]
    exact mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk inCommittee
  have reads (keys : Finset ValidatorIndex) (inKeys : ∀ a ∈ attesters, a ∈ keys)
      (side : ∀ a ∈ keys, a ∈ previous ∨ a ∈ current) :
      ∀ a ∈ attesters, ∀ reward, getBaseReward u total a = .ok reward → reward.toNat ≤ base a :=
    fun a member reward rewardOk => based total a reward (side a (inKeys a member)) totalOk rewardOk
  simp only [flagPotential, altair, ↓reduceDIte, BeaconState.putBalance]
  by_cases chosen : (att.data.target.epoch == getCurrentEpoch u) = true
  · -- The attestation sets flags of the current epoch.
    have target : att.data.target.epoch = getCurrentEpoch u := beq_iff_eq.mp chosen
    simp only [chosen, ↓reduceIte] at flagsOk
    have inKeys (a : ValidatorIndex) (member : a ∈ attesters) : a ∈ current :=
      currentActive a (target ▸ active a member)
    have gain := participation_gain distinct flagsOk current base inKeys
      (reads current inKeys fun _ member => .inr member)
    simp only [setEpochParticipation, chosen, ↓reduceIte]
    omega
  · -- The attestation sets flags of the previous epoch.
    have target : att.data.target.epoch = getPreviousEpoch u :=
      recent.resolve_right fun same => chosen (beq_iff_eq.mpr same)
    simp only [chosen, Bool.false_eq_true, ↓reduceIte] at flagsOk
    have inKeys (a : ValidatorIndex) (member : a ∈ attesters) : a ∈ previous :=
      previousActive a (target ▸ active a member)
    have gain := participation_gain distinct flagsOk previous base inKeys
      (reads previous inKeys fun _ member => .inl member)
    simp only [setEpochParticipation, chosen, Bool.false_eq_true, ↓reduceIte]
    omega

/-- A step that keeps or zeroes each byte of flags keeps or raises the flag potential.

The keys must be inside the registry before the step, where no byte is zeroed. -/
private theorem flagPotential_le_of_flags {f : Fork} {a b : BeaconState preset f}
    (flags : FlagsKeptOrZero a b) {previous current : Finset ValidatorIndex}
    {base : ValidatorIndex → Nat} (inside : ∀ i ∈ previous ∪ current,
      i.toNat < a.validators.data.size) :
    flagPotential previous current base ⟨f, a⟩ ≤ flagPotential previous current base ⟨f, b⟩ := by
  simp only [flagPotential]
  split
  · rename_i altair
    -- An entry kept by the step weighs as before, and a missing one weighs the most.
    have entry {before after : Option ParticipationFlags} (position : Nat)
        (small : position < a.validators.data.size)
        (read : ∀ value, after = some value →
          before = some value ∨ value = 0 ∧ a.validators.data.size ≤ position) :
        entryWeight before ≤ entryWeight after := by
      cases found : after with
      | none => exact entryWeight_le _
      | some value =>
        rcases read value found with same | ⟨_, late⟩
        · rw [same]
        · omega
    apply Nat.add_le_add
    · exact Finset.sum_le_sum fun i member => Nat.mul_le_mul_right _
        (entry i.toNat (inside i (Finset.mem_union_left _ member))
          fun value => (flags altair i.toNat value).1)
    · exact Finset.sum_le_sum fun i member => Nat.mul_le_mul_right _
        (entry i.toNat (inside i (Finset.mem_union_right _ member))
          fun value => (flags altair i.toNat value).2)
  · exact Nat.le_refl _

/-- No event of a list is a penalty or an inactivity event. -/
def PenaltyFree (events : List (BalanceEvent preset)) : Prop :=
  ∀ e ∈ events, e.source ≠ .penalties ∧ e.source ≠ .inactivity

theorem PenaltyFree.append {left right : List (BalanceEvent preset)}
    (one : PenaltyFree left) (two : PenaltyFree right) : PenaltyFree (left ++ right) :=
  fun e member => (List.mem_append.mp member).elim (one e) (two e)

/-- The facts that a replay of a block keeps, from the start `b` of the block.

The potential rises by `448` times the proposer credits.

No sync credit and no sync debit is recorded yet, and no penalty or inactivity event.

The registry does not shrink. -/
def BlockKept {f : Fork} (b : BeaconState preset f)
    (previous current : Finset ValidatorIndex)
    (base : ValidatorIndex → Nat) (pre : BalanceReplay preset f) : Prop :=
  flagPotential previous current base ⟨f, b⟩ + 448 * sourceCredits .rewards pre.2 ≤
      flagPotential previous current base ⟨f, pre.1⟩ ∧
    sourceCredits .sync pre.2 = 0 ∧ sourceDebits .sync pre.2 = 0 ∧
    b.validators.data.size ≤ pre.1.validators.data.size ∧ PenaltyFree pre.2

/-- A replayed step that forms a block frame and records no reward, sync credit or sync debit. -/
theorem BlockKept.step {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {pre : BalanceReplay preset f} {u : BeaconState preset f} {added : List (BalanceEvent preset)}
    (held : BlockKept b previous current base pre) (frame : BlockFrame pre.1 u)
    (quiet : sourceCredits .rewards added = 0) (silent : sourceCredits .sync added = 0)
    (mute : sourceDebits .sync added = 0) (free : PenaltyFree added) :
    BlockKept b previous current base (u, pre.2 ++ added) := by
  have raised := flagPotential_le_of_flags (base := base) frame.flags
    fun i member => Nat.lt_of_lt_of_le (inside i member) held.2.2.2.1
  refine ⟨?_, ?_, ?_, held.2.2.2.1.trans frame.registryGrows, held.2.2.2.2.append free⟩
  · simp only [sourceCredits_append, quiet, Nat.add_zero]
    exact held.1.trans raised
  · simp only [sourceCredits_append, silent, held.2.1]
  · simp only [sourceDebits_append, mute, held.2.2.1]

private theorem BlockKept.carry {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (frame : ∀ x y, action x = .ok y → BlockFrame x y) {pre post : BalanceReplay preset f}
    (ok : carryBalance action pre = .ok post) (held : BlockKept b previous current base pre) :
    BlockKept b previous current base post := by
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨u, computed, rfl⟩ := ok
  have kept := held.step inside (frame _ _ computed) (added := []) rfl rfl rfl
    (by simp [PenaltyFree])
  rwa [List.append_nil] at kept

private theorem BlockKept.record {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (frame : ∀ x y, action x = .ok y → BlockFrame x y) {pre post : BalanceReplay preset f}
    (ok : recordBalance source limits action pre = .ok post)
    (other : source ≠ .rewards ∧ source ≠ .sync ∧ source ≠ .penalties ∧ source ≠ .inactivity)
    (held : BlockKept b previous current base pre) : BlockKept b previous current base post := by
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, u, computed, rfl⟩ := ok
  exact held.step inside (frame _ _ computed) (by simp [sourceCredits, other.1])
    (by simp [sourceCredits, other.2.1]) (by simp [sourceDebits, other.2.1])
    (by simp [PenaltyFree, other.2.2])

private theorem BlockKept.fold {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat} {α : Type}
    {step : BalanceReplay preset f → α → Except TransitionError (BalanceReplay preset f)}
    (kept : ∀ pre x post, step pre x = .ok post → BlockKept b previous current base pre →
      BlockKept b previous current base post)
    {items : List α} {pre post : BalanceReplay preset f} (ok : items.foldlM step pre = .ok post)
    (held : BlockKept b previous current base pre) : BlockKept b previous current base post :=
  foldlM_ok_invariant (BlockKept b previous current base) (fun _ _ _ prior computed =>
    kept _ _ _ computed prior) held ok

/-- The steps of a block before its attestations keep the effective balances and the activity. -/
def SiteKept {f : Fork} (b : BeaconState preset f) (pre : BalanceReplay preset f) : Prop :=
  EffectiveKept b pre.1 ∧ ActiveStep b pre.1 ∧ b.validators.data.size ≤ pre.1.validators.data.size

/-- A step of a block that keeps the effective balances and the activity, and is a block frame. -/
private def SiteStep {f : Fork} (x y : BeaconState preset f) : Prop :=
  BlockFrame x y ∧ EffectiveKept x y ∧ ActiveStep x y

theorem SiteKept.step {f : Fork} {b : BeaconState preset f}
    {pre : BalanceReplay preset f} {u : BeaconState preset f} (held : SiteKept b pre)
    (effective : EffectiveKept pre.1 u) (active : ActiveStep pre.1 u)
    (grows : pre.1.validators.data.size ≤ u.validators.data.size)
    (added : List (BalanceEvent preset)) : SiteKept b (u, added) :=
  ⟨effectiveKept_trans held.1 effective held.2.2, held.2.1.trans active, held.2.2.trans grows⟩

private theorem SiteKept.carry {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (step : ∀ x y, action x = .ok y → SiteStep x y) {pre post : BalanceReplay preset f}
    (ok : carryBalance action pre = .ok post)
    (held : BlockKept b previous current base pre ∧ SiteKept b pre) :
    BlockKept b previous current base post ∧ SiteKept b post := by
  refine ⟨held.1.carry inside (fun x y computed => (step x y computed).1) ok, ?_⟩
  simp only [carryBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨u, computed, rfl⟩ := ok
  have kept := step _ _ computed
  exact held.2.step kept.2.1 kept.2.2 kept.1.registryGrows _

private theorem SiteKept.record {f : Fork} {b : BeaconState preset f}
    {previous current : Finset ValidatorIndex} {base : ValidatorIndex → Nat}
    (inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    {source : BalanceSource}
    {limits : BeaconState preset f → Except TransitionError (Nat × Nat)}
    {action : BeaconState preset f → Except TransitionError (BeaconState preset f)}
    (step : ∀ x y, action x = .ok y → SiteStep x y) {pre post : BalanceReplay preset f}
    (ok : recordBalance source limits action pre = .ok post)
    (other : source ≠ .rewards ∧ source ≠ .sync ∧ source ≠ .penalties ∧ source ≠ .inactivity)
    (held : BlockKept b previous current base pre ∧ SiteKept b pre) :
    BlockKept b previous current base post ∧ SiteKept b post := by
  refine ⟨held.1.record inside (fun x y computed => (step x y computed).1) ok other, ?_⟩
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
  obtain ⟨_, _, u, computed, rfl⟩ := ok
  have kept := step _ _ computed
  exact held.2.step kept.2.1 kept.2.2 kept.1.registryGrows _

/-- Move a fork-conditional replay before its common continuation. -/
private theorem except_dite_bind {α β : Type} (p : Prop) [Decidable p]
    (yes : p → Except TransitionError α) (no : ¬p → Except TransitionError α)
    (next : α → Except TransitionError β) :
    (if h : p then yes h >>= next else no h >>= next) =
      ((if h : p then yes h else no h) >>= next) := by
  split <;> rfl

/-- The replay of one block raises the flag potential by `448` times its proposer credits.

Its sync credit, times `28` per slot of an epoch, is at most the issuance envelope of the total.

That total is the one after the block, which the sync aggregate reads.

Its sync debit limit is at most its sync credit limit, and it records no penalty event.

Each attestation must raise the potential, at every state that keeps the start of the block. -/
private theorem block_credits_generic {f : Fork} {b t : BeaconState preset f}
    (early : f < .glamsterdam) (altair : .altair ≤ f)
    {engine : ExecutionEngine preset f} {block : BeaconBlock preset f}
    {events : List (BalanceEvent preset)}
    (replay : blockBalanceReplay (config := config) (checks := checks) early engine b block =
      .ok (t, events)) :
    ∃ total perIncrement, getTotalActiveBalance t = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement ∧
      ∀ (previous current : Finset ValidatorIndex) (base : ValidatorIndex → Nat)
    (_inside : ∀ i ∈ previous ∪ current, i.toNat < b.validators.data.size)
    (_attest : ∀ {u u' : BeaconState preset f} {att : Attestation preset f} {credit : Nat},
      EffectiveKept b u → ActiveStep b u →
      processAttestation config checks u b.latestBlockHeader.slot att = .ok u' →
      attestationCredit u att b.latestBlockHeader.slot = .ok credit →
      flagPotential previous current base ⟨f, u⟩ + 448 * credit ≤
        flagPotential previous current base ⟨f, u'⟩),
    flagPotential previous current base ⟨f, b⟩ + 448 * sourceCredits .rewards events ≤
        flagPotential previous current base ⟨f, t⟩ ∧
      sourceCredits .sync events * (28 * preset.SLOTS_PER_EPOCH.toNat) ≤
        preset.epochIssuanceBeforeAltair total.toNat ∧
      sourceDebits .sync events ≤ sourceCredits .sync events ∧
      0 < preset.SLOTS_PER_EPOCH.toNat ∧ PenaltyFree events := by
  have normalized := replay
  unfold blockBalanceReplay at normalized
  simp only [altair, ↓reduceDIte] at normalized
  simp only [← bind_assoc, except_dite_bind] at normalized
  simp only [bind_assoc] at normalized
  simp only [bind_ok_iff, ensure_ok_iff] at normalized
  obtain ⟨headed, headedOk, executed, executedOk, revealed, revealedOk, voted, votedOk, _, _, _,
    _, proposed, proposedOk, slashed, slashedOk, attested, attestedOk, deposited, depositedOk,
    exited, exitedOk, changed, changedOk, consolidated, requestsOk, syncOk⟩ := normalized
  simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at syncOk
  obtain ⟨⟨credit, debit⟩, limitsOk, u, synced, rfl, rfl⟩ := syncOk
  obtain ⟨balances, rfl⟩ := processSyncAggregate_eq synced
  obtain ⟨reward, rewardOk, proposer, proposerOk, rfl, rfl⟩ := limitsOk
  have reads := rewardOk
  simp only [syncParticipantReward, bind_ok_iff, liftAccessor_ok] at reads
  obtain ⟨total, totalEnd, perIncrement, per, _⟩ := reads
  refine ⟨total, perIncrement, totalEnd, per, ?_⟩
  intro previous current base inside attest
  have start : BlockKept b previous current base (b, []) ∧ SiteKept b (b, []) :=
    ⟨⟨by simp [sourceCredits], rfl, rfl, Nat.le_refl _, by simp [PenaltyFree]⟩,
      effectiveKept_refl _, .refl _,
      Nat.le_refl _⟩
  -- The steps before the attestations keep the effective balances and the activity.
  have one := SiteKept.carry inside (fun _ _ ok => ⟨frame_processBlockHeader ok,
    effectiveKept_data (by obtain ⟨_, _, same⟩ := processBlockHeader_eq ok; rw [same]),
    activeStep_processBlockHeader ok⟩) headedOk start
  have two : BlockKept b previous current base executed ∧ SiteKept b executed := by
    split at executedOk
    · exact SiteKept.record inside (fun _ _ ok =>
        ⟨frame_processBlockExecution ok,
          effectiveKept_data (congrArg (·.data) (processBlockExecution_validators ok)),
          activeStep_processBlockExecution ok⟩) executedOk (by decide) one
    · cases executedOk
      exact one
  have three := SiteKept.carry inside (fun _ _ ok => ⟨frame_processRandao ok,
    effectiveKept_data (by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := processRandao_eq ok
      rw [same]), activeStep_processRandao ok⟩) revealedOk two
  have four := SiteKept.carry inside (fun _ _ ok => ⟨frame_processEth1Data ok,
    by obtain ⟨_, _, rest⟩ := processEth1Data_eq ok
       exact effectiveKept_data (congrArg (·.validators.data) rest),
    activeStep_processEth1Data ok⟩) votedOk three
  have five := foldlM_ok_invariant
    (fun pre => BlockKept b previous current base pre ∧ SiteKept b pre)
    (fun _ _ _ prior computed => SiteKept.record inside (fun _ _ ok =>
      ⟨frame_processProposerSlashing ok, effectiveKept_proposerSlashing ok,
        activeStep_processProposerSlashing ok⟩) computed (by decide) prior)
    four proposedOk
  have six := foldlM_ok_invariant
    (fun pre => BlockKept b previous current base pre ∧ SiteKept b pre)
    (fun _ _ _ prior computed => SiteKept.record inside (fun _ _ ok =>
      ⟨frame_processAttesterSlashing ok, effectiveKept_attesterSlashing ok,
        activeStep_processAttesterSlashing ok⟩) computed (by decide) prior)
    five slashedOk
  -- Each attestation raises the potential by `448` times the credit that it records.
  have seven := foldlM_ok_invariant
    (fun pre => BlockKept b previous current base pre ∧ SiteKept b pre)
    (fun pre _ _ prior computed => by
      simp only [recordBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨⟨credit, debit⟩, limitsOk, u, processed, rfl⟩ := computed
      obtain ⟨_, creditOk, rfl, rfl⟩ := limitsOk
      have raised := attest prior.2.1 prior.2.2.1 processed creditOk
      have before := prior.1.1
      refine ⟨⟨?_, ?_, ?_, prior.1.2.2.2.1.trans (frame_processAttestation processed).registryGrows,
        prior.1.2.2.2.2.append (by simp [PenaltyFree])⟩,
        prior.2.step (effectiveKept_data (by rw [(processAttestation_registry processed).1]))
          (activeStep_processAttestation processed)
          (frame_processAttestation processed).registryGrows _⟩
      · simp only [sourceCredits_append] at before ⊢
        simp only [sourceCredits, List.map_cons, List.map_nil, ↓reduceIte, List.sum_cons,
          List.sum_nil, Nat.add_zero] at before ⊢
        omega
      · simp only [sourceCredits_append, prior.1.2.1]
        simp [sourceCredits]
      · simp only [sourceDebits_append, prior.1.2.2.1]
        simp [sourceDebits]) six attestedOk
  -- The steps after the attestations are block frames that record no credit of either kind.
  have eight := BlockKept.fold (fun _ _ _ computed prior => prior.record inside
    (fun _ _ ok => frame_processDeposit ok) computed (by decide)) depositedOk seven.1
  have nine := BlockKept.carry inside (fun _ _ ok => by
    rw [← Array.foldlM_toList] at ok
    exact BlockFrame.foldlM (fun _ _ _ h => frame_processVoluntaryExit h) ok) exitedOk eight
  have ten := BlockKept.carry inside (fun _ _ ok => by
    unfold processBlsToExecutionChanges at ok
    split at ok
    · rw [← Array.foldlM_toList] at ok
      exact BlockFrame.foldlM (fun _ _ _ h => frame_processBlsToExecutionChange h) ok
    · cases ok
      exact .refl _) changedOk nine
  have thirteen : BlockKept b previous current base consolidated := by
    split at requestsOk
    · simp only [bind_ok_iff] at requestsOk
      obtain ⟨requested, requestedOk, withdrawn, withdrawnOk, consolidatedOk⟩ := requestsOk
      have eleven := BlockKept.carry inside (fun _ _ ok => by
        rw [← Array.foldlM_toList] at ok
        exact BlockFrame.foldlM (fun _ _ _ h => frame_processDepositRequest h) ok) requestedOk ten
      have twelve := BlockKept.carry inside (fun _ _ ok => by
        rw [← Array.foldlM_toList] at ok
        exact BlockFrame.foldlM (fun _ _ _ h => frame_processWithdrawalRequest h) ok)
        withdrawnOk eleven
      exact BlockKept.fold (fun _ _ _ computed prior => prior.record inside
        (fun _ _ ok => frame_processConsolidationRequest ok) computed (by decide))
        consolidatedOk twelve
    · cases requestsOk
      exact ten
  -- The sync aggregate changes only the balances, and records the one sync credit.
  simp only [liftAccessor_ok, liftArith, mapError_ok_iff, bind_ok_iff, mulChecked_ok_iff,
    divChecked_ok_iff] at proposerOk
  obtain ⟨scaled, ⟨_, scaledValue⟩, _, proposerValue⟩ := proposerOk
  have share : proposer.toNat * 7 ≤ reward.toNat := by
    rw [proposerValue, scaledValue, show PROPOSER_WEIGHT.toNat = 8 from rfl,
      show (WEIGHT_DENOMINATOR - PROPOSER_WEIGHT).toNat = 56 from rfl]
    omega
  obtain ⟨bound, positive⟩ := syncCredit_le rewardOk share totalEnd
  refine ⟨?_, ?_, ?_, positive, thirteen.2.2.2.2.append (by simp [PenaltyFree])⟩
  · calc _ = flagPotential previous current base ⟨f, b⟩ +
          448 * sourceCredits .rewards consolidated.2 := by
          simp [sourceCredits]
      _ ≤ flagPotential previous current base ⟨f, consolidated.1⟩ := thirteen.1
      _ = _ := rfl
  · simp only [sourceCredits_append, thirteen.2.1, Nat.zero_add]
    simpa [sourceCredits] using bound
  · -- The sync debit is the members' rewards, and the credit adds the proposer's shares.
    simp only [sourceCredits_append, sourceDebits_append, thirteen.2.1, thirteen.2.2.1,
      Nat.zero_add]
    simpa [sourceCredits, sourceDebits] using
      Nat.mul_le_mul_left preset.SYNC_COMMITTEE_SIZE.toNat (Nat.le_add_right _ proposer.toNat)

/-- A step of a run inside an epoch from Electra raises the flag potential by its proposer credits.

The potential reads the keys active at the previous and the current epoch of the start `r`.

Each key weighs its base reward at the total of `r`.

A slot step records no credit and moves the slot on, keeping the slot of the latest header.

A block step stays at its slot, after the slot of the latest header, and makes that header its own.

Its sync credit, times `28` per slot of an epoch, is at most the issuance envelope of the total.

The sync debit limit of each step is at most its sync credit limit.

No step records a penalty or an inactivity event. -/
private theorem step_credits_generic {r m l : ForkedBeaconState preset}
    (pre : Run config checks r m)
    (step : Step config checks m l) (altairR : .altair ≤ r.fork) (early : l.fork < .glamsterdam)
    (same : getCurrentEpoch l.state = getCurrentEpoch r.state)
    (prefixEffective : ∀ i, i < r.state.validators.data.size → effectiveAt m i = effectiveAt r i)
    {added : List (BalanceEvent preset)} (addedOk : step.balanceEvents = .ok added) :
    (∀ i, i < r.state.validators.data.size → effectiveAt l i = effectiveAt r i) ∧
    ((∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
      (sourceCredits .rewards added = 0 ∧ sourceCredits .sync added = 0 ∧
        sourceDebits .sync added = 0 ∧ PenaltyFree added)) ∧
    ∀ (total perIncrement : Gwei) (_totalOk : getTotalActiveBalance r.state = .ok total)
    (_per : getBaseRewardPerIncrement preset total = .ok perIncrement)
    (previous current : Finset ValidatorIndex) (base : ValidatorIndex → Nat)
    (_previousEq :
      previous = (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset)
    (_currentEq : current = (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset)
    (_baseEq : ∀ i, base i =
      effectiveAt r i.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat),
    flagPotential previous current base m + 448 * sourceCredits .rewards added ≤
        flagPotential previous current base l ∧
      sourceDebits .sync added ≤ sourceCredits .sync added ∧
      ((sourceCredits .sync added = 0 ∧ l.state.slot.toNat = m.state.slot.toNat + 1 ∧
          l.state.latestBlockHeader.slot = m.state.latestBlockHeader.slot) ∨
        (sourceCredits .sync added * (28 * preset.SLOTS_PER_EPOCH.toNat) ≤
            preset.epochIssuanceBeforeAltair total.toNat ∧ 0 < preset.SLOTS_PER_EPOCH.toNat ∧
          l.state.slot = m.state.slot ∧
          m.state.latestBlockHeader.slot.toNat < m.state.slot.toNat ∧
          l.state.latestBlockHeader.slot = l.state.slot)) ∧
      PenaltyFree added := by
  have mEarly : m.fork < .glamsterdam := Nat.lt_of_le_of_lt step.chainStep.fork_le early
  have rEarly : r.fork < .glamsterdam :=
    Nat.lt_of_le_of_lt (fork_le_of_chainSteps pre.chainSteps) mEarly
  have mAltair : .altair ≤ m.fork := Nat.le_trans altairR (fork_le_of_chainSteps pre.chainSteps)
  have mEpoch : getCurrentEpoch m.state = getCurrentEpoch r.state :=
    UInt64.le_antisymm (same ▸ step.chainStep.currentEpoch_le)
      (currentEpoch_le_of_chainSteps pre.chainSteps)
  have oneEffective := step_same_epoch_effective step early (same.trans mEpoch.symm)
  have effectiveEnd : ∀ i, i < r.state.validators.data.size →
      effectiveAt l i = effectiveAt r i := fun i inside =>
    (oneEffective i (Nat.lt_of_lt_of_le inside
      (registryGrows_of_chainSteps pre.chainSteps))).trans (prefixEffective i inside)
  cases step with
  | slot ok =>
    obtain ⟨advanced, advanceOk, upgrades⟩ := bind_ok_iff.mp ok
    have advanceCopy := advanceOk
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at advanceCopy
    obtain ⟨next, nextOk, cached, cachedOk, epoched, epochOk, advancedEq⟩ := advanceCopy
    have sum := (Uint64.addChecked_ok_iff.mp
      (mapError_ok_iff.mp (liftAccessor_ok.mp nextOk))).2
    simp only [UInt64.toNat_one] at sum
    have lSlot : l.state.slot = next := by rw [processUpgrades_slot upgrades, ← advancedEq]
    -- The slot stays inside the epoch, so it runs no epoch transition and no upgrade.
    have notLast : ¬ next % preset.SLOTS_PER_EPOCH = 0 := by
      intro last
      have epochs := nextSlot_epoch_of_boundary sum last
      have equal := congrArg UInt64.toNat (same.trans mEpoch.symm)
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, lSlot] at equal
      omega
    simp only [epochIfLast, notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochOk
    subst epochOk
    have due : upgradeDue config ⟨m.fork, advanced⟩ = false := by
      apply upgradeDue_of_not_first
      rw [← advancedEq]
      exact notLast
    have kept := (Except.ok.inj ((processUpgrades_of_not_due due).symm.trans upgrades)).symm
    have none : added = [] := by
      have crossings : upgradeBalanceReplay (config := config) (checks := checks)
          ⟨m.fork, advanced⟩ = .ok [] := by
        unfold upgradeBalanceReplay
        simp [due, pure, Except.pure]
      simp only [Step.balanceEvents, cachedOk, nextOk, notLast, ↓reduceIte, advanceOk,
        crossings, bind, Except.bind, pure, Except.pure, List.append_nil,
        Except.ok.injEq] at addedOk
      exact addedOk.symm
    subst kept none
    obtain ⟨root, _, header⟩ := advanceSlot_latestBlockHeader advanceOk
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    refine ⟨effectiveEnd, ?_⟩
    refine ⟨.inr ⟨by simp [sourceCredits], by simp [sourceCredits],
      by simp [sourceDebits], by simp [PenaltyFree]⟩, ?_⟩
    intro total perIncrement totalOk per previous current base previousEq currentEq baseEq
    refine ⟨Nat.le_of_eq ?_, by simp [sourceDebits, sourceCredits],
      .inl ⟨by simp [sourceCredits], by rw [← advancedEq]; exact sum,
      by rw [header]; split <;> rfl⟩, by simp [PenaltyFree]⟩
    simp only [sourceCredits, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.add_zero]
    rw [← advancedEq]
    rfl
  | @block f before after engine signed due ok =>
    have altair : .altair ≤ f := mAltair
    have processed := (applySignedBlock_ok ok).2.1
    have replay := Step.balanceEvents_block mEarly addedOk
    obtain ⟨read, readPer, readOk, readComputed, credits⟩ :=
      block_credits_generic mEarly altair replay
    have whole := pre.snoc (.block engine signed due ok)
    refine ⟨effectiveEnd, ?_⟩
    have rootRead : getTotalActiveBalance r.state = .ok read :=
      (total_active_congr rEarly mEarly
        ((activeKept_of_chainSteps whole.chainSteps).mono
          (getCurrentEpoch_le_activityFixedEpoch _)) same
        effectiveEnd).symm.trans readOk
    refine ⟨.inl ⟨read, readPer, rootRead, readComputed⟩, ?_⟩
    intro total perIncrement totalOk per previous current base previousEq currentEq baseEq
    have equal : read = total := Except.ok.inj (rootRead.symm.trans totalOk)
    subst read
    have within := r.state.validators.bound rEarly
    -- The block starts with the effective balances, the activity and the total of `r`.
    have effective := prefixEffective
    have activeR := activeKept_of_chainSteps pre.chainSteps
    have sizeR := registryGrows_of_chainSteps pre.chainSteps
    have totalBefore : getTotalActiveBalance before = .ok total :=
      (total_active_congr rEarly mEarly
        (activeR.mono (getCurrentEpoch_le_activityFixedEpoch _)) mEpoch effective).trans totalOk
    have afterSlot := (frame_processBlock processed).slot
    have insideR : ∀ i ∈ previous ∪ current, i.toNat < r.state.validators.data.size := by
      intro i member
      rw [previousEq, currentEq] at member
      rcases Finset.mem_union.mp member with chosen | chosen <;>
      · obtain ⟨_, found, _⟩ := (mem_getActiveValidatorIndices within).mp
          (List.mem_toFinset.mp chosen)
        exact (Array.getElem?_eq_some_iff.mp found).1
    -- An attestation of the block reads the same activity, balances and total as `r`.
    have attest {u u' : BeaconState preset f} {att : Attestation preset f} {credit : Nat}
        (siteEffective : EffectiveKept before u) (siteActive : ActiveStep before u)
        (attested : processAttestation config checks u before.latestBlockHeader.slot att =
          .ok u')
        (credited : attestationCredit u att before.latestBlockHeader.slot = .ok credit) :
        flagPotential previous current base ⟨f, u⟩ + 448 * credit ≤
          flagPotential previous current base ⟨f, u'⟩ := by
      have uEpoch : getCurrentEpoch u = getCurrentEpoch r.state := by
        rw [← mEpoch]
        simp only [getCurrentEpoch, siteActive.1]
      have reads (epoch : Epoch) (low : epoch ≤ getCurrentEpoch r.state) :
          getActiveValidatorIndices u epoch = getActiveValidatorIndices r.state epoch := by
        rw [siteActive.2.getActiveValidatorIndices_eq (UInt64.le_trans low
            (mEpoch ▸ getCurrentEpoch_le_activityFixedEpoch before)),
          activeR.getActiveValidatorIndices_eq
            (UInt64.le_trans low (getCurrentEpoch_le_activityFixedEpoch _))]
      have previousSame : getPreviousEpoch u = getPreviousEpoch r.state := by
        simp only [getPreviousEpoch, uEpoch]
      have siteTotal : getTotalActiveBalance u = .ok total :=
        (total_active_congr mEarly mEarly
          (siteActive.2.mono (getCurrentEpoch_le_activityFixedEpoch _))
          (by simp only [getCurrentEpoch, siteActive.1]) siteEffective).trans totalBefore
      refine attestation_flagPotential mEarly altair attested credited
        (fun i member => by
          rw [previousSame, reads _ (getPreviousEpoch_le _)] at member
          exact previousEq ▸ List.mem_toFinset.mpr member)
        (fun i member => by
          rw [uEpoch, reads _ (UInt64.le_refl _)] at member
          exact currentEq ▸ List.mem_toFinset.mpr member)
        (fun total' i reward member totalU rewardOk => ?_)
      obtain rfl := Except.ok.inj (totalU.symm.trans siteTotal)
      obtain ⟨v, found, value⟩ := getBaseReward_eq_mul_of_altair altair per rewardOk
      have small := insideR i (Finset.mem_union.mpr member)
      have read : v.effectiveBalance.toNat = effectiveAt r i.toNat := by
        rw [← effective i.toNat small, ← siteEffective i.toNat (Nat.lt_of_lt_of_le small sizeR)]
        simp [effectiveAt, found]
      rw [value, read, baseEq]
    obtain ⟨potential, sync, mute, positive, free⟩ := credits previous current base
      (fun i member => Nat.lt_of_lt_of_le (insideR i member) sizeR) attest
    obtain ⟨atSlot, newer, -⟩ := processBlock_parentRoot processed
    obtain ⟨_, -, header⟩ := latestBlockHeader_processBlock processed
    exact ⟨potential, mute, .inr ⟨sync, positive, afterSlot,
      atSlot ▸ UInt64.lt_iff_toNat_lt.mp newer,
      by rw [header, afterSlot, atSlot]⟩, free⟩

/-- The flag potential is at most `54` times the base rewards of the two sets of keys. -/
private theorem flagPotential_le (previous current : Finset ValidatorIndex)
    (base : ValidatorIndex → Nat) (u : ForkedBeaconState preset) :
    flagPotential previous current base u ≤
      54 * (∑ i ∈ previous, base i + ∑ i ∈ current, base i) := by
  simp only [flagPotential]
  split
  · rw [Nat.mul_add, Finset.mul_sum, Finset.mul_sum]
    exact Nat.add_le_add
      (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (entryWeight_le _))
      (Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (entryWeight_le _))
  · exact Nat.zero_le _

/-- The proposer and sync credits of the blocks of a run inside one epoch, from Electra.

The proposer credits, times `448`, are at most `54` base rewards per increment for each increment.

The increments are those of the effective stakes at the start `r` of two sets of keys.

The sets are the keys active at the previous epoch of `r`, and those active at its current epoch.

The sync credits, times `28`, are at most the issuance envelope of the total active balance of `r`.

So are the sync debit limits, since each block's debit limit is at most its credit limit.

No event of the run is a penalty or an inactivity event.

A slot holds at most one block, so the epoch has at most `SLOTS_PER_EPOCH` of them. -/
private theorem epoch_credits_generic {r s : ForkedBeaconState preset}
    (inner : Run config checks r s)
    (altairR : .altair ≤ r.fork) (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (high : Nat) {events : List (BalanceEvent preset)}
    (replayed : inner.balanceEvents high = .ok events) :
    (∀ i, i < r.state.validators.data.size → effectiveAt s i = effectiveAt r i) ∧
    ((∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
      (sourceCredits .rewards events = 0 ∧ sourceCredits .sync events = 0 ∧
        sourceDebits .sync events = 0 ∧ PenaltyFree events)) ∧
    ∀ (total perIncrement : Gwei) (_totalOk : getTotalActiveBalance r.state = .ok total)
      (_per : getBaseRewardPerIncrement preset total = .ok perIncrement),
    sourceCredits .rewards events * 448 ≤ 54 * perIncrement.toNat *
      ((∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
      sourceCredits .sync events * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat ∧
      sourceDebits .sync events * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat ∧
      PenaltyFree events := by
  set previous := (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset
  set current := (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset
  let base (perIncrement : Gwei) (i : ValidatorIndex) : Nat :=
    effectiveAt r i.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat * perIncrement.toNat
  -- The potential rises by the proposer credits, and the blocks are at most one per slot.
  have key : ∀ {u : ForkedBeaconState preset} (tail : Run config checks r u),
      u.fork < .glamsterdam → getCurrentEpoch u.state = getCurrentEpoch r.state →
      ∀ found, tail.balanceEvents high = .ok found →
      (∀ i, i < r.state.validators.data.size → effectiveAt u i = effectiveAt r i) ∧
      ((∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
        getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
        (sourceCredits .rewards found = 0 ∧ sourceCredits .sync found = 0 ∧
          sourceDebits .sync found = 0 ∧ PenaltyFree found)) ∧
      ∀ (total perIncrement : Gwei) (_totalOk : getTotalActiveBalance r.state = .ok total)
        (_per : getBaseRewardPerIncrement preset total = .ok perIncrement),
      flagPotential previous current (base perIncrement) r + 448 * sourceCredits .rewards found ≤
          flagPotential previous current (base perIncrement) u ∧
        sourceDebits .sync found ≤ sourceCredits .sync found ∧
        (∃ count, sourceCredits .sync found * (28 * preset.SLOTS_PER_EPOCH.toNat) ≤
            count * preset.epochIssuanceBeforeAltair total.toNat ∧
          count + r.state.slot.toNat ≤ u.state.slot.toNat + 1 ∧
          (count + r.state.slot.toNat = u.state.slot.toNat + 1 →
            u.state.latestBlockHeader.slot.toNat = u.state.slot.toNat) ∧
          (sourceCredits .sync found = 0 ∨ 0 < preset.SLOTS_PER_EPOCH.toNat)) ∧
        PenaltyFree found := by
    intro u tail
    induction tail with
    | nil =>
      intro _ _ found ok
      cases ok
      refine ⟨fun _ _ => rfl, ?_⟩
      refine ⟨.inr ⟨by simp [sourceCredits], by simp [sourceCredits],
        by simp [sourceDebits], by simp [PenaltyFree]⟩, ?_⟩
      intro total perIncrement totalOk per
      exact ⟨by simp [sourceCredits], by simp [sourceDebits], ⟨0, by simp [sourceCredits],
        by omega, by omega, .inl (by simp [sourceCredits])⟩, by simp [PenaltyFree]⟩
    | @snoc m l pre step ih =>
      intro lEarly lEpoch found ok
      have mEarly := Nat.lt_of_le_of_lt step.chainStep.fork_le lEarly
      have mEpoch : getCurrentEpoch m.state = getCurrentEpoch r.state :=
        UInt64.le_antisymm (lEpoch ▸ step.chainStep.currentEpoch_le)
          (currentEpoch_le_of_chainSteps pre.chainSteps)
      simp only [Run.balanceEvents, bind_ok_iff] at ok
      obtain ⟨prior, priorOk, rest⟩ := ok
      obtain ⟨prefixEffective, priorReads, priorBound⟩ :=
        ih mEarly mEpoch prior priorOk
      obtain ⟨added, addedOk⟩ := step.balanceEvents_ok lEarly
      obtain ⟨endEffective, addedReads, addedBound⟩ :=
        step_credits_generic pre step altairR lEarly lEpoch prefixEffective addedOk
      -- The step's events count only if it starts by `high + 1`.
      have events : ∃ taken, found = prior ++ taken ∧
          (taken = [] ∨ taken = added) := by
        split at rest
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, addedOk] at rest
          obtain ⟨_, rfl, rfl⟩ := rest
          exact ⟨added, rfl, .inr rfl⟩
        · cases rest
          exact ⟨[], (List.append_nil _).symm, .inl rfl⟩
      obtain ⟨taken, rfl, choice⟩ := events
      have reads : (∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
          getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
          (sourceCredits .rewards (prior ++ taken) = 0 ∧
            sourceCredits .sync (prior ++ taken) = 0 ∧
            sourceDebits .sync (prior ++ taken) = 0 ∧ PenaltyFree (prior ++ taken)) := by
        rcases priorReads with one | zero
        · exact .inl one
        rcases addedReads with one | quiet
        · exact .inl one
        right
        rcases choice with rfl | rfl
        · simpa only [List.append_nil] using zero
        · exact ⟨by rw [sourceCredits_append, zero.1, quiet.1],
            by rw [sourceCredits_append, zero.2.1, quiet.2.1],
            by rw [sourceDebits_append, zero.2.2.1, quiet.2.2.1],
            zero.2.2.2.append quiet.2.2.2⟩
      refine ⟨endEffective, reads, ?_⟩
      intro total perIncrement totalOk per
      obtain ⟨potential, debits, ⟨count, sync, counted, full, positive⟩, priorFree⟩ :=
        priorBound total perIncrement totalOk per
      obtain ⟨raised, mute, kind, addedFree⟩ := addedBound total perIncrement totalOk per
        previous current (base perIncrement) rfl rfl (fun _ => rfl)
      have bounded : sourceCredits .rewards taken ≤ sourceCredits .rewards added ∧
          sourceCredits .sync taken ≤ sourceCredits .sync added := by
        rcases choice with rfl | rfl
        · simp [sourceCredits]
        · exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      have takenMute : sourceDebits .sync taken ≤ sourceCredits .sync taken := by
        rcases choice with rfl | rfl
        · simp [sourceDebits]
        · exact mute
      have takenFree : PenaltyFree taken := by
        rcases choice with rfl | rfl
        · simp [PenaltyFree]
        · exact addedFree
      simp only [sourceCredits_append, sourceDebits_append]
      refine ⟨by omega, by omega, ?_, priorFree.append takenFree⟩
      rcases kind with ⟨silent, slot, header⟩ | ⟨blockSync, slotsPositive, slot, newer, header⟩
      · have none : sourceCredits .sync taken = 0 := by omega
        refine ⟨count, by rw [none, Nat.add_zero]; exact sync, by omega, by omega, ?_⟩
        rcases positive with zero | holds
        · exact .inl (by omega)
        · exact .inr holds
      · refine ⟨count + 1, ?_, ?_, ?_, .inr slotsPositive⟩
        · rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add sync ((Nat.mul_le_mul_right _ bounded.2).trans blockSync)
        · have : count + r.state.slot.toNat ≠ m.state.slot.toNat + 1 := fun equal => by
            have := full equal
            omega
          rw [slot]
          omega
        · intro _
          rw [header]
  obtain ⟨effective, reads, bounds⟩ :=
    key inner early same events replayed
  refine ⟨effective, reads, ?_⟩
  intro total perIncrement totalOk per
  obtain ⟨potential, debits, ⟨count, sync, counted, _, positive⟩, free⟩ :=
    bounds total perIncrement totalOk per
  have syncBound : sourceCredits .sync events * 28 ≤
      preset.epochIssuanceBeforeAltair total.toNat := by
    -- The blocks of the epoch are at most one per slot.
    rcases positive with zero | slotsPositive
    · rw [zero]
      exact Nat.zero_le _
    have epochs := congrArg UInt64.toNat same
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at epochs
    generalize preset.SLOTS_PER_EPOCH.toNat = slots at *
    have sDiv := Nat.div_add_mod s.state.slot.toNat slots
    have rDiv := Nat.div_add_mod r.state.slot.toNat slots
    have sMod := Nat.mod_lt s.state.slot.toNat slotsPositive
    rw [epochs] at sDiv
    have fewer : count ≤ slots := by omega
    have scaled : sourceCredits .sync events * 28 * slots ≤
        preset.epochIssuanceBeforeAltair total.toNat * slots := by
      calc sourceCredits .sync events * 28 * slots =
            sourceCredits .sync events * (28 * slots) := by ring
        _ ≤ count * preset.epochIssuanceBeforeAltair total.toNat := sync
        _ ≤ slots * preset.epochIssuanceBeforeAltair total.toNat := Nat.mul_le_mul_right _ fewer
        _ = preset.epochIssuanceBeforeAltair total.toNat * slots := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right scaled slotsPositive
  refine ⟨?_, syncBound, (Nat.mul_le_mul_right 28 debits).trans syncBound, free⟩
  -- The potential at `s` is at most `54` base rewards for each key.
  have most := flagPotential_le previous current (base perIncrement) s
  have stakes (keys : Finset ValidatorIndex) : ∑ i ∈ keys, base perIncrement i ≤
      perIncrement.toNat *
        ((∑ i ∈ keys, effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) := by
    rw [← Finset.sum_mul, Nat.mul_comm]
    exact Nat.mul_le_mul_left _ (sum_div_le _ _ _)
  have one := stakes previous
  have two := stakes current
  have joined := Nat.mul_le_mul_left 54 (Nat.add_le_add one two)
  rw [← Nat.mul_add] at joined
  rw [Nat.mul_assoc]
  omega

/-- The existing Electra credit interface projects the generic epoch certificate. -/
theorem epoch_credits_data {r s : ForkedBeaconState preset} (inner : Run config checks r s)
    (electra : .pectra ≤ r.fork) (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (high : Nat) {events : List (BalanceEvent preset)}
    (replayed : inner.balanceEvents high = .ok events) :
    ((∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement) ∨
      (sourceCredits .rewards events = 0 ∧ sourceCredits .sync events = 0 ∧
        sourceDebits .sync events = 0 ∧ PenaltyFree events)) ∧
    ∀ (total perIncrement : Gwei) (_totalOk : getTotalActiveBalance r.state = .ok total)
      (_per : getBaseRewardPerIncrement preset total = .ok perIncrement),
    sourceCredits .rewards events * 448 ≤ 54 * perIncrement.toNat *
      ((∑ i ∈ (getActiveValidatorIndices r.state (getPreviousEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat +
        (∑ i ∈ (getActiveValidatorIndices r.state (getCurrentEpoch r.state)).toFinset,
          effectiveAt r i.toNat) / preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∧
      sourceCredits .sync events * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat ∧
      sourceDebits .sync events * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat ∧
      PenaltyFree events :=
  (epoch_credits_generic inner (Nat.le_trans (by decide) electra) early same high replayed).2

/-- The generic epoch certificate supplies sync bounds without a supplied per-increment read. -/
theorem epoch_sync_data {r s : ForkedBeaconState preset} (inner : Run config checks r s)
    (altair : .altair ≤ r.fork) (early : s.fork < .glamsterdam)
    (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (high : Nat) {events : List (BalanceEvent preset)}
    (replayed : inner.balanceEvents high = .ok events) :
    (∀ i, i < r.state.validators.data.size → effectiveAt s i = effectiveAt r i) ∧
    PenaltyFree events ∧
    ((∃ total perIncrement, getTotalActiveBalance r.state = .ok total ∧
      getBaseRewardPerIncrement preset total = .ok perIncrement) ∨ sourceDebits .sync events = 0) ∧
    ∀ total, getTotalActiveBalance r.state = .ok total →
      sourceDebits .sync events * 28 ≤ preset.epochIssuanceBeforeAltair total.toNat := by
  obtain ⟨effective, cases, bounds⟩ := epoch_credits_generic inner altair early same high replayed
  refine ⟨effective, ?_⟩
  rcases cases with ⟨actual, perIncrement, actualOk, per⟩ | quiet
  · have certificate := bounds actual perIncrement actualOk per
    refine ⟨certificate.2.2.2, .inl ⟨actual, perIncrement, actualOk, per⟩, ?_⟩
    intro total totalOk
    obtain rfl := Except.ok.inj (actualOk.symm.trans totalOk)
    exact certificate.2.2.1
  · exact ⟨quiet.2.2.2, .inr quiet.2.2.1, fun _ _ => by
      rw [quiet.2.2.1, Nat.zero_mul]; exact Nat.zero_le _⟩

/-- Successful total reads transport backwards through the generic same-epoch certificate. -/
theorem epoch_total_transport {r s : ForkedBeaconState preset}
    (inner : Run config checks r s) (altair : .altair ≤ r.fork)
    (early : s.fork < .glamsterdam) (same : getCurrentEpoch s.state = getCurrentEpoch r.state)
    (high : Nat) {events : List (BalanceEvent preset)}
    (replayed : inner.balanceEvents high = .ok events) {total : Gwei}
    (computed : getTotalActiveBalance s.state = .ok total) :
    getTotalActiveBalance r.state = .ok total := by
  have effective := (epoch_credits_generic inner altair early same high replayed).1
  have rEarly := Nat.lt_of_le_of_lt (fork_le_of_chainSteps inner.chainSteps) early
  exact (total_active_congr rEarly early
    ((activeKept_of_chainSteps inner.chainSteps).mono
      (getCurrentEpoch_le_activityFixedEpoch _)) same effective).symm.trans computed

end

end EthLib.Consensus.DirectSafety.Apriori.Internal
