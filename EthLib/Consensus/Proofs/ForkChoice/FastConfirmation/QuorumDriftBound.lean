module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.QuorumReserve
public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.HistoricalStatements
public import EthLib.Consensus.Proofs.Transition.BranchLedger
public import EthLib.Consensus.Proofs.Transition.EffectiveFall
public import EthLib.Consensus.Proofs.Transition.EffectiveRise
public import EthLib.Consensus.Proofs.Mutators
import EthLib.Consensus.Proofs.Transition.ActiveKept
import EthLib.Consensus.Proofs.Transition.ChainRoots
import EthLib.Consensus.Proofs.Transition.Genesis
import EthLib.Consensus.Proofs.Transition.RegistryLifecycle

/-!
# The quorum of a fast-confirmation call drifts by at most its reserve

A call of the fast confirmation rule counts honest stake in its pulled-up head state.

A later state that counts the same voters is in the call's epoch or the next one.

Within the epoch nothing drifts: the active set and its effective balances stay.

Across one epoch transition the total rises by at most the reserve's gain.

Across it the voters' stake falls by at most the reserve's loss.

Inside the epoch, the balances at the call differ from those at its start by bounded corrections.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Network

open Base Uint64 Models

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}


/-- A sum over some voters of a function of their positions is at most its sum over positions.

Each voter's position must be one of those positions. -/
private theorem voters_sum_le {voters : Finset ValidatorIndex} {positions : Finset ℕ}
    (f : ℕ → ℕ) (inside : ∀ v ∈ voters, v.toNat ∈ positions) :
    ∑ v ∈ voters, f v.toNat ≤ ∑ i ∈ positions, f i := by
  rw [← Finset.sum_image (g := UInt64.toNat) fun a _ b _ same => UInt64.toNat_inj.mp same]
  exact Finset.sum_le_sum_of_subset fun i member => by
    obtain ⟨v, voter, rfl⟩ := Finset.mem_image.mp member
    exact inside v voter

/-- The validators active in the next epoch weigh at most those active now and those joining. -/
private theorem sum_upcoming_le (s : Finset ℕ) (current upcoming : ℕ → Bool) (f : ℕ → ℕ) :
    ∑ i ∈ s with upcoming i = true, f i ≤
      ∑ i ∈ s with current i = true, f i +
        ∑ i ∈ s with current i = false ∧ upcoming i = true, f i := by
  rw [← Finset.sum_filter_add_sum_filter_not (s.filter fun i => upcoming i = true)
    (fun i => current i = true)]
  refine Nat.add_le_add (Finset.sum_le_sum_of_subset fun i member => ?_) (le_of_eq ?_)
  · simp only [Finset.mem_filter] at member ⊢
    exact ⟨member.1.1, member.2⟩
  · rw [Finset.filter_filter]
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ?_) fun _ _ => rfl
    cases current i <;> simp [and_comm]

/-- A count of the blocks of a branch, kept or replaced by a larger count, bounds the credited. -/
private theorem credited_mono {c : Prop} [Decidable c] {m n a b : ℕ} (counts : m ≤ n)
    (deposits : a ≤ b) : (if c then 0 else m) + a ≤ (if c then 0 else n) + b := by
  split <;> omega

/-- The deposits read before Electra grow with the count of the blocks. -/
private theorem blockDeposits_mono {c d : Prop} [Decidable c] [Decidable d] {k m n : ℕ}
    {index : c → ℕ} (counts : m ≤ n) :
    (if h : c then (if d then 0 else min (k * m) (index h)) else 0) ≤
      (if h : c then (if d then 0 else min (k * n) (index h)) else 0) := by
  split
  · split
    · exact Nat.le_refl _
    · exact min_le_min (Nat.mul_le_mul_left _ counts) (Nat.le_refl _)
  · exact Nat.le_refl _

/-- The quorum of a call drifts by at most the reserve from the call's state to a later state.

An assumption on the run: its fork is Fulu or later, and before Gloas.

The bounds read the epoch transition of Fulu; earlier and later forks are not covered.

The call's state is in the epoch of a boundary state, which is right after its epoch transition.

The bands of hysteresis hold at the boundary state, and genesis reaches it.

A middle state follows the boundary state by at most one block.

It holds the queue of partial withdrawals of the ancestor that the reserve reads.

The call's state and the later state both follow the middle state.

The blocks from the boundary state to the call's state number at most one per slot.

The later state is in the call's epoch or the next one.

Take voters that are active at the call's state and not slashed at the later state.

Twice the later total and three times their stake at the call add up to at most a bound.

That bound is twice the total at the call, three times their later stake, and the reserve.

The seed lookahead covers at least one epoch, so activity in the next epoch is fixed in the current.
-/
theorem quorumDrift_le_quorumReserve
    {g : ForkedBeaconState preset}
    {boundary middle pulled anc state : BeaconState preset fork}
    (genesis : Genesis config checks g) (history : Run config checks g ⟨fork, boundary⟩)
    (edge : Run config checks ⟨fork, boundary⟩ ⟨fork, middle⟩)
    (tailP : Run config checks ⟨fork, middle⟩ ⟨fork, pulled⟩)
    (tailS : Run config checks ⟨fork, middle⟩ ⟨fork, state⟩)
    (early : fork < .glamsterdam) (fulu : .fusaka ≤ fork)
    (bands : preset.IncrementWithinUpwardBand)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (caps : CapOrder preset) (maxLookahead : 1 ≤ preset.MAX_SEED_LOOKAHEAD.toNat)
    (hysteresis : Hysteresis boundary) (single : edge.blockCount ≤ 1)
    (counted : edge.blockCount + tailP.blockCount ≤
      pulled.slot.toNat - (getCurrentEpoch pulled).toNat * preset.SLOTS_PER_EPOCH.toNat + 1)
    (queue : ∀ electra : .pectra ≤ fork,
      middle.pendingPartialWithdrawals electra = anc.pendingPartialWithdrawals electra)
    (middleEpoch : getCurrentEpoch middle = getCurrentEpoch boundary)
    (callEpoch : getCurrentEpoch pulled = getCurrentEpoch boundary)
    (later : getCurrentEpoch pulled ≤ getCurrentEpoch state)
    (near : (getCurrentEpoch state).toNat ≤ (getCurrentEpoch pulled).toNat + 1)
    {voters : Finset ValidatorIndex} {total pulledTotal : Gwei}
    (voting : ∀ v ∈ voters,
      v ∈ activeVoters pulled ∧ (slashedFlagAt state v.toNat).getD false = false)
    (totalOk : getTotalActiveBalance state = .ok total)
    (pulledOk : getTotalActiveBalance pulled = .ok pulledTotal) :
    2 * total.toNat + 3 * stake (fun v => balanceAt pulled v.toNat) voters ≤
      2 * pulledTotal.toNat + 3 * stake (fun v => balanceAt state v.toNat) voters +
        quorumReserve config pulled anc := by
  have notGloas : ¬Fork.glamsterdam ≤ fork := fun late =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le early late)
  -- The reserve reads the queue of the ancestor, which the middle state holds.
  have sameQueue : quorumReserve config pulled anc = quorumReserve config pulled middle := by
    unfold quorumReserve
    simp only [queue]
  rw [sameQueue]
  -- Each voter is active in the epoch of the call.
  have voterActive : ∀ v ∈ voters, isActiveAt pulled (getCurrentEpoch pulled) v.toNat = true := by
    intro v voter
    obtain ⟨validator, found, active⟩ :=
      (mem_getActiveValidatorIndices (pulled.validators.bound early)).mp
        (List.mem_toFinset.mp (voting v voter).1)
    exact isActiveAt_eq_true_iff.mpr ⟨validator, found, active⟩
  have fixed : getCurrentEpoch boundary ≤ activityFixedEpoch boundary :=
    getCurrentEpoch_le_activityFixedEpoch boundary
  have activeP : ∀ i, isActiveAt pulled (getCurrentEpoch boundary) i =
      isActiveAt boundary (getCurrentEpoch boundary) i :=
    activeKept_of_chainSteps (edge.append tailP).chainSteps _ fixed
  have keptP : EffectiveKept boundary pulled :=
    (edge.append tailP).effectiveKept_of_same_epoch early callEpoch
  have insideR {i : ℕ} (active : isActiveAt boundary (getCurrentEpoch boundary) i = true) :
      i < boundary.validators.data.size := by
    obtain ⟨_, found, -⟩ := isActiveAt_eq_true_iff.mp active
    exact (Array.getElem?_eq_some_iff.mp found).1
  rcases Nat.lt_or_ge (getCurrentEpoch pulled).toNat (getCurrentEpoch state).toNat with
    advanced | stayed
  rotate_left
  · -- The state is in the epoch of the call: the active set and its effective balances stay.
    have sameEpoch : getCurrentEpoch state = getCurrentEpoch boundary :=
      (UInt64.le_antisymm (UInt64.le_iff_toNat_le.mpr stayed) later).trans callEpoch
    have activeS : ∀ i, isActiveAt state (getCurrentEpoch boundary) i =
        isActiveAt boundary (getCurrentEpoch boundary) i :=
      activeKept_of_chainSteps (edge.append tailS).chainSteps _ fixed
    have keptS : EffectiveKept boundary state :=
      (edge.append tailS).effectiveKept_of_same_epoch early sameEpoch
    have totals : total.toNat = pulledTotal.toNat := by
      rw [getTotalActiveBalance_toNat totalOk, getTotalActiveBalance_toNat pulledOk,
        activeBalanceTotal, activeBalanceTotal, sameEpoch, callEpoch]
      -- Both totals sum the effective balances that the boundary state holds.
      congr 1
      exact (activeSum_eq activeS keptS (edge.append tailS).registryLifecycle.size_le).trans
        (activeSum_eq activeP keptP (edge.append tailP).registryLifecycle.size_le).symm
    have stakes : stake (fun v => balanceAt state v.toNat) voters =
        stake (fun v => balanceAt pulled v.toNat) voters := by
      refine Finset.sum_congr rfl fun v voter => ?_
      have active := voterActive v voter
      rw [callEpoch, activeP] at active
      exact (keptS _ (insideR active)).trans (keptP _ (insideR active)).symm
    omega
  -- The state is in the next epoch.
  have next : (getCurrentEpoch state).toNat = (getCurrentEpoch boundary).toNat + 1 := by
    rw [← callEpoch]; omega
  -- The invariant of the transition holds from genesis along the history.
  have invG : Invariant g.state := genesis.invariant
  have invR := Run.invariant invG history
  have invM := Run.invariant invG (history.append edge)
  -- The branch corrections from the boundary state, and from the middle state.
  obtain ⟨debitedKeys, -, -, -, debitedCard, -, gainSide, -, -, -, -, -, -, -, capsKept, -, -⟩ :=
    (edge.append tailP).balanceCorrections_of_same_epoch early fulu callEpoch invR.balancesMatch
      invR.exitsOrdered
  obtain ⟨-, creditedKeys, pc, deposit, -, creditedCard, -, lossSide, zeroOff, electraZero, budget,
    -, -, -, -, -, -⟩ := tailP.balanceCorrections_of_same_epoch early fulu
      (callEpoch.trans middleEpoch.symm) invM.balancesMatch invM.exitsOrdered
  have blocksLe : (edge.append tailP).blockCount ≤
      pulled.slot.toNat - (getCurrentEpoch pulled).toNat * preset.SLOTS_PER_EPOCH.toNat + 1 := by
    rw [Run.blockCount_append]; exact counted
  -- The reserve, term by term.
  unfold quorumReserve
  extract_lets epoch inc slots p positions validator effective actual cap capMax current upcoming
    before recent slashed totalGwei' total' base num den flagWeight seatReward seats sync
    depositChurn score delay inactivity credit penalty syncProposer proposerCredit
    whistleblower depositCredit due dueStake proposers depositRecipients recipients nP debited
    transfers depositGain slashBack syncP blockDeposits creditedP creditMax joining crossing
    headroom gain partials fall syncPMax whistleblowerP maskBudget loss
  have gainEq : gain = joining + min headroom (crossing + (recipients + debited) *
      preset.upwardBand + debited * creditMax + transfers + depositGain) := rfl
  have lossEq : loss = ∑ i ∈ positions with current i = true, fall i +
      creditedP * (inc + 2 * preset.downwardBand + syncPMax) + maskBudget := rfl
  have nPLe : edge.blockCount + tailP.blockCount ≤ nP := counted
  -- The rise of the total: the active set of the next epoch is fixed at the boundary state.
  have nextEpoch : getCurrentEpoch state = epoch + 1 := by
    apply UInt64.toNat_inj.mp
    have small := (getCurrentEpoch state).toNat_lt
    rw [UInt64.toNat_add, UInt64.toNat_one, show epoch = getCurrentEpoch pulled from rfl]
    omega
  have fixedNext : epoch + 1 ≤ activityFixedEpoch boundary := by
    have small := (getCurrentEpoch state).toNat_lt
    rw [← nextEpoch, UInt64.le_iff_toNat_le, activityFixedEpoch_toNat]
    omega
  have nextS : ∀ i, isActiveAt state (epoch + 1) i = isActiveAt boundary (epoch + 1) i :=
    activeKept_of_chainSteps (edge.append tailS).chainSteps _ fixedNext
  have nextP : ∀ i, isActiveAt pulled (epoch + 1) i = isActiveAt boundary (epoch + 1) i :=
    activeKept_of_chainSteps (edge.append tailP).chainSteps _ fixedNext
  have totalS : total.toNat = max inc
      (∑ i ∈ positions with upcoming i = true, effectiveAt ⟨fork, state⟩ i) := by
    rw [getTotalActiveBalance_toNat totalOk, activeBalanceTotal, nextEpoch]
    -- Both states take their active set in the next epoch from the boundary state.
    rw [activeFilter_eq nextS (edge.append tailS).registryLifecycle.size_le,
      activeFilter_eq nextP (edge.append tailP).registryLifecycle.size_le]
    rfl
  have totalP : pulledTotal.toNat = total' := by
    simp only [total', totalGwei', pulledOk, Except.toOption, Option.getD_some]
  have rise : ∑ i ∈ positions with upcoming i = true, (effectiveAt ⟨fork, state⟩ i - effective i) ≤
      min headroom (crossing + (recipients + debited) * preset.upwardBand + debited * creditMax +
        transfers + depositGain) :=
    effectiveRise_le genesis history (edge.append tailP) (edge.append tailS) caps withdrawDelay
      bands maxLookahead hysteresis early fulu callEpoch next
      (n := nP) debitedKeys
      (debitedCard.trans (Nat.mul_le_mul_left _ blocksLe))
      (fun v off => (gainSide v off).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ blocksLe) _))
      capsKept
  have split : ∑ i ∈ positions with upcoming i = true, effectiveAt ⟨fork, state⟩ i ≤
      ∑ i ∈ positions with upcoming i = true, effective i +
        ∑ i ∈ positions with upcoming i = true, (effectiveAt ⟨fork, state⟩ i - effective i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by omega
  have joined := sum_upcoming_le positions current upcoming effective
  have totalEq : total' = max inc (∑ i ∈ positions with current i = true, effective i) := by
    rw [← totalP, getTotalActiveBalance_toNat pulledOk, activeBalanceTotal]
    rfl
  have riseBound : total.toNat ≤ pulledTotal.toNat + gain := by
    rw [totalS, totalP, totalEq, gainEq]
    omega
  -- The fall of the voters.
  obtain ⟨below, owed, belowOff, belowSum, falls⟩ : ∃ (below : ValidatorIndex → ℕ)
      (owed : Finset ValidatorIndex), (∀ v, v ∉ owed → below v = 0) ∧
      ∑ v ∈ owed, below v ≤ (if Fork.pectra ≤ fork then
        preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat *
          (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat - preset.MIN_ACTIVATION_BALANCE.toNat)
        else 0) ∧
      ∀ v : ValidatorIndex, current v.toNat = true →
        ((state.validators.data[v.toNat]?).map (·.slashed)).getD false = false →
        effective v.toNat - effectiveAt ⟨fork, state⟩ v.toNat ≤ fall v.toNat +
          (if pc v + deposit v = 0 then 0
           else inc + 2 * preset.downwardBand + syncP v.toNat +
             min (pc v + deposit v) (below v)) :=
    effectiveFall_le genesis history edge tailP tailS caps bands withdrawDelay hysteresis early
      fulu
      middleEpoch callEpoch next single counted (fun v => pc v + deposit v)
      (fun v => (lossSide v).trans (by rw [Nat.add_assoc]; exact Nat.le_refl _))
  -- Each voter loses at most its computed fall, and a band and its share if it was credited.
  have each : ∀ v ∈ voters, balanceAt pulled v.toNat ≤ balanceAt state v.toNat + fall v.toNat +
      ((if v ∈ creditedKeys then inc + 2 * preset.downwardBand + syncPMax else 0) +
        min (pc v + deposit v) (below v)) := by
    intro v voter
    have active : current v.toNat = true := voterActive v voter
    have bound := falls v active (voting v voter).2
    have fallen : balanceAt pulled v.toNat - balanceAt state v.toNat ≤ fall v.toNat +
        (if pc v + deposit v = 0 then 0
         else inc + 2 * preset.downwardBand + syncP v.toNat +
           min (pc v + deposit v) (below v)) := bound
    split at fallen
    · omega
    · rename_i credited
      have member : v ∈ creditedKeys := by
        by_contra outside
        exact credited (by rw [(zeroOff v outside).1, (zeroOff v outside).2])
      have position : v.toNat ∈ positions := by
        obtain ⟨_, found, -⟩ := isActiveAt_eq_true_iff.mp active
        exact Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1
      have largest := Finset.le_sup (f := fun i => if current i = true then syncP i else 0)
        position
      simp only [active, ↓reduceIte] at largest
      have most : syncP v.toNat ≤ syncPMax := largest
      simp only [member, ↓reduceIte]
      omega
  have voterSum := Finset.sum_le_sum each
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at voterSum
  have fallSum := voters_sum_le fall (positions := positions.filter fun i => current i = true)
    fun v voter => by
      have active : current v.toNat = true := voterActive v voter
      obtain ⟨_, found, -⟩ := isActiveAt_eq_true_iff.mp active
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Array.getElem?_eq_some_iff.mp found).1, active⟩
  -- The credited voters number at most the credited validators of the branch.
  have creditedLe : creditedKeys.card ≤ creditedP :=
    creditedCard.trans (credited_mono ((Nat.le_add_left _ _).trans nPLe)
      (blockDeposits_mono ((Nat.le_add_left _ _).trans nPLe)))
  have bandSum : ∑ v ∈ voters, (if v ∈ creditedKeys then
      inc + 2 * preset.downwardBand + syncPMax else 0) ≤
      creditedP * (inc + 2 * preset.downwardBand + syncPMax) := by
    refine (Finset.sum_le_sum_of_ne_zero (t := creditedKeys) fun v _ nonzero =>
      by_contra fun outside => nonzero (by simp [outside])).trans ?_
    rw [Finset.sum_ite_of_true fun v member => member, Finset.sum_const,
      nsmul_eq_mul, Nat.cast_id]
    exact Nat.mul_le_mul_right _ creditedLe
  -- The credits that hide a queued payment fit the mask budget.
  have maskSum : ∑ v ∈ voters, min (pc v + deposit v) (below v) ≤ maskBudget := by
    have byBelow : ∑ v ∈ voters, min (pc v + deposit v) (below v) ≤ ∑ v ∈ owed, below v :=
      (Finset.sum_le_sum fun v _ => Nat.min_le_right _ _).trans
        (Finset.sum_le_sum_of_ne_zero fun v _ nonzero =>
          by_contra fun outside => nonzero (belowOff v outside))
    by_cases electra : Fork.pectra ≤ fork
    · have byCredit : ∑ v ∈ voters, min (pc v + deposit v) (below v) ≤
          ∑ v ∈ creditedKeys, pc v := by
        refine (Finset.sum_le_sum fun v _ => Nat.min_le_left _ _).trans ?_
        refine (Finset.sum_le_sum_of_ne_zero (f := fun v => pc v + deposit v) (t := creditedKeys)
          fun v _ nonzero => by_contra fun outside =>
            nonzero (by simp [(zeroOff v outside).1, (zeroOff v outside).2])).trans
          (Finset.sum_le_sum fun v _ => by rw [electraZero electra v, Nat.add_zero])
      have budget' : ∑ v ∈ creditedKeys, pc v ≤ proposerCredit + whistleblowerP := budget
      have maskEq : maskBudget = min (proposerCredit + whistleblowerP)
          (preset.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP.toNat *
            (preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat -
              preset.MIN_ACTIVATION_BALANCE.toNat)) := by
        simp only [maskBudget, capMax, electra, ↓reduceIte]
      simp only [electra, ↓reduceIte] at belowSum
      rw [maskEq]
      exact le_min (byCredit.trans budget') (byBelow.trans belowSum)
    · simp only [electra, ↓reduceIte] at belowSum
      exact (byBelow.trans belowSum).trans (Nat.zero_le _)
  have fallBound : stake (fun v => balanceAt pulled v.toNat) voters ≤
      stake (fun v => balanceAt state v.toNat) voters + loss := by
    simp only [stake]
    rw [lossEq]
    omega
  omega

end EthLib.Consensus.Models.Network
