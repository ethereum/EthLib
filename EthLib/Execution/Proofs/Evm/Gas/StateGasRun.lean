module

public import EthLib.Execution.Proofs.Evm.Gas.StateGas

/-!
# Proofs: the state gas meter over any sequence of operations

A run of a frame charges and refills state gas, charges execution gas and runs child frames.

Its reservoir and its spill then depend only on its net state gas, whatever the order.

So refills that undo every outstanding charge, in any order, put them back.

A child frame that fails leaves the meter of its caller as it found it, but for execution gas.

Source: [EIP-8037][eip8037], its reservoir model and its accounting for halts and reverts.

[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-halts-and-reverts
-/

@[expose] public section

namespace EthLib.Execution.Evm.StateGasMeter

/-! ## How a child frame ends -/

/-- How a child frame ends: it succeeds, reverts or halts. -/
inductive Ending where
  /-- The child succeeds, and keeps its meter. -/
  | success
  /-- The child reverts, and rolls its meter back. -/
  | revert
  /-- The child halts, rolls its meter back, and loses its execution gas. -/
  | halt
  deriving DecidableEq

/-- The meter of a child that ends in the way `ending`, from the meter `meter` of its last step. -/
def Ending.meter : Ending → StateGasMeter → StateGasMeter
  | .success, meter => meter
  | .revert, meter => meter.restore
  | .halt, meter => meter.halt

/-- The child succeeded. -/
def Ending.succeeded (ending : Ending) : Bool :=
  ending = .success

/-! ## A run of a frame -/

/-- A run of the meter of a frame, from one meter to another, with a net state gas.

The net state gas is what the run charges, less what it refills.

A child frame adds its net state gas when it succeeds, and nothing otherwise.

Commits are not steps: only the top frame commits, before its code runs. -/
inductive Runs : StateGasMeter → Int → StateGasMeter → Prop where
  /-- A run with no operation keeps the meter. -/
  | done (meter : StateGasMeter) : Runs meter 0 meter
  /-- A charge of execution gas. -/
  | charge {meter paid after : StateGasMeter} {amount : Nat} {net : Int} :
      meter.charge amount = .ok paid → Runs paid net after → Runs meter net after
  /-- A charge of state gas. -/
  | chargeState {meter paid after : StateGasMeter} {amount : Nat} {net : Int} :
      meter.chargeState amount = .ok paid → Runs paid net after → Runs meter (amount + net) after
  /-- A refill of state gas. -/
  | refill {meter after : StateGasMeter} {amount : Nat} {net : Int} :
      Runs (meter.refill amount) net after → Runs meter (net - amount) after
  /-- A child frame that runs: the caller pays `cost`, and the child starts with `gas`.

  The gas may include a stipend that the caller does not pay.

  The child gets the whole reservoir of the caller, and gives back what is left of it. -/
  | call {meter paid child after : StateGasMeter} {cost gas : Nat} {inner net : Int}
      (ending : Ending) :
      meter.charge cost = .ok paid → Runs (start gas paid.reservoir) inner child →
      Runs (absorb paid.drain (ending.meter child) ending.succeeded) net after →
      Runs meter ((if ending = .success then inner else 0) + net) after
  /-- A child frame that never runs: the caller pays `cost`, and gets back `gas`.

  It also gets its reservoir back. -/
  | skip {meter paid after : StateGasMeter} {cost gas : Nat} {net : Int} :
      meter.charge cost = .ok paid → Runs (cancel paid.drain (start gas paid.reservoir)) net after →
      Runs meter net after

/-! ## What each operation keeps -/

/-- A charge of execution gas keeps every field but the execution gas left. -/
private theorem charge_keeps {meter paid : StateGasMeter} {amount : Nat}
    (h : meter.charge amount = .ok paid) :
    paid.reservoir = meter.reservoir ∧ paid.spill = meter.spill ∧ paid.baseline = meter.baseline ∧
      paid.committed = meter.committed ∧ paid.grant = meter.grant := by
  obtain ⟨-, rfl⟩ := charge_eq_ok_iff.mp h
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A charge of state gas keeps the baseline, the committed spill and the grant. -/
private theorem chargeState_keeps {meter paid : StateGasMeter} {amount : Nat}
    (h : meter.chargeState amount = .ok paid) :
    paid.baseline = meter.baseline ∧ paid.committed = meter.committed ∧
      paid.grant = meter.grant := by
  unfold chargeState at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl⟩
    · cases h

/-- A run keeps the baseline, the committed spill and the grant of the meter.

The net state gas used grows by the net state gas of the run. -/
theorem Runs.keeps {meter after : StateGasMeter} {net : Int} (h : Runs meter net after) :
    after.baseline = meter.baseline ∧ after.committed = meter.committed ∧
      after.grant = meter.grant ∧ after.stateGasUsed = meter.stateGasUsed + net := by
  induction h with
  | done => exact ⟨rfl, rfl, rfl, by omega⟩
  | charge hc _ ih =>
    obtain ⟨-, -, hb, hcm, hg⟩ := charge_keeps hc
    obtain ⟨b, c, g, u⟩ := ih
    refine ⟨b.trans hb, c.trans hcm, g.trans hg, ?_⟩
    rw [u, stateGasUsed_charge hc]
  | chargeState hc _ ih =>
    obtain ⟨hb, hcm, hg⟩ := chargeState_keeps hc
    obtain ⟨b, c, g, u⟩ := ih
    refine ⟨b.trans hb, c.trans hcm, g.trans hg, ?_⟩
    rw [u, stateGasUsed_chargeState hc]
    omega
  | refill _ ih =>
    obtain ⟨b, c, g, u⟩ := ih
    refine ⟨b, c, g, ?_⟩
    rw [u, stateGasUsed_refill]
    omega
  | @call meter paid child after cost gas inner net ending hc _ _ ihc ih =>
    obtain ⟨hr, hs, hb, hcm, hg⟩ := charge_keeps hc
    obtain ⟨cb, cc, cg, cu⟩ := ihc
    simp only [start] at cb cc cg cu
    -- The caller after the merge, before its later operations.
    have merged :
        (absorb paid.drain (ending.meter child) ending.succeeded).baseline = meter.baseline ∧
        (absorb paid.drain (ending.meter child) ending.succeeded).committed = meter.committed ∧
        (absorb paid.drain (ending.meter child) ending.succeeded).grant = meter.grant ∧
        (absorb paid.drain (ending.meter child) ending.succeeded).stateGasUsed =
          meter.stateGasUsed + if ending = .success then inner else 0 := by
      cases ending with
      | success =>
        -- A child that succeeds adds its net state gas, and the merge repays the spill.
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [Ending.meter, Ending.succeeded, absorb, repay, drain, hb]
        · simp [Ending.meter, Ending.succeeded, absorb, repay, drain, hcm]
        · simp [Ending.meter, Ending.succeeded, absorb, repay, drain, hg]
        · have := stateGasUsed_absorb paid child gas true cg cc
          simp only [enter] at this
          simp only [Ending.meter, Ending.succeeded, decide_true, ↓reduceIte]
          rw [this, cu, stateGasUsed_charge hc]
          simp [stateGasUsed]
      | revert =>
        -- A child that reverts rolls back to the reservoir it got, with no spill.
        simp only [Ending.meter, Ending.succeeded, reduceCtorEq, decide_false, ↓reduceIte,
          absorb, restore, drain, stateGasUsed, Int.add_zero]
        refine ⟨hb, hcm, hg, ?_⟩
        rw [cb, ← hr, ← hs, ← hcm, ← hg]
        omega
      | halt =>
        -- A child that halts rolls back in the same way, and loses its execution gas.
        simp only [Ending.meter, Ending.succeeded, reduceCtorEq, decide_false, ↓reduceIte,
          absorb, StateGasMeter.halt, restore, drain, stateGasUsed, Int.add_zero]
        refine ⟨hb, hcm, hg, ?_⟩
        rw [cb, ← hr, ← hs, ← hcm, ← hg]
        omega
    obtain ⟨mb, mc, mg, mu⟩ := merged
    obtain ⟨b, c, g, u⟩ := ih
    refine ⟨b.trans mb, c.trans mc, g.trans mg, ?_⟩
    rw [u, mu]
    omega
  | skip hc _ ih =>
    obtain ⟨hr, hs, hb, hcm, hg⟩ := charge_keeps hc
    obtain ⟨b, c, g, u⟩ := ih
    refine ⟨b.trans hb, c.trans hcm, g.trans hg, ?_⟩
    -- The caller gets its reservoir back, and keeps its spill.
    rw [u]
    simp only [cancel, drain, start, stateGasUsed, Nat.zero_add]
    rw [hr, hs, hcm, hg]

/-- A run from a meter whose reservoir or spill is empty ends with a meter of the same kind. -/
theorem Runs.repaid {meter after : StateGasMeter} {net : Int} (h : Runs meter net after)
    (repaid : meter.Repaid) : after.Repaid := by
  induction h with
  | done => exact repaid
  | charge hc _ ih =>
    obtain ⟨hr, hs, -⟩ := charge_keeps hc
    exact ih (by unfold Repaid at repaid ⊢; rw [hr, hs]; exact repaid)
  | chargeState hc _ ih => exact ih (repaid_chargeState repaid hc)
  | refill _ ih => exact ih (repaid_refill repaid _)
  | @call meter paid child after cost gas inner net ending hc run _ _ ih =>
    obtain ⟨hr, hs, -⟩ := charge_keeps hc
    obtain ⟨cb, -⟩ := run.keeps
    simp only [start] at cb
    refine ih ?_
    cases ending with
    -- The merge of a child that succeeds repays the spill.
    | success => exact repaid_absorb _ _
    -- A child that fails gives back the reservoir it got, and no spill.
    | revert =>
      simp only [Ending.meter, Ending.succeeded, reduceCtorEq, decide_false, absorb, restore,
        drain, Repaid, cb, hr, hs, Bool.false_eq_true, ↓reduceIte]
      unfold Repaid at repaid
      omega
    | halt =>
      simp only [Ending.meter, Ending.succeeded, reduceCtorEq, decide_false, absorb,
        StateGasMeter.halt, restore, drain, Repaid, cb, hr, hs, Bool.false_eq_true, ↓reduceIte]
      unfold Repaid at repaid
      omega
  | @skip meter paid after cost gas net hc _ ih =>
    obtain ⟨hr, hs, -⟩ := charge_keeps hc
    refine ih ?_
    -- The caller gets its reservoir back, and keeps its spill.
    unfold Repaid at repaid ⊢
    simp only [cancel, drain, start, Nat.zero_add]
    rw [hr, hs]
    exact repaid

/-! ## The reservoir and the spill depend only on the net state gas -/

/-- Two meters with the reservoir or the spill empty and the same net state gas are alike.

They must have the same grant and committed spill.

Then they have the same reservoir and the same spill. -/
theorem Repaid.reservoir_spill_eq {a b : StateGasMeter} (ha : a.Repaid) (hb : b.Repaid)
    (grant : a.grant = b.grant) (committed : a.committed = b.committed)
    (used : a.stateGasUsed = b.stateGasUsed) : a.reservoir = b.reservoir ∧ a.spill = b.spill := by
  unfold Repaid at ha hb
  unfold stateGasUsed at used
  rw [grant, committed] at used
  omega

/-- A run whose net state gas is 0 puts the reservoir, the spill and the net state gas back.

The charges and refills may come in any order, with any execution charge and child between them.

The charges of a child that fails count for nothing, and need no refill.

The meter must start with its reservoir or its spill empty. -/
theorem Runs.eq_of_net_eq_zero {meter after : StateGasMeter} (h : Runs meter 0 after)
    (repaid : meter.Repaid) :
    after.reservoir = meter.reservoir ∧ after.spill = meter.spill ∧
      after.stateGasUsed = meter.stateGasUsed := by
  obtain ⟨-, c, g, u⟩ := h.keeps
  rw [Int.add_zero] at u
  have hrs := Repaid.reservoir_spill_eq (h.repaid repaid) repaid g c u
  exact ⟨hrs.1, hrs.2, u⟩

/-- A frame whose run has a net state gas of 0 ends as it started, but for execution gas.

Its spill is 0, its reservoir is the one it got, and it has used no state gas. -/
theorem Runs.start_eq_of_net_eq_zero {gas reservoir : Nat} {after : StateGasMeter}
    (h : Runs (start gas reservoir) 0 after) :
    after.reservoir = reservoir ∧ after.spill = 0 ∧ after.stateGasUsed = 0 := by
  have back := h.eq_of_net_eq_zero (Or.inr rfl)
  simpa [start, stateGasUsed] using back

/-! ## A child frame that fails -/

/-- A child frame that fails leaves the meter of its caller as it found it, but for execution gas.

The meter it finds is that of the caller after the caller paid for the call.

The child starts with the reservoir of the caller and may run any operations.

It reverts or halts, and the caller then gets back only the execution gas it has left. -/
theorem absorb_failed {paid child : StateGasMeter} {gas : Nat} {inner : Int} (ending : Ending)
    (run : Runs (start gas paid.reservoir) inner child) (failed : ending ≠ .success) :
    absorb paid.drain (ending.meter child) ending.succeeded =
      { paid with gasLeft := paid.gasLeft + (ending.meter child).gasLeft } := by
  -- The child keeps the baseline it started with, which is the reservoir of the caller.
  obtain ⟨cb, -⟩ := run.keeps
  simp only [start] at cb
  cases ending with
  | success => exact absurd rfl failed
  | revert =>
    simp [Ending.meter, Ending.succeeded, absorb, restore, drain, cb]
  | halt =>
    simp [Ending.meter, Ending.succeeded, absorb, StateGasMeter.halt, restore, drain, cb]

end EthLib.Execution.Evm.StateGasMeter
