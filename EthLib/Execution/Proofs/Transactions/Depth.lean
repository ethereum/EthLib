module

public import EthLib.Execution.Proofs.Evm.Call.ChildGas
public import EthLib.Execution.Proofs.Evm.Call.Depth
public import EthLib.Execution.Proofs.Transactions.Observe
public import EthLib.Execution.Proofs.Transactions.Process
public import EthLib.Execution.Proofs.Transactions.Validity

/-!
# Proofs: every frame of a transaction has a depth of at most 1024

A transaction starts its message at depth 0.

So every frame of its run is within the depth limit, and an observer sees no deeper frame.

From Fusaka, the cap of [EIP-7825][eip7825] bounds the gas of each frame by `2^24`.

From Berlin, each level pays at least 100 and passes on all but one 64th, by [EIP-150][eip150].

So no frame that runs code is then deeper than 501.

[eip7825]: https://eips.ethereum.org/EIPS/eip-7825#specification
[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.State (BlockState)
open EthLib.Execution.Evm.GasCosts (TX_MAX_GAS_LIMIT)

variable {Meter : Type} [GasMeter Meter] {σ : Type}

omit [GasMeter Meter] in
/-- A lifted result that leads to a successful run is a success, and the rest runs from it. -/
private theorem liftExcept_bind_eq_ok {α β : Type} {x : Except EvmError α}
    {g : α → StateT σ (Except EvmError) β} {s : σ} {r : β × σ}
    (h : (liftExcept x >>= g) s = .ok r) : ∃ a, x = .ok a ∧ g a s = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- The first frame of a message keeps the depth of the message. -/
private theorem depth_prepareFirstFrame {fork : Fork} {chainId : Nat} {message : Message fork}
    {state : State.TransactionState} {substate : Substate} {auths : List Authorization}
    {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    first.message.depth = message.depth := by
  unfold prepareFirstFrame at h
  dsimp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  all_goals
    simp only [Except.ok.injEq] at h
    subst h
    rfl

/-- The message of a transaction starts at depth 0. -/
private theorem depth_transactionMessage {fork : Fork} {env : BlockEnvironment fork}
    {txEnv : TransactionEnvironment fork} {state : State.TransactionState}
    {sender target : Address} {gas : Nat} {tx : Transaction} {message : Message fork}
    (h : transactionMessage env txEnv state sender target gas tx = .ok message) :
    message.depth = 0 := by
  unfold transactionMessage at h
  split at h
  · obtain ⟨_, -, rfl⟩ := Base.map_ok_iff.mp h
    rfl
  · cases h
    rfl

/-- The first frame of a message holds at most the gas of the message.

The meter must not hold more after a commit. -/
private theorem gas_le_prepareFirstFrame [LawfulGasMeter Meter] {fork : Fork}
    (commit : ∀ meter : Meter, GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter)
    {chainId : Nat} {message : Message fork} {state : State.TransactionState}
    {substate : Substate} {auths : List Authorization} {paid : Std.ExtTreeSet Address}
    {first : FirstFrame fork Meter}
    (h : prepareFirstFrame chainId message state substate auths paid = .ok first) :
    first.message.gas ≤ message.gas := by
  have held := meter_prepareFirstFrame
    (Q := fun a b : Meter => GasMeter.gasHeld b ≤ GasMeter.gasHeld a)
    (fun _ => Nat.le_refl _) (fun hab hbc => Nat.le_trans hbc hab)
    (fun hc => Nat.le_trans (Nat.le_add_right _ _) (LawfulGasMeter.gasHeld_charge hc))
    (fun hc => LawfulGasMeter.gasHeld_chargeState hc) commit h
  rw [gas_prepareFirstFrame h]
  exact Nat.le_trans held (Nat.le_of_eq (LawfulGasMeter.gasHeld_start _ _))

/-- An observed message of a transaction whose depth and gas have a property keeps an invariant.

The property `P` of the depth and the gas must hold for less gas too.

Each message that a frame with the property sends must have it. -/
private theorem processMessageCallWith_inv [LawfulGasMeter Meter] {fork : Fork}
    (P : Nat → Nat → Prop) (mono : ∀ {depth gas gas'}, gas' ≤ gas → P depth gas → P depth gas')
    (commit : ∀ meter : Meter, GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter)
    (inv : σ → Prop) (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, P evm.message.depth evm.message.gas →
      GasMeter.gasHeld evm.gas ≤ evm.message.gas → inv s → inv (f evm result s))
    (closed : ∀ (evm caller : Evm fork Meter) message resume,
      P evm.message.depth evm.message.gas → GasMeter.gasHeld evm.gas ≤ evm.message.gas →
      step fork evm = .ok (.child caller message resume) → P message.depth message.gas)
    (chainId : Nat) (message : Message fork) (holds : P message.depth message.gas)
    (state : State.TransactionState) (substate : Substate) (auths : List Authorization)
    (paid : Std.ExtTreeSet Address) {s : σ} (start : inv s) {r : CallOutput × σ}
    (run : processMessageCallWith (Meter := Meter) (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) chainId message state substate auths paid s =
        .ok r) :
    inv r.2 := by
  rw [processMessageCallWith] at run
  rcases hp : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid
    with ⟨e, read⟩ | first
  · rw [hp] at run
    by_cases aborts : e.aborts <;>
      simp [aborts, pure, StateT.pure, throw, throwThe, MonadExceptOf.throw, StateT.lift,
        bind, Except.bind, Except.pure] at run
    subst run
    exact start
  · rw [hp] at run
    -- The first frame keeps the depth of the message, and holds at most its gas.
    have first_holds : P first.message.depth first.message.gas := by
      rw [depth_prepareFirstFrame hp]
      exact mono (gas_le_prepareFirstFrame commit hp) holds
    dsimp only at run
    cases ht : message.target <;> simp only [ht] at run
    · obtain ⟨⟨⟨evm, used⟩, s'⟩, hrun, rest⟩ := Base.stateT_bind_eq_ok run
      cases rest
      exact processCreateMessageWith_inv_of (fun m => P m.depth m.gas) inv f keeps closed
        first_holds _ _ _ _ start hrun
    · obtain ⟨⟨⟨evm, used⟩, s'⟩, hrun, rest⟩ := Base.stateT_bind_eq_ok run
      cases rest
      exact processMessageWith_inv_of (fun m => P m.depth m.gas) inv f keeps closed
        first_holds _ _ _ _ start hrun

/-- An observed run of a transaction with one gas meter keeps an invariant.

Its message starts at depth 0, with the execution gas of the transaction.

That depth and gas must have the property `P` of the observed message. -/
private theorem runTransactionWith_inv [LawfulGasMeter Meter] {fork : Fork}
    (P : Nat → Nat → Prop) (mono : ∀ {depth gas gas'}, gas' ≤ gas → P depth gas → P depth gas')
    (commit : ∀ meter : Meter, GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter)
    (inv : σ → Prop) (f : Evm fork Meter → Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ evm result s, P evm.message.depth evm.message.gas →
      GasMeter.gasHeld evm.gas ≤ evm.message.gas → inv s → inv (f evm result s))
    (closed : ∀ (evm caller : Evm fork Meter) message resume,
      P evm.message.depth evm.message.gas → GasMeter.gasHeld evm.gas ≤ evm.message.gas →
      step fork evm = .ok (.child caller message resume) → P message.depth message.gas)
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules)
    (holds : P 0 (allocateGas fork tx included.intrinsicGas lifted).execution) {s : σ}
    (start : inv s) {r : TransactionOutput × σ}
    (run : runTransactionWith Meter (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
        .ok r) :
    inv r.2 := by
  rw [runTransactionWith] at run
  obtain ⟨target, -, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨state, -, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨message, hm, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨⟨output, s'⟩, hcall, run⟩ := Base.stateT_bind_eq_ok run
  have back : inv s' := processMessageCallWith_inv P mono commit inv f keeps closed _ _
    (by simp only [depth_transactionMessage hm, gas_transactionMessage hm]; exact holds)
    _ _ _ _ start hcall
  obtain ⟨_, -, run⟩ := liftExcept_bind_eq_ok run
  obtain ⟨_, -, run⟩ := liftExcept_bind_eq_ok run
  cases run
  exact back

/-- A commit does not raise the gas that the meter before Glamsterdam holds. -/
private theorem gasHeld_commit_nat (meter : Nat) :
    GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter :=
  Nat.le_refl _

/-- A commit does not raise the gas that the meter of Glamsterdam holds. -/
private theorem gasHeld_commit_stateGas (meter : StateGasMeter) :
    GasMeter.gasHeld (GasMeter.commit meter) ≤ GasMeter.gasHeld meter := by
  simp only [GasMeter.gasHeld, GasMeter.commit, StateGasMeter.gasHeld, StateGasMeter.commit]
  omega

/-- A run of a transaction that succeeds keeps an invariant of the record of its observer.

The record needs to keep the invariant only at frames within the depth limit, at every meter. -/
theorem processTransactionWith_inv_of_depth_le {fork : Fork} (inv : σ → Prop)
    (f : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) result s,
      evm.message.depth ≤ STACK_DEPTH_LIMIT → inv s → inv (f evm result s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules) {s : σ} (start : inv s)
    {r : TransactionOutput × σ}
    (run : processTransactionWith (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
        .ok r) :
    inv r.2 := by
  rw [processTransactionWith] at run
  by_cases hegota : .hegota ≤ fork
  · rw [ite_eq_left hegota] at run
    cases run
  rw [ite_eq_right hegota] at run
  -- Each fork runs the transaction with one meter, and the observer keeps the invariant at it.
  by_cases glamsterdam : fork ≥ .glamsterdam
  · rw [ite_eq_left glamsterdam] at run
    exact runTransactionWith_inv (fun depth _ => depth ≤ STACK_DEPTH_LIMIT) (fun _ h => h)
      gasHeld_commit_stateGas inv f (fun evm result s depth _ => keeps evm result s depth)
      (fun _ _ _ _ _ _ h => depth_le_of_step_eq_child h) env block included tx precompiles lifted
      (Nat.zero_le _) start run
  · rw [ite_eq_right glamsterdam] at run
    exact runTransactionWith_inv (fun depth _ => depth ≤ STACK_DEPTH_LIMIT) (fun _ h => h)
      gasHeld_commit_nat inv f (fun evm result s depth _ => keeps evm result s depth)
      (fun _ _ _ _ _ _ h => depth_le_of_step_eq_child h) env block included tx precompiles lifted
      (Nat.zero_le _) start run

/-! ## The gas and the depth of the frames from Berlin -/

/-- The most gas that a frame at depth `d` can hold, when the first frame holds at most `G`.

From Berlin, each level pays at least 100 and passes on at most all but one 64th of the rest. -/
def gasAtDepth (G : Nat) : Nat → Nat
  | 0 => G
  | d + 1 => maxMessageCallGas (gasAtDepth G d - 100)

/-- All but one 64th keeps the order. -/
private theorem maxMessageCallGas_mono {a b : Nat} (h : a ≤ b) :
    maxMessageCallGas a ≤ maxMessageCallGas b := by
  unfold maxMessageCallGas
  have : a / 64 ≤ b / 64 := Nat.div_le_div_right h
  omega

/-- The bound shrinks from one level to the next. -/
private theorem gasAtDepth_succ_le (G d : Nat) : gasAtDepth G (d + 1) ≤ gasAtDepth G d := by
  show maxMessageCallGas (gasAtDepth G d - 100) ≤ gasAtDepth G d
  unfold maxMessageCallGas
  omega

/-- The bound shrinks with the depth. -/
theorem gasAtDepth_anti (G : Nat) {d d' : Nat} (h : d ≤ d') : gasAtDepth G d' ≤ gasAtDepth G d := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans (gasAtDepth_succ_le G _) ih

/-- Levels add up: `a + b` levels from `G` are `b` levels from the bound after `a`. -/
private theorem gasAtDepth_add (G a b : Nat) :
    gasAtDepth G (a + b) = gasAtDepth (gasAtDepth G a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show maxMessageCallGas (gasAtDepth G (a + b) - 100) =
      maxMessageCallGas (gasAtDepth (gasAtDepth G a) b - 100)
    rw [ih]

/-- With `2^24` gas, a frame at depth 501 holds less than 100 gas, too little for a call. -/
theorem gasAtDepth_txMax_lt : gasAtDepth TX_MAX_GAS_LIMIT 501 < 100 := by
  -- The bound every 25 levels, then one more level from 117 gas.
  have e1 : gasAtDepth TX_MAX_GAS_LIMIT 25 = 11315037 := by decide
  have e2 : gasAtDepth TX_MAX_GAS_LIMIT 50 = 7630522 := by
    rw [gasAtDepth_add _ 25 25, e1]
    decide
  have e3 : gasAtDepth TX_MAX_GAS_LIMIT 75 = 5145134 := by
    rw [gasAtDepth_add _ 50 25, e2]
    decide
  have e4 : gasAtDepth TX_MAX_GAS_LIMIT 100 = 3468612 := by
    rw [gasAtDepth_add _ 75 25, e3]
    decide
  have e5 : gasAtDepth TX_MAX_GAS_LIMIT 125 = 2337712 := by
    rw [gasAtDepth_add _ 100 25, e4]
    decide
  have e6 : gasAtDepth TX_MAX_GAS_LIMIT 150 = 1574867 := by
    rw [gasAtDepth_add _ 125 25, e5]
    decide
  have e7 : gasAtDepth TX_MAX_GAS_LIMIT 175 = 1060289 := by
    rw [gasAtDepth_add _ 150 25, e6]
    decide
  have e8 : gasAtDepth TX_MAX_GAS_LIMIT 200 = 713179 := by
    rw [gasAtDepth_add _ 175 25, e7]
    decide
  have e9 : gasAtDepth TX_MAX_GAS_LIMIT 225 = 479035 := by
    rw [gasAtDepth_add _ 200 25, e8]
    decide
  have e10 : gasAtDepth TX_MAX_GAS_LIMIT 250 = 321094 := by
    rw [gasAtDepth_add _ 225 25, e9]
    decide
  have e11 : gasAtDepth TX_MAX_GAS_LIMIT 275 = 214554 := by
    rw [gasAtDepth_add _ 250 25, e10]
    decide
  have e12 : gasAtDepth TX_MAX_GAS_LIMIT 300 = 142688 := by
    rw [gasAtDepth_add _ 275 25, e11]
    decide
  have e13 : gasAtDepth TX_MAX_GAS_LIMIT 325 = 94209 := by
    rw [gasAtDepth_add _ 300 25, e12]
    decide
  have e14 : gasAtDepth TX_MAX_GAS_LIMIT 350 = 61510 := by
    rw [gasAtDepth_add _ 325 25, e13]
    decide
  have e15 : gasAtDepth TX_MAX_GAS_LIMIT 375 = 39451 := by
    rw [gasAtDepth_add _ 350 25, e14]
    decide
  have e16 : gasAtDepth TX_MAX_GAS_LIMIT 400 = 24573 := by
    rw [gasAtDepth_add _ 375 25, e15]
    decide
  have e17 : gasAtDepth TX_MAX_GAS_LIMIT 425 = 14535 := by
    rw [gasAtDepth_add _ 400 25, e16]
    decide
  have e18 : gasAtDepth TX_MAX_GAS_LIMIT 450 = 7763 := by
    rw [gasAtDepth_add _ 425 25, e17]
    decide
  have e19 : gasAtDepth TX_MAX_GAS_LIMIT 475 = 3197 := by
    rw [gasAtDepth_add _ 450 25, e18]
    decide
  have e20 : gasAtDepth TX_MAX_GAS_LIMIT 500 = 117 := by
    rw [gasAtDepth_add _ 475 25, e19]
    decide
  rw [gasAtDepth_add _ 500 1, e20]
  decide

/-- From Berlin, a run of a transaction keeps an invariant given the gas of each frame by depth.

The transaction must give its message at most `G` execution gas.

The record may use that a frame at depth `d` holds at most `gasAtDepth G d` gas.

It may also use that its depth is 0, or that the bound of the level above is at least 100. -/
theorem processTransactionWith_inv_of_gasAtDepth {fork : Fork} (hfork : .berlin ≤ fork)
    {G : Nat} (inv : σ → Prop)
    (f : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) result s,
      GasMeter.gasHeld evm.gas ≤ gasAtDepth G evm.message.depth →
      (evm.message.depth = 0 ∨ 100 ≤ gasAtDepth G (evm.message.depth - 1)) →
      inv s → inv (f evm result s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules)
    (gas : (allocateGas fork tx included.intrinsicGas lifted).execution ≤ G) {s : σ}
    (start : inv s) {r : TransactionOutput × σ}
    (run : processTransactionWith (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
        .ok r) :
    inv r.2 := by
  -- A message at depth `d` has at most `gasAtDepth G d` gas, and its sender held at least 100.
  let P : Nat → Nat → Prop := fun depth gas =>
    gas ≤ gasAtDepth G depth ∧ (depth = 0 ∨ 100 ≤ gasAtDepth G (depth - 1))
  have mono : ∀ {depth gas gas'}, gas' ≤ gas → P depth gas → P depth gas' :=
    fun hle h => ⟨Nat.le_trans hle h.1, h.2⟩
  have holds : P 0 (allocateGas fork tx included.intrinsicGas lifted).execution :=
    ⟨gas, Or.inl rfl⟩
  -- Each message that a frame with the property sends has it, at either meter.
  have closed : ∀ {Meter : Type} [GasMeter Meter] [LawfulGasMeter Meter],
      (∀ {meter after : Meter} {amount : Nat}, GasMeter.charge meter amount = .ok after →
        amount ≤ GasMeter.gasLeft meter) →
      ∀ (evm caller : Evm fork Meter) message resume,
        P evm.message.depth evm.message.gas → GasMeter.gasHeld evm.gas ≤ evm.message.gas →
        step fork evm = .ok (.child caller message resume) → P message.depth message.gas := by
    intro Meter _ _ charge evm caller message resume hp held h
    obtain ⟨hundred, hgas⟩ := gas_le_of_step_eq_child hfork charge h
    have hframe := Nat.le_trans held hp.1
    rw [depth_of_step_eq_child h]
    refine ⟨Nat.le_trans hgas (maxMessageCallGas_mono (Nat.sub_le_sub_right hframe 100)), ?_⟩
    exact Or.inr (by simpa using Nat.le_trans hundred hframe)
  rw [processTransactionWith] at run
  by_cases hegota : .hegota ≤ fork
  · rw [ite_eq_left hegota] at run
    cases run
  rw [ite_eq_right hegota] at run
  by_cases glamsterdam : fork ≥ .glamsterdam
  · rw [ite_eq_left glamsterdam] at run
    exact runTransactionWith_inv P mono gasHeld_commit_stateGas inv f
      (fun evm result s hp held => keeps evm result s (Nat.le_trans held hp.1) hp.2)
      (closed charge_le_gasLeft_stateGas) env block included tx precompiles lifted holds start run
  · rw [ite_eq_right glamsterdam] at run
    exact runTransactionWith_inv P mono gasHeld_commit_nat inv f
      (fun evm result s hp held => keeps evm result s (Nat.le_trans held hp.1) hp.2)
      (closed charge_le_gasLeft_nat) env block included tx precompiles lifted holds start run

/-- From Fusaka, a valid transaction gives its message at most `2^24` execution gas.

From Fusaka to BPO5 its gas limit is at most `2^24`, as [EIP-7825][eip7825] asks.

From Glamsterdam, the execution gas is capped at `2^24`, as no rule is lifted.

[eip7825]: https://eips.ethereum.org/EIPS/eip-7825#specification -/
theorem allocateGas_execution_le_txMax {fork : Fork} (hfork : .fusaka ≤ fork) {sender : Address}
    {tx : Transaction} {intrinsic : Nat}
    (valid : validateTransaction fork sender tx = .ok intrinsic) :
    (allocateGas fork tx intrinsic).execution ≤ TX_MAX_GAS_LIMIT := by
  by_cases hg : fork ≥ .glamsterdam
  · exact Nat.le_trans (allocateGas_execution_le hg tx intrinsic) (Nat.sub_le _ _)
  · have hlt : fork < .glamsterdam := Nat.lt_of_not_le hg
    obtain ⟨-, -, -, -, cap, -⟩ := validateTransaction_eq_ok_iff.mp valid
    rw [allocateGas_of_lt hlt]
    exact Nat.le_trans (Nat.sub_le _ _) (cap hfork hlt)

/-- From Fusaka, no frame of a transaction that runs code is deeper than 501.

None holds more than `2^24` execution gas.

So the depth check of a call or a creation, at 1024, never fires.

The transaction must give its message at most `2^24` execution gas, as each valid one does.

A simulation that lifts the cap from Glamsterdam can give it more.

A run that succeeds then keeps an invariant that needs to hold only at such frames. -/
theorem processTransactionWith_inv_of_fusaka {fork : Fork} (hfork : .fusaka ≤ fork)
    (inv : σ → Prop)
    (f : {Meter : Type} → [GasMeter Meter] → Evm fork Meter →
      Except EvmError (StepResult fork Meter) → σ → σ)
    (keeps : ∀ {Meter : Type} [GasMeter Meter] (evm : Evm fork Meter) result s,
      evm.message.depth ≤ 501 → GasMeter.gasHeld evm.gas ≤ TX_MAX_GAS_LIMIT →
      inv s → inv (f evm result s))
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address) (lifted : LiftedRules)
    (gas : (allocateGas fork tx included.intrinsicGas lifted).execution ≤ TX_MAX_GAS_LIMIT)
    {s : σ} (start : inv s) {r : TransactionOutput × σ}
    (run : processTransactionWith (M := StateT σ (Except EvmError))
      (fun evm result => modify (f evm result)) env block included tx precompiles lifted s =
        .ok r) :
    inv r.2 := by
  refine processTransactionWith_inv_of_gasAtDepth (Nat.le_trans (by decide) hfork) inv f
    (fun evm result s held above => keeps evm result s ?_ ?_) env block included tx
    precompiles lifted gas start run
  · -- A frame below depth 501 has a level above it that held less than 100.
    refine Nat.le_of_not_lt fun deep => ?_
    rcases above with h | h
    · omega
    · have := gasAtDepth_anti TX_MAX_GAS_LIMIT (show 501 ≤ evm.message.depth - 1 by omega)
      have := gasAtDepth_txMax_lt
      omega
  · exact Nat.le_trans held (gasAtDepth_anti _ (Nat.zero_le _))

end EthLib.Execution.Transactions
