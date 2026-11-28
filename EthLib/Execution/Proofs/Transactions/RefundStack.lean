module

public import EthLib.Execution.Proofs.Evm.Call.AccessesRun
public import EthLib.Execution.Proofs.Transactions.Refund

/-!
# Proofs: the refund counters of the live frames sum to at least zero after every step

A run of a message keeps a stack of frames: the frame that runs, and the callers that wait.

From the first frame of a transaction, these counters sum to at least zero after every step.

Source: [EIP-2200][eip2200], the refunds of net gas metering.

Source: [EIP-3529][eip3529], the refund to clear a slot from London.

[eip2200]: https://eips.ethereum.org/EIPS/eip-2200#specification
[eip3529]: https://eips.ethereum.org/EIPS/eip-3529#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork)
open EthLib.Execution.State (Rebuildable TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The frames that a run from `start` reaches, with the callers that wait for a message.

The callers come outermost first. -/
inductive RunStack (fork : Fork) (Meter : Type) [GasMeter Meter] :
    BurnStart fork Meter → List (Evm fork Meter) → Evm fork Meter → Prop
  -- A run of a frame reaches that frame, with no caller.
  | here (evm : Evm fork Meter) : RunStack fork Meter (.frame evm) [] evm
  -- A running frame reaches what the frame after its step reaches.
  | next {evm after reached : Evm fork Meter} {callers : List (Evm fork Meter)}
      (running : evm.running = true) (h : step fork evm = .ok (.next after))
      (tail : RunStack fork Meter (.frame after) callers reached) :
      RunStack fork Meter (.frame evm) callers reached
  -- A step that sends a message reaches what its run reaches, and the caller waits.
  | childRun {evm caller reached : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
      {callers : List (Evm fork Meter)} (running : evm.running = true)
      (h : step fork evm = .ok (.child caller message resume))
      (run : RunStack fork Meter (BurnStart.child caller message) callers reached) :
      RunStack fork Meter (.frame evm) (caller :: callers) reached
  -- A certified run of the message ends and the caller resumes: it reaches what the frame does.
  | childTail {evm caller child after reached : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)} {middle : BurnLog}
      {callers : List (Evm fork Meter)} (running : evm.running = true)
      (h : step fork evm = .ok (.child caller message resume))
      (run : RunBurns fork Meter (BurnStart.child caller message) child middle)
      (resumed : resume child = .ok after)
      (tail : RunStack fork Meter (.frame after) callers reached) :
      RunStack fork Meter (.frame evm) callers reached
  -- A message that selects no precompile reaches what its frame reaches.
  | body {evm reached : Evm fork Meter} {callers : List (Evm fork Meter)}
      (selected : precompileAddress fork evm.message = none)
      (run : RunStack fork Meter (.frame evm) callers reached) :
      RunStack fork Meter (.body evm) callers reached
  -- A call reaches what the frame of the state it enters reaches.
  | call {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {reached : Evm fork Meter}
      {callers : List (Evm fork Meter)}
      (entered : Entered fork message state substate entry entrySubstate)
      (run : RunStack fork Meter (.body (startFrame message entry entrySubstate meter))
        callers reached) :
      RunStack fork Meter (.call message state substate meter) callers reached
  -- A creation reaches what the call of its init code reaches, after the account is prepared.
  | create {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {reached : Evm fork Meter}
      {callers : List (Evm fork Meter)}
      (preparation : prepareCreation fork state message.currentTarget = .ok prepared)
      (run : RunStack fork Meter (.call message prepared substate meter) callers reached) :
      RunStack fork Meter (.create message state substate meter) callers reached

/-- A frame that a run reaches with its callers is a frame that the run reaches. -/
theorem RunStack.runReaches {start : BurnStart fork Meter} {callers : List (Evm fork Meter)}
    {reached : Evm fork Meter} (h : RunStack fork Meter start callers reached) :
    RunReaches fork Meter start reached := by
  induction h with
  | here evm => exact .here evm
  | next running h _ ih => exact .next running h ih
  | childRun running h _ ih => exact .childRun running h ih
  | childTail running h run resumed _ ih => exact .childTail running h run resumed ih
  | body selected _ ih => exact .body selected ih
  | call entered _ ih => exact .call entered ih
  | create preparation _ ih => exact .create preparation ih

/-- A frame that a run reaches is reached with some list of callers. -/
theorem RunReaches.runStack {start : BurnStart fork Meter} {reached : Evm fork Meter}
    (h : RunReaches fork Meter start reached) :
    ∃ callers, RunStack fork Meter start callers reached := by
  induction h with
  | here evm => exact ⟨[], .here evm⟩
  | next running h _ ih => exact ih.imp fun _ => .next running h
  | childRun running h _ ih =>
    obtain ⟨callers, run⟩ := ih
    exact ⟨_, .childRun running h run⟩
  | childTail running h run resumed _ ih => exact ih.imp fun _ => .childTail running h run resumed
  | body selected _ ih => exact ih.imp fun _ => .body selected
  | call entered _ ih => exact ih.imp fun _ => .call entered
  | create preparation _ ih => exact ih.imp fun _ => .create preparation

/-! ## What a certified run ends with -/

/-- What a run from `start` ends with: `R` from a frame with `Inv`, or what its message ends with.

A call ends with `Mcall`, and a creation with `Mcreate`. -/
def BurnStart.Ends (Inv : Evm fork Meter → Prop) (R : Evm fork Meter → Evm fork Meter → Prop)
    (Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop) :
    BurnStart fork Meter → Evm fork Meter → Prop
  | .frame evm, ended | .body evm, ended => Inv evm → R evm ended
  | .call message state substate meter, ended => Mcall message state substate meter ended
  | .create message state substate meter, ended => Mcreate message state substate meter ended

/-- What the run of a message that a caller sends ends with relates the caller to the child. -/
theorem BurnStart.ends_child {Inv : Evm fork Meter → Prop}
    {R : Evm fork Meter → Evm fork Meter → Prop}
    {Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    {caller child : Evm fork Meter} {message : Message fork}
    (h : (BurnStart.child caller message).Ends Inv R Mcall Mcreate child) :
    ChildRelByKind Mcall Mcreate caller message child := by
  unfold BurnStart.child at h
  unfold ChildRelByKind ChildRel
  split at h <;> rename_i ht <;> simp only [ht] <;> exact h

/-- A certified run ends with what the rules of its frames and of its messages give.

It needs no bound on gas: the certificate carries the induction. -/
theorem RunBurns.ends_byKind {R : Evm fork Meter → Evm fork Meter → Prop}
    {Inv : Evm fork Meter → Prop}
    {Mcall Mcreate : Message fork → TransactionState → Substate → Meter → Evm fork Meter → Prop}
    (refl : ∀ evm, R evm evm) (trans : ∀ {a b c}, R a b → R b c → R a c)
    (keeps : ∀ {a b}, Inv a → R a b → Inv b)
    (halt : ∀ evm error, Inv evm → R evm (exceptionalHalt evm error))
    (steps : ∀ {evm result}, Inv evm → step fork evm = .ok result →
      StepResult.Keeps R (ChildRelByKind Mcall Mcreate) evm result)
    (stop : ∀ evm : Evm fork Meter, Inv evm → R evm { evm with running := false })
    (precompile : ∀ {address : Nat} {evm after : Evm fork Meter},
      runPrecompile fork address evm = some after → Inv evm → R evm after)
    (call : ∀ {message : Message fork} {state entry : TransactionState}
      {substate entrySubstate : Substate} {meter : Meter} {ended : Evm fork Meter},
      Entered fork message state substate entry entrySubstate →
      (Inv (startFrame message entry entrySubstate meter) →
        R (startFrame message entry entrySubstate meter) ended) →
      Mcall message state substate meter (rollbackOnError state ended))
    (create : ∀ {message : Message fork} {state prepared : TransactionState}
      {substate : Substate} {meter : Meter} {evm after : Evm fork Meter},
      prepareCreation fork state message.currentTarget = .ok prepared →
      Mcall message prepared substate meter evm → depositCode fork state evm = .ok after →
      Mcreate message state substate meter after)
    {start : BurnStart fork Meter} {ended : Evm fork Meter} {log : BurnLog}
    (h : RunBurns fork Meter start ended log) : start.Ends Inv R Mcall Mcreate ended := by
  induction h with
  | stopped evm _ => exact fun _ => refl evm
  | halt => exact fun hinv => halt _ _ hinv
  | next _ hstep _ ih =>
    refine fun hinv => ?_
    have r := steps hinv hstep
    exact trans r (ih (keeps hinv r))
  | child _ hstep _ resumed _ ihRun ihTail =>
    refine fun hinv => ?_
    -- The caller resumes related to the frame, as the run of its message ends as it should.
    have ra := (steps hinv hstep).2 _ _ resumed (BurnStart.ends_child ihRun)
    exact trans ra (ihTail (keeps hinv ra))
  | failedResume => exact fun hinv => halt _ _ hinv
  | bodyFrame _ _ ih => exact ih
  | skipPrecompile evm => exact fun hinv => stop evm hinv
  | precompile _ _ hrun => exact fun hinv => precompile hrun hinv
  | call entered _ _ ih => exact call entered ih
  | createRollback preparation _ deposit _ _ ih | createKeep preparation _ deposit _ ih =>
    exact create preparation ih deposit

/-- From Spurious Dragon, a certified run ends with the refund relation of its frames.

A call and a creation pay for their clears. -/
theorem RunBurns.refund (hfork : .spuriousDragon ≤ fork) {start : BurnStart fork Meter}
    {ended : Evm fork Meter} {log : BurnLog} (h : RunBurns fork Meter start ended log) :
    start.Ends CodeAtNonceOrCode RefundFrame CallRefund CreateRefund ended :=
  h.ends_byKind refundFrame_refl refundFrame_trans (fun ha hab => ha.keeps hab.1)
    (fun evm error _ => refundFrame_of_staticStep (staticStep_exceptionalHalt evm error))
    (fun hinv h => refundFrame_step hinv h)
    (fun _ _ => refundFrame_of_staticStep (.of_sameContext ⟨rfl, rfl, rfl, rfl⟩))
    (fun hrp _ => refundFrame_of_staticStep (staticStep_runPrecompile hrp))
    (fun hentry hrun => callRefund_rollbackOnError hentry hrun)
    (fun hp hm hd => createRefund_depositCode hfork hp hm hd)

/-- Before Istanbul, a certified run lowers no counter of a frame, nor of a message that succeeds.

A message that fails is left out. -/
theorem RunBurns.counter (hfork : fork < .istanbul) {start : BurnStart fork Meter}
    {ended : Evm fork Meter} {log : BurnLog} (h : RunBurns fork Meter start ended log) :
    start.Ends (fun _ => True) CounterLe CounterEnds CounterEnds ended :=
  RunBurns.ends_byKind (Inv := fun _ => True) (R := CounterLe) (Mcall := CounterEnds)
    (Mcreate := CounterEnds) (fun _ => Int.le_refl _) (fun hab hbc => Int.le_trans hab hbc)
    (fun _ _ => trivial) (fun _ _ _ => Int.le_of_eq (staticStep_exceptionalHalt _ _).refund.symm)
    (fun _ h => by rw [childRelByKind_self]; exact counterLe_step hfork h)
    (fun _ _ => Int.le_refl _)
    (fun hrp _ => Int.le_of_eq (staticStep_runPrecompile hrp).refund.symm)
    (fun hentry hrun => counterEnds_rollbackOnError hentry (hrun trivial))
    (fun _ hm hd => counterEnds_depositCode hm hd) h

/-! ## The stack of frames -/

/-- The sum of the refund counters of a list of frames. -/
abbrev counterSum (frames : List (Evm fork Meter)) : Int :=
  (frames.map fun frame => frame.substate.refundCounter).sum

/-- Where a run starts, it runs code only at an account with a nonce or code.

A creation must go to an address with no nonce or code.

Its preparation then gives that address a nonce. -/
def BurnStart.RunsAtNonceOrCode : BurnStart fork Meter → Prop
  | .frame evm | .body evm => CodeAtNonceOrCode evm
  | .call message state _ _ => message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget
  | .create message state _ _ => ¬HasNonceOrCode state message.currentTarget

/-- A message that a step sends starts where it runs code only at an account with a nonce or code.

The step must run code only at an account with a nonce or code.

The caller must keep each nonce or code of the frame. -/
theorem runsAtNonceOrCode_child {evm caller : Evm fork Meter} {message : Message fork}
    {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hinv : CodeAtNonceOrCode evm) (h : step fork evm = .ok (.child caller message resume))
    (hcaller : KeepsNonceOrCode evm.state caller.state) :
    (BurnStart.child caller message).RunsAtNonceOrCode := by
  have hk := childRelByKind_of_step (child := caller)
    (Mcall := fun message state _ _ _ =>
      message.code.size ≠ 0 → HasNonceOrCode state message.currentTarget)
    (Mcreate := fun message state _ _ _ => ¬HasNonceOrCode state message.currentTarget)
    hinv h hcaller (by unfold ChildRelByKind ChildRel; split <;> exact id)
  unfold ChildRelByKind ChildRel at hk
  unfold BurnStart.child
  split <;> rename_i ht <;> simp only [ht] at hk <;> exact hk

/-- From Spurious Dragon, the stack keeps at least the refund surplus of the start of the run.

The surplus of the stack is the sum of the counters, less the refund of the cleared slots. -/
theorem RunStack.surplus_le (hfork : .spuriousDragon ≤ fork) {start : BurnStart fork Meter}
    {callers : List (Evm fork Meter)} {reached : Evm fork Meter}
    (h : RunStack fork Meter start callers reached) (hinv : start.RunsAtNonceOrCode) :
    start.substate.refundCounter - clearedRefund fork start.state ≤
      counterSum callers + refundSurplus reached := by
  induction h with
  | here evm =>
    simp [counterSum, BurnStart.substate, BurnStart.state, refundSurplus]
  | next _ hstep _ ih =>
    have r : RefundFrame _ _ := refundFrame_step hinv hstep
    have := ih (hinv.keeps r.1)
    have := r.2 hinv
    simp only [refundSurplus, BurnStart.substate, BurnStart.state] at *
    omega
  | @childRun evm caller reached message resume callers _ hstep _ ih =>
    obtain ⟨r, -⟩ := refundFrame_step hinv hstep
    have hrun := ih (runsAtNonceOrCode_child hinv hstep r.1.1.1.1)
    have hcaller := r.2 hinv
    -- The message starts from the state of the caller, with a counter of zero.
    have hsub : (BurnStart.child caller message).substate.refundCounter = 0 := by
      unfold BurnStart.child
      split <;> rfl
    rw [BurnStart.state_child, hsub] at hrun
    simp only [refundSurplus, counterSum, List.map_cons, List.sum_cons] at hrun hcaller ⊢
    simp only [BurnStart.substate, BurnStart.state] at hcaller ⊢
    omega
  | childTail _ hstep run resumed _ ih =>
    -- The caller resumes related to the frame, as the run of its message pays for its clears.
    have ra : RefundFrame _ _ :=
      (refundFrame_step hinv hstep).2 _ _ resumed (BurnStart.ends_child (run.refund hfork))
    have := ih (hinv.keeps ra.1)
    have := ra.2 hinv
    simp only [refundSurplus, BurnStart.substate, BurnStart.state] at *
    omega
  | body _ _ ih => exact ih hinv
  | @call message state entry substate entrySubstate meter _ _ entered _ ih =>
    -- The frame of the call starts with the cleared slots and the counter of the call.
    have kentry := keepsNonceOrCode_entered entered
    have := ih fun hs => kentry.2 _ (hinv hs)
    obtain ⟨hslots, hsub⟩ := refund_entered entered
    simp only [BurnStart.substate, BurnStart.state, startFrame, clearedRefund] at *
    rw [hslots, hsub] at this
    exact this
  | @create message state prepared substate meter _ _ preparation _ ih =>
    -- The account of a creation gets a nonce, and the preparation keeps the cleared slots.
    have := ih fun _ => .inl (nonce_prepareCreation hfork preparation)
    have hslots : nonceOrCodeClearedSlots prepared = nonceOrCodeClearedSlots state :=
      nonceOrCodeSlots_prepareCreation slotsOf_clearedSlots (fun h => h.1 rfl) hinv preparation
    simp only [BurnStart.substate, BurnStart.state, clearedRefund] at *
    rw [hslots] at this
    exact this

/-- Before Istanbul, the counters of the stack sum to at least the counter of the start. -/
theorem RunStack.counter_le (hfork : fork < .istanbul) {start : BurnStart fork Meter}
    {callers : List (Evm fork Meter)} {reached : Evm fork Meter}
    (h : RunStack fork Meter start callers reached) :
    start.substate.refundCounter ≤ counterSum callers + reached.substate.refundCounter := by
  induction h with
  | here evm => simp [counterSum, BurnStart.substate]
  | next _ hstep _ ih =>
    have r : CounterLe _ _ := counterLe_step hfork hstep
    simp only [BurnStart.substate] at *
    omega
  | @childRun evm caller reached message resume callers _ hstep _ ih =>
    obtain ⟨r, -⟩ := counterLe_step hfork hstep
    -- The message starts with a counter of zero.
    have hsub : (BurnStart.child caller message).substate.refundCounter = 0 := by
      unfold BurnStart.child
      split <;> rfl
    rw [hsub] at ih
    simp only [counterSum, List.map_cons, List.sum_cons] at ih ⊢
    simp only [BurnStart.substate] at r ⊢
    omega
  | childTail _ hstep run resumed _ ih =>
    have ra : CounterLe _ _ := (counterLe_step hfork hstep).2 _ _ resumed
      (by have := BurnStart.ends_child (run.counter hfork); rwa [childRelByKind_self] at this)
    simp only [BurnStart.substate] at *
    omega
  | body _ _ ih => exact ih
  | call entered _ ih =>
    obtain ⟨-, hsub⟩ := refund_entered entered
    simp only [BurnStart.substate, startFrame] at *
    omega
  | create _ _ ih => exact ih

end EthLib.Execution.Evm

namespace EthLib.Execution.Transactions

open EthLib.Base (Address Fork)
open EthLib.Execution.State (Rebuildable TransactionState)
open EthLib.Execution.Evm

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The counters of the live frames sum to at least zero, after each step of a transaction message.

The steps are those that a run of the message reaches.

The live frames are the frame that runs and the callers that wait for it.

The state must have the rebuild property and no write of storage.

No account with nonce 0 and no code may hold storage in its block state.

The caller must have a nonce or code, and a call must run at its recipient.

The substate must start with a counter of at least zero. -/
theorem runStack_refundCounter_nonneg [LawfulGasMeter Meter] {block : State.BlockState}
    {chainId : Nat} {message : Message fork} {state : TransactionState} {substate : Substate}
    {auths : List Authorization} {paid : Std.ExtTreeSet Address} {first : FirstFrame fork Meter}
    {callers : List (Evm fork Meter)} {reached : Evm fork Meter}
    (valid : RebuildState block state) (empty : Rebuildable block) (hw : NoStorageWrite state)
    (hcaller : HasNonceOrCode state message.caller)
    (htarget : ∀ target, message.target = some target → message.currentTarget = target)
    (hsub : 0 ≤ substate.refundCounter)
    (h : prepareFirstFrame (Meter := Meter) chainId message state substate auths paid = .ok first)
    (reach : RunStack fork Meter
      (if message.target = none then .create first.message first.state first.substate first.meter
      else .call first.message first.state first.substate first.meter) callers reached) :
    0 ≤ counterSum callers + reached.substate.refundCounter := by
  have hsub' : 0 ≤ first.substate.refundCounter := by
    rw [refundCounter_prepareFirstFrame h]
    exact hsub
  -- The start of the run has the substate of the first frame.
  have hstart : (if message.target = none then
      BurnStart.create first.message first.state first.substate first.meter
      else .call first.message first.state first.substate first.meter).substate =
        first.substate := by
    split <;> rfl
  by_cases hfork : fork < .istanbul
  · -- Before Istanbul, no write lowers a counter.
    have := reach.counter_le hfork
    rw [hstart] at this
    exact hsub'.trans this
  -- From Istanbul, the first frame has no cleared slot, and the stack keeps its surplus.
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) (Nat.not_lt.mp hfork)
  obtain ⟨vfirst, -, hdep, hcode⟩ := prepareFirstFrame_rebuildState valid hcaller htarget h
  have hzero : clearedRefund fork first.state = 0 := by
    unfold clearedRefund
    rw [nonceOrCodeClearedSlots_eq_empty vfirst empty (hw.prepareFirstFrame h)]
    simp
  have hclear : 0 ≤ clearedRefund fork reached.state :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hinv : (if message.target = none then
      BurnStart.create first.message first.state first.substate first.meter
      else .call first.message first.state first.substate first.meter).RunsAtNonceOrCode := by
    split
    · -- A creation goes to an address with no nonce or code.
      rename_i hnone
      obtain ⟨hn, hc⟩ := TransactionState.accountDeployable_eq_true_iff.mp (hdep hnone)
      exact fun h => h.elim (fun h1 => by omega) (fun h2 => h2 hc)
    · rename_i hne
      exact hcode hne
  have hstate : (if message.target = none then
      BurnStart.create first.message first.state first.substate first.meter
      else .call first.message first.state first.substate first.meter).state = first.state := by
    split <;> rfl
  have := reach.surplus_le hsd hinv
  rw [hstart, hstate, hzero] at this
  unfold refundSurplus at this
  omega

end EthLib.Execution.Transactions
