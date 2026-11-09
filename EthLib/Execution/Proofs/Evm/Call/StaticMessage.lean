module

public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Evm.Call.MessageCall
public import EthLib.Execution.Proofs.Evm.Call.StaticStep

/-!
# Proofs: a message in a frame that must not change the state

A message that is static and is a call changes no storage and no transient storage.

Before Paris, a call touches its target and gives an absent address the empty account.

From Byzantium, [EIP-214][e214] adds STATICCALL, and a static call changes the state by touches.

Each touched address goes from no account to the empty account.

[EIP-161][e161] deletes the touched empty accounts, leaving only deleted empty accounts.

From Paris, [EIP-7523][e7523] allows no empty account, so a call drops the touch.

Every address then stays as it was, up to the records of reads.

Each statement holds whatever the code of the message does, however deep its calls.

The message runs code at an account that holds code, when it has code.

A value that it sends goes to its own sender, whose account holds code.

A message that fails rolls back to its start, so the statements hold for it too.

[e161]: https://eips.ethereum.org/EIPS/eip-161#specification
[e214]: https://eips.ethereum.org/EIPS/eip-214#specification
[e7523]: https://eips.ethereum.org/EIPS/eip-7523
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256 toAddressMasked)
open EthLib.Execution.State (Account EMPTY_ACCOUNT EMPTY_CODE_HASH TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- A precompile is a static step. -/
theorem staticStep_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : StaticStep evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact staticStep_exceptionalHalt _ _
  · split at h
    · cases h
      exact staticStep_exceptionalHalt _ _
    · cases h
      exact ⟨StateKept.refl _, rfl, rfl, rfl⟩

omit [GasMeter Meter] in
/-- The frame that starts a static message is a static frame. -/
theorem StaticFrame.start {state : State.TransactionState} {message : Message fork}
    (h : StaticMessage state message) (substate : Substate) (meter : Meter) :
    StaticFrame (startFrame message state substate meter) :=
  ⟨h.1, rfl, h.2.2.1⟩

omit [GasMeter Meter] in
/-- A message that a state may send, from a state that differs from it only by reads. -/
theorem StaticMessage.of_sameOutside {state state' : State.TransactionState}
    {message : Message fork}
    (so : State.TransactionState.SameOutside [] state state') (h : StaticMessage state message) :
    StaticMessage state' message := by
  have acc : ∀ a, state'.getAccount a = state.getAccount a := fun a => by
    have := (so a (by simp)).1
    simp [State.TransactionState.getAccount, this]
  obtain ⟨m1, m2, m3, m4⟩ := h
  refine ⟨m1, m2, fun nonempty => ?_, fun t v => ?_⟩
  · rw [acc]; exact m3 nonempty
  · obtain ⟨c, hc⟩ := m4 t v
    exact ⟨c, by rw [acc]; exact hc⟩

/-- A change of the state by touches of absent accounts.

The storage and the transient storage of every address stay as they were.

Each touched address had no account, and holds the empty account after. -/
def TouchesOnly (touched : List Address) (before after : TransactionState) : Prop :=
  TransactionState.SameOutside touched before after ∧
    (∀ address key, after.getStorage address key = before.getStorage address key) ∧
    (∀ address key,
      after.getTransientStorage address key = before.getTransientStorage address key) ∧
    ∀ address ∈ touched,
      before.getAccountOptional address = none ∧
        after.getAccountOptional address = some EMPTY_ACCOUNT

omit [GasMeter Meter] in
/-- A state that stays as it was changes by no touch. -/
theorem TouchesOnly.refl (state : TransactionState) : TouchesOnly [] state state :=
  ⟨TransactionState.SameOutside.refl _ _, fun _ _ => rfl, fun _ _ => rfl, by simp⟩

omit [GasMeter Meter] in
/-- A state that differs only by reads changes by no touch. -/
theorem TouchesOnly.of_sameOutside {before after : TransactionState}
    (h : TransactionState.SameOutside [] before after) : TouchesOnly [] before after :=
  ⟨h, fun a k => (h a (by simp)).2.1 k, fun a k => (h a (by simp)).2.2 k, by simp⟩

omit [GasMeter Meter] in
/-- Two changes by touches make one, and a second touch of an address counts once. -/
theorem TouchesOnly.trans {first second : List Address} {a b c : TransactionState}
    (hab : TouchesOnly first a b) (hbc : TouchesOnly second b c) :
    TouchesOnly (first ++ second.filter fun addr => decide (addr ∉ first)) a c := by
  refine ⟨?_, fun addr k => (hbc.2.1 addr k).trans (hab.2.1 addr k),
    fun addr k => (hbc.2.2.1 addr k).trans (hab.2.2.1 addr k), fun addr hmem => ?_⟩
  · intro addr hnot
    have hn1 : addr ∉ first := fun h1 => hnot (List.mem_append_left _ h1)
    have hn2 : addr ∉ second := fun h2 =>
      hnot (List.mem_append_right _ (List.mem_filter.mpr ⟨h2, decide_eq_true hn1⟩))
    obtain ⟨a1, s1, t1⟩ := hab.1 addr hn1
    obtain ⟨a2, s2, t2⟩ := hbc.1 addr hn2
    exact ⟨a2.trans a1, fun k => (s2 k).trans (s1 k), fun k => (t2 k).trans (t1 k)⟩
  · rcases List.mem_append.mp hmem with h1 | hex
    · obtain ⟨hanone, hbsome⟩ := hab.2.2.2 addr h1
      by_cases h2 : addr ∈ second
      · obtain ⟨hbnone, -⟩ := hbc.2.2.2 addr h2
        simp [hbnone] at hbsome
      · exact ⟨hanone, (hbc.1 addr h2).1.trans hbsome⟩
    · obtain ⟨h2, hdec⟩ := List.mem_filter.mp hex
      have hn1 : addr ∉ first := of_decide_eq_true hdec
      obtain ⟨hbnone, hcsome⟩ := hbc.2.2.2 addr h2
      exact ⟨(hab.1 addr hn1).1.symm.trans hbnone, hcsome⟩

omit [GasMeter Meter] in
/-- A change by touches keeps every account, as the empty account is the absent one. -/
theorem TouchesOnly.getAccount_eq {touched : List Address} {before after : TransactionState}
    (h : TouchesOnly touched before after) (address : Address) :
    after.getAccount address = before.getAccount address := by
  by_cases hmem : address ∈ touched
  · obtain ⟨hnone, hsome⟩ := h.2.2.2 address hmem
    simp [TransactionState.getAccount, hnone, hsome]
  · simp [TransactionState.getAccount, (h.1 address hmem).1]

omit [GasMeter Meter] in
/-- A touch of an address changes the state only when the address had no account. -/
theorem touchesOnly_touchAccount (state : TransactionState) (address : Address) :
    TouchesOnly (if state.accountExists address then [] else [address]) state
      (state.touchAccount address) := by
  unfold TransactionState.touchAccount
  split
  · exact TouchesOnly.refl state
  · rename_i hnot
    have hnone : state.getAccountOptional address = none := by
      simpa [TransactionState.accountExists, Option.isSome_iff_ne_none] using hnot
    refine ⟨?_, ?_, fun _ _ => rfl, ?_⟩
    · intro other hmem
      have hne : other ≠ address := by simpa using hmem
      exact ⟨TransactionState.getAccountOptional_setAccount_of_ne _ _ hne,
        fun _ => by simp, fun _ => rfl⟩
    · intro _ _
      simp
    · intro other hmem
      simp only [List.mem_singleton] at hmem
      subst hmem
      exact ⟨hnone, TransactionState.getAccountOptional_setAccount_self _ _ _⟩

omit [GasMeter Meter] in
/-- The state at the start of a message changes by the touch of its target, before Paris.

From Paris, it changes by no touch. -/
theorem touchesOnly_startState (message : Message fork) (state : TransactionState) :
    ∃ touched, TouchesOnly touched state (startState fork message state) ∧
      (startState fork message state).parent = state.parent ∧
      ∀ address ∈ touched, fork < .paris ∧ address = message.currentTarget := by
  unfold startState
  split
  · rename_i hlt
    refine ⟨_, touchesOnly_touchAccount state message.currentTarget,
      TransactionState.parent_touchAccount state message.currentTarget, ?_⟩
    intro address hmem
    split at hmem
    · cases hmem
    · simp only [List.mem_singleton] at hmem
      exact ⟨hlt, hmem⟩
  · exact ⟨[], TouchesOnly.refl state, rfl, by simp⟩

omit [GasMeter Meter] in
/-- A message that a state may send, from a state that differs from it by touches. -/
theorem StaticMessage.of_touchesOnly {touched : List Address} {before after : TransactionState}
    {message : Message fork} (h : TouchesOnly touched before after)
    (hmsg : StaticMessage before message) : StaticMessage after message := by
  obtain ⟨m1, m2, m3, m4⟩ := hmsg
  refine ⟨m1, m2, fun nonempty => ?_, fun t v => ?_⟩
  · rw [h.getAccount_eq]
    exact m3 nonempty
  · obtain ⟨c, hc⟩ := m4 t v
    exact ⟨c, by rw [h.getAccount_eq]; exact hc⟩

/-- A message in a static frame leaves the state as it was, up to the records of its reads.

It also keeps the block of the state.

It is the induction on the gas of the message that the theorem below states for one message. -/
theorem processMessage_static [LawfulGasMeter Meter] (hfork : .paris ≤ fork) :
    ∀ (n : Nat) (message : Message fork) (state : State.TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas),
      message.gas = n → StaticMessage state message →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
        State.TransactionState.SameOutside [] state ended.val.state ∧
          ended.val.state.parent = state.parent := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro message state substate meter held hn hmsg ended h
    rw [processMessage] at h
    obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
    simp only [startState, show ¬fork < Fork.paris from Nat.not_lt.mpr hfork, ite_false] at hdo
    split at hdo
    all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
    all_goals
      have hS1 : State.TransactionState.SameOutside [] state state1 ∧
          state1.parent = state.parent ∧ StaticMessage state1 message := by
        first
        | (have ht := ‹message.shouldTransferValue = true ∧ message.value ≠ 0›
           have hm' := Base.mapError_ok_iff.mp hm
           obtain ⟨hcaller, hcode⟩ := hmsg.2.2.2 ht.1 ht.2
           rw [hcaller] at hm'
           have so := State.TransactionState.sameOutside_moveEther_self hcode hm'
           exact ⟨so, State.TransactionState.parent_moveEther hm',
             StaticMessage.of_sameOutside so hmsg⟩)
        | (cases hm
           exact ⟨State.TransactionState.SameOutside.refl _ _, rfl, hmsg⟩)
    all_goals
      obtain ⟨hso, hpar, hmsg1⟩ := hS1
      have core : State.TransactionState.SameOutside [] state ended0.val.state ∧
          ended0.val.state.parent = state.parent := by
        have conclude : State.TransactionState.SameOutside [] state1 ended0.val.state →
            ended0.val.state.parent = state1.parent →
            State.TransactionState.SameOutside [] state ended0.val.state ∧
              ended0.val.state.parent = state.parent :=
          fun so par => ⟨hso.trans so, par.trans hpar⟩
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            have hst := staticStep_runFrame (hf := StaticFrame.start hmsg1 _ _) (h := hrun)
              (fun {evm' after'} hf' hstep =>
                staticResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
              (fun {evm' caller' message' resume'} hf' hstep =>
                staticResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
              (by
                intro caller' message' lt c used hf' hm hrun'
                split at hrun'
                · exact ih message'.gas (by omega) message' caller'.state _ _ _ rfl hm ⟨c, used⟩
                    hrun'
                · have := hm.2.1
                  simp_all)
            exact conclude hst.state hst.parent
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            exact conclude (State.TransactionState.SameOutside.refl _ _) rfl
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact conclude (staticStep_runPrecompile hrp).state
                (staticStep_runPrecompile hrp).parent
            · cases hdo
              exact conclude (State.TransactionState.SameOutside.refl _ _) rfl
      have hval := congrArg Subtype.val rolled
      simp only at hval
      rw [← hval]
      unfold rollbackOnError
      split
      · exact ⟨State.TransactionState.sameOutside_restoreTxState core.2, core.2⟩
      · exact core

/-- A static message that is a call changes no address of the state, up to the records of reads.

From Paris, the account, storage and transient storage of every address read as before.

That holds whatever its code does, however deep its calls.

The message must be static and be a call, not a creation.

Its code, when it has any, runs at an account that holds code.

A value that it sends goes to its own sender, whose account holds code.

A message with no value, as STATICCALL sends, satisfies the last condition without a premise.

Before Paris a call touches the account that it calls, so the statement does not cover it. -/
theorem processMessage_sameOutside_static [LawfulGasMeter Meter] (hfork : .paris ≤ fork)
    {message : Message fork} {state : State.TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hmsg : StaticMessage state message) {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    State.TransactionState.SameOutside [] state ended.val.state :=
  (processMessage_static hfork message.gas message state substate meter held rfl hmsg ended h).1


/-! ## Touches from Byzantium -/

/-- The second set holds every address of the first. -/
def TouchedSubset (a b : Std.ExtTreeSet Address) : Prop :=
  ∀ address, address ∈ a → address ∈ b

omit [GasMeter Meter] in
/-- A set holds every address of itself. -/
theorem TouchedSubset.refl (s : Std.ExtTreeSet Address) : TouchedSubset s s :=
  fun _ h => h

omit [GasMeter Meter] in
/-- A subset of a subset is a subset. -/
theorem TouchedSubset.trans {a b c : Std.ExtTreeSet Address}
    (hab : TouchedSubset a b) (hbc : TouchedSubset b c) : TouchedSubset a c :=
  fun addr h => hbc addr (hab addr h)

/-- A step of a static frame that changes the state by touches.

The step keeps the message, the code and the block.

It keeps every touched account of the first frame, and records each new touch. -/
structure StaticTouchStep (touched : List Address) (before after : Evm fork Meter) : Prop where
  /-- The state changes by the touches. -/
  state : TouchesOnly touched before.state after.state
  /-- The step keeps the message. -/
  message : after.message = before.message
  /-- The step keeps the code. -/
  code : after.code = before.code
  /-- The step keeps the block. -/
  parent : after.state.parent = before.state.parent
  /-- The step keeps the touched accounts of the first frame. -/
  substate : TouchedSubset before.substate.touchedAccounts after.substate.touchedAccounts
  /-- Each touch is recorded, from Spurious Dragon before Paris. -/
  recorded : ∀ address ∈ touched,
    fork < .paris ∧ (.spuriousDragon ≤ fork → address ∈ after.substate.touchedAccounts)

omit [GasMeter Meter] in
/-- A frame is a static touch step from itself, with no touch. -/
theorem StaticTouchStep.refl (evm : Evm fork Meter) : StaticTouchStep [] evm evm :=
  ⟨TouchesOnly.refl _, rfl, rfl, rfl, TouchedSubset.refl _, by simp⟩

omit [GasMeter Meter] in
/-- Two static touch steps make one, and a second touch of an address counts once. -/
theorem StaticTouchStep.trans {t1 t2 : List Address} {a b c : Evm fork Meter}
    (hab : StaticTouchStep t1 a b) (hbc : StaticTouchStep t2 b c) :
    StaticTouchStep (t1 ++ t2.filter fun addr => decide (addr ∉ t1)) a c := by
  refine ⟨TouchesOnly.trans hab.state hbc.state, hbc.message.trans hab.message,
    hbc.code.trans hab.code, hbc.parent.trans hab.parent,
    hab.substate.trans hbc.substate, fun addr hmem => ?_⟩
  rcases List.mem_append.mp hmem with h1 | hex
  · obtain ⟨hlt, hrec⟩ := hab.recorded addr h1
    exact ⟨hlt, fun hsd => hbc.substate addr (hrec hsd)⟩
  · exact hbc.recorded addr (List.mem_filter.mp hex).1

omit [GasMeter Meter] in
/-- A step that keeps the whole context is a static touch step, with no touch. -/
theorem StaticTouchStep.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) :
    StaticTouchStep [] a b :=
  ⟨by rw [h.state]; exact TouchesOnly.refl _, h.message, h.code, by rw [h.state],
    fun addr ha => by rw [h.substate]; exact ha, by simp⟩

omit [GasMeter Meter] in
/-- A static step that keeps the touched accounts is a static touch step, with no touch. -/
theorem StaticTouchStep.of_staticKeep {a b : Evm fork Meter} (h : StaticStep a b)
    (ht : b.substate.touchedAccounts = a.substate.touchedAccounts) : StaticTouchStep [] a b :=
  ⟨TouchesOnly.of_sameOutside h.state, h.message, h.code, h.parent,
    fun addr ha => by rw [ht]; exact ha, by simp⟩

omit [GasMeter Meter] in
/-- The touched accounts of a frame stay touched when a failed child ends. -/
theorem subset_touchedOnError (caller child : Evm fork Meter) :
    TouchedSubset caller.substate.touchedAccounts (touchedOnError fork caller child) := by
  intro address h
  unfold touchedOnError
  split
  · exact Std.ExtTreeSet.mem_insert.mpr (Or.inr h)
  · exact h

omit [GasMeter Meter] in
/-- The touched accounts after a child succeeds hold those of the caller and of the child.

From Spurious Dragon before Paris, they also hold the target of the child when that is empty. -/
theorem mem_touchedOnSuccess (caller child : Evm fork Meter) {address : Address}
    (h : address ∈ caller.substate.touchedAccounts ∨
      (.spuriousDragon ≤ fork ∧ fork < .paris ∧
        (address ∈ child.substate.touchedAccounts ∨
          (child.state.accountExistsAndIsEmpty child.message.currentTarget = true ∧
            address = child.message.currentTarget)))) :
    address ∈ touchedOnSuccess fork caller child := by
  unfold touchedOnSuccess
  split
  · rename_i hfork
    rcases h with hc | ⟨-, -, hchild | ⟨hempty, rfl⟩⟩
    · split
      · exact Std.ExtTreeSet.mem_insert.mpr
          (Or.inr (Std.ExtTreeSet.mem_insertMany_list.mpr (Or.inl hc)))
      · exact Std.ExtTreeSet.mem_insertMany_list.mpr (Or.inl hc)
    · have hm : child.substate.touchedAccounts.toList.contains address = true :=
        List.contains_iff_mem.mpr (Std.ExtTreeSet.mem_toList.mpr hchild)
      split
      · exact Std.ExtTreeSet.mem_insert.mpr
          (Or.inr (Std.ExtTreeSet.mem_insertMany_list.mpr (Or.inr hm)))
      · exact Std.ExtTreeSet.mem_insertMany_list.mpr (Or.inr hm)
    · simp [hempty, Std.ExtTreeSet.mem_insert]
  · rename_i hfork
    rcases h with hc | ⟨h1, h2, -⟩
    · exact hc
    · exact absurd ⟨h1, h2⟩ hfork

/-- The touched accounts of a caller stay touched after its child ends. -/
theorem subset_incorporateChild (caller child : Evm fork Meter) :
    TouchedSubset caller.substate.touchedAccounts
      (incorporateChild fork caller child).substate.touchedAccounts := by
  intro address h
  unfold incorporateChild
  split
  · exact mem_touchedOnSuccess caller child (Or.inl h)
  · exact subset_touchedOnError caller child address h

omit [GasMeter Meter] in
/-- An account exists and is empty if and only if its optional account is the empty account. -/
theorem accountExistsAndIsEmpty_iff_eq_some (state : TransactionState) (address : Address) :
    state.accountExistsAndIsEmpty address = true ↔
      state.getAccountOptional address = some EMPTY_ACCOUNT := by
  unfold TransactionState.accountExistsAndIsEmpty
  cases h : state.getAccountOptional address with
  | none => simp
  | some acc =>
    cases acc
    simp [EMPTY_ACCOUNT, Bool.and_eq_true, decide_eq_true_eq, and_assoc, and_comm]

/-- A caller that resumes after a static child changes by the touches of that child. -/
theorem staticTouchStep_resumeCall {caller child after : Evm fork Meter} {touched : List Address}
    {newAccount : Nat} {outputStart outputSize : U256}
    (h : resumeCall fork caller newAccount outputStart outputSize child = .ok after)
    (kept : TouchesOnly touched caller.state child.state)
    (parent : child.state.parent = caller.state.parent)
    (hrec : ∀ address ∈ touched, child.error = none ∧ fork < .paris ∧
      ((.spuriousDragon ≤ fork → address ∈ child.substate.touchedAccounts) ∨
        address = child.message.currentTarget)) :
    StaticTouchStep touched caller after := by
  obtain ⟨e, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have hp := pushWord_sameContext h1
  have hs : e.state = child.state := by
    rw [hp.state]; split <;> simp [state_incorporateChild, refillStateGas]
  have hm : e.message = caller.message := by
    rw [hp.message]; split <;> simp [message_incorporateChild, refillStateGas]
  have hc : e.code = caller.code := by
    rw [hp.code]; split <;> simp [code_incorporateChild, refillStateGas]
  have htouch : e.substate.touchedAccounts =
      (incorporateChild fork caller child).substate.touchedAccounts := by
    rw [hp.substate]; split <;> rfl
  refine ⟨?_, hm, hc, ?_, ?_, ?_⟩
  · show TouchesOnly touched caller.state e.state
    rw [hs]; exact kept
  · show e.state.parent = caller.state.parent
    rw [hs]; exact parent
  · intro address ha
    show address ∈ e.substate.touchedAccounts
    rw [htouch]
    exact subset_incorporateChild caller child address ha
  · intro address ha
    obtain ⟨herr, hlt, hmem⟩ := hrec address ha
    refine ⟨hlt, fun hsd => ?_⟩
    show address ∈ e.substate.touchedAccounts
    rw [htouch]
    unfold incorporateChild
    simp only [herr, Option.isNone_none, ↓reduceIte]
    refine mem_touchedOnSuccess caller child (Or.inr ⟨hsd, hlt, ?_⟩)
    rcases hmem with hsub | rfl
    · exact Or.inl (hsub hsd)
    · right
      exact ⟨(accountExistsAndIsEmpty_iff_eq_some child.state _).mpr (kept.2.2.2 _ ha).2, rfl⟩

/-- A static step that also keeps the touched accounts of the substate. -/
structure StaticKeepStep (before after : Evm fork Meter) : Prop
    extends StaticStep before after where
  /-- The step keeps the touched accounts. -/
  touched : after.substate.touchedAccounts = before.substate.touchedAccounts

omit [GasMeter Meter] in
/-- A frame keeps its own state and touched accounts. -/
theorem StaticKeepStep.refl (evm : Evm fork Meter) : StaticKeepStep evm evm :=
  ⟨StaticStep.refl _, rfl⟩

omit [GasMeter Meter] in
/-- Two steps that keep the state and touched accounts keep them together. -/
theorem StaticKeepStep.trans {a b c : Evm fork Meter}
    (hab : StaticKeepStep a b) (hbc : StaticKeepStep b c) : StaticKeepStep a c :=
  ⟨hab.toStaticStep.trans hbc.toStaticStep, hbc.touched.trans hab.touched⟩

omit [GasMeter Meter] in
/-- A step that keeps the context keeps the state and touched accounts. -/
theorem StaticKeepStep.of_sameContext {a b : Evm fork Meter} (h : SameContext a b) :
    StaticKeepStep a b :=
  ⟨StaticStep.of_sameContext h, by rw [h.substate]⟩

omit [GasMeter Meter] in
/-- Setting the memory keeps the state and touched accounts. -/
theorem StaticKeepStep.withMemory (evm : Evm fork Meter) (memory : ByteArray) :
    StaticKeepStep evm { evm with memory } := ⟨StaticStep.withMemory _ _, rfl⟩

omit [GasMeter Meter] in
/-- Advancing the program counter keeps the state and touched accounts. -/
theorem StaticKeepStep.advance {a b : Evm fork Meter} (h : StaticKeepStep a b) (n : Nat := 1) :
    StaticKeepStep a (advance b n) := ⟨h.toStaticStep.advance n, h.touched⟩

omit [GasMeter Meter] in
/-- A step that keeps the state and touched accounts is a static touch step, with no touch. -/
theorem StaticKeepStep.toTouchStep {a b : Evm fork Meter} (h : StaticKeepStep a b) :
    StaticTouchStep [] a b :=
  StaticTouchStep.of_staticKeep h.toStaticStep h.touched

omit [GasMeter Meter] in
/-- A step that keeps the state and touched accounts before a touch step keeps its touches. -/
theorem StaticKeepStep.transTouch {touched : List Address} {a b c : Evm fork Meter}
    (hab : StaticKeepStep a b) (hbc : StaticTouchStep touched b c) :
    StaticTouchStep touched a c := by
  have ht := hab.toTouchStep.trans hbc
  have hf : ∀ l : List Address, (l.filter fun addr => decide (addr ∉ ([] : List Address))) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.filter_cons, ih]
      rfl
  rwa [List.nil_append, hf] at ht

omit [GasMeter Meter] in
/-- Recording a read of an account keeps the state and touched accounts. -/
theorem staticKeepStep_recordAccountRead (evm : Evm fork Meter) (address : Address) :
    StaticKeepStep evm (recordAccountRead evm address) :=
  ⟨staticStep_recordAccountRead evm address, rfl⟩

omit [GasMeter Meter] in
/-- Recording a read of a storage slot keeps the state and touched accounts. -/
theorem staticKeepStep_recordStorageRead (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) : StaticKeepStep evm (recordStorageRead evm address key) :=
  ⟨staticStep_recordStorageRead evm address key, rfl⟩

omit [GasMeter Meter] in
/-- An access to an address keeps the state and touched accounts. -/
theorem staticKeepStep_accessAddress (evm : Evm fork Meter) (address : Address) :
    StaticKeepStep evm (accessAddress evm address).2 := by
  obtain ⟨_, h⟩ := accessAddress_snd evm address
  exact ⟨staticStep_accessAddress evm address, by rw [h]⟩

omit [GasMeter Meter] in
/-- An access to a storage key keeps the state and touched accounts. -/
theorem staticKeepStep_accessStorageKey (evm : Evm fork Meter) (address : Address)
    (key : Bytes32) : StaticKeepStep evm (accessStorageKey evm address key).2 := by
  obtain ⟨_, h⟩ := accessStorageKey_snd evm address key
  exact ⟨staticStep_accessStorageKey evm address key, by rw [h]⟩

/-- An exceptional halt keeps the state and touched accounts. -/
theorem staticKeepStep_exceptionalHalt (evm : Evm fork Meter) (e : EvmError) :
    StaticKeepStep evm (exceptionalHalt evm e) := ⟨staticStep_exceptionalHalt evm e, rfl⟩

/-- A precompile keeps the state and touched accounts. -/
theorem staticKeepStep_runPrecompile {address : Nat} {evm after : Evm fork Meter}
    (h : runPrecompile fork address evm = some after) : StaticKeepStep evm after := by
  unfold runPrecompile at h
  split at h
  · cases h
  · cases h
    exact staticKeepStep_exceptionalHalt _ _
  · split at h
    · cases h
      exact staticKeepStep_exceptionalHalt _ _
    · cases h
      exact ⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩

/-- BALANCE keeps the state and touched accounts. -/
theorem staticKeepStep_balanceStep {evm after : Evm fork Meter}
    (h : balanceStep evm = .ok after) : StaticKeepStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticKeepStep e1 e2 := by
    have := staticKeepStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticKeepStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticKeepStep_recordAccountRead _ _)).trans
    (StaticKeepStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODESIZE keeps the state and touched accounts. -/
theorem staticKeepStep_extcodesizeStep {evm after : Evm fork Meter}
    (h : extcodesizeStep evm = .ok after) : StaticKeepStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticKeepStep e1 e2 := by
    have := staticKeepStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticKeepStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticKeepStep_recordAccountRead _ _)).trans
    (StaticKeepStep.of_sameContext (pushWord_sameContext h5)) |>.advance

/-- EXTCODEHASH keeps the state and touched accounts. -/
theorem staticKeepStep_extcodehashStep {evm after : Evm fork Meter}
    (h : extcodehashStep evm = .ok after) : StaticKeepStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticKeepStep e1 e2 := by
    have := staticKeepStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  exact ((((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticKeepStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticKeepStep_recordAccountRead _ _)).trans
    (StaticKeepStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- EXTCODECOPY keeps the state and touched accounts. -/
theorem staticKeepStep_extcodecopyStep {evm after : Evm fork Meter}
    (h : extcodecopyStep evm = .ok after) : StaticKeepStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨st, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨off, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨sz, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  rcases hacc : accessAddress e4 (toAddressMasked w) with ⟨cold, e5⟩
  simp only [hacc] at h
  obtain ⟨e6, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨code, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticKeepStep e4 e5 := by
    have := staticKeepStep_accessAddress e4 (toAddressMasked w)
    rwa [hacc] at this
  exact (((((((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h2))).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h3))).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h4))).trans ha).trans
    (StaticKeepStep.of_sameContext (chargeGasAndMemory_sameContext h6))).trans
    (staticKeepStep_recordAccountRead _ _)).trans (StaticKeepStep.withMemory _ _) |>.advance

/-- Each instruction of account data keeps the state and touched accounts. -/
theorem staticKeepStep_accountStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : accountStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : StaticKeepStep evm after := by
  cases op <;> simp only [accountStep, Option.some.injEq, reduceCtorEq] at hstep
  case balance => subst hstep; exact staticKeepStep_balanceStep h
  case extcodesize => subst hstep; exact staticKeepStep_extcodesizeStep h
  case extcodecopy => subst hstep; exact staticKeepStep_extcodecopyStep h
  case selfbalance =>
    split at hstep
    · cases hstep
      exact (staticKeepStep_recordAccountRead _ _).trans
        (StaticKeepStep.of_sameContext (readFrame_sameContext h))
    · cases hstep
  case extcodehash =>
    split at hstep
    · cases hstep; exact staticKeepStep_extcodehashStep h
    · cases hstep

/-- SLOAD keeps the state and touched accounts. -/
theorem staticKeepStep_sloadStep {evm after : Evm fork Meter} (h : sloadStep evm = .ok after) :
    StaticKeepStep evm after := by
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w) with ⟨cold, e2⟩
  simp only [hacc] at h
  obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have ha : StaticKeepStep e1 e2 := by
    have := staticKeepStep_accessStorageKey e1 e1.message.currentTarget (U256.toBeBytes w)
    rwa [hacc] at this
  exact ((((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (StaticKeepStep.of_sameContext (chargeGas_sameContext h3))).trans
    (staticKeepStep_recordStorageRead _ _ _)).trans
    (StaticKeepStep.of_sameContext (pushWord_sameContext h4)) |>.advance

/-- SSTORE in a static frame keeps the state and touched accounts. -/
theorem staticKeepStep_sstoreStep_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : sstoreStep evm = .ok after) :
    StaticKeepStep evm after := by
  unfold sstoreStep at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  obtain ⟨⟨k, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨n, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  have c2 := (StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h2))
  have m2 : e2.message = evm.message := c2.message
  simp only [] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨keys, hacc⟩ := accessStorageKey_snd e2 e2.message.currentTarget (U256.toBeBytes k)
      rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      rw [hpair] at hacc
      simp only [hpair] at h
      obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
      have m5 : e5.message = evm.message := by
        obtain ⟨_, -, h5⟩ := Base.bind_ok_iff.mp h5
        cases h5
        rw [(chargeGas_sameContext h4).message]
        cases hacc
        exact m2
      simp [m5, static, throw, throwThe, MonadExceptOf.throw] at h
    · rcases hpair : accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k) with
        ⟨cold, e3⟩
      have ha : StaticKeepStep e2 e3 := by
        have := staticKeepStep_accessStorageKey e2 e2.message.currentTarget (U256.toBeBytes k)
        rwa [hpair] at this
      exact ((c2.trans ha).trans (staticKeepStep_recordStorageRead _ _ _)).trans
        (staticKeepStep_exceptionalHalt _ _)

/-- Each instruction of storage in a static frame keeps the state and touched accounts. -/
theorem staticKeepStep_storageStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : storageStep op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) :
    StaticKeepStep evm after := by
  cases op <;> simp only [storageStep, Option.some.injEq, reduceCtorEq] at hstep
  case sload => subst hstep; exact staticKeepStep_sloadStep h
  case sstore => subst hstep; exact staticKeepStep_sstoreStep_of_isStatic static h

/-- SELFDESTRUCT in a static frame keeps the state and touched accounts. -/
theorem staticKeepStep_selfdestructStep_of_isStatic {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : selfdestructStep fork evm = .ok after) :
    StaticKeepStep evm after := by
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨w, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  rcases hacc : accessAddress e1 (toAddressMasked w) with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticKeepStep e1 e2 := by
    have := staticKeepStep_accessAddress e1 (toAddressMasked w)
    rwa [hacc] at this
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  have c := ((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans ha).trans
    (staticKeepStep_recordAccountRead e2 (toAddressMasked w))
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e4, h4, h⟩ := Base.bind_ok_iff.mp h
    have m4 : e4.message = evm.message := by
      rw [(chargeStateGas_sameContext h4).message, (chargeGas_sameContext h3).message]
      exact c.message
    unfold finishSelfdestruct at h
    simp [m4, static] at h
  · exact c.trans (staticKeepStep_exceptionalHalt _ _)

/-- Each instruction of transient storage in a static frame keeps the state and touched accounts. -/
theorem staticKeepStep_transientStorageStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : transientStorageStep fork op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) :
    StaticKeepStep evm after := by
  cases op <;> simp only [transientStorageStep, reduceCtorEq] at hstep <;> split at hstep <;>
    simp only [Option.some.injEq, reduceCtorEq] at hstep <;> subst hstep
  case tload => exact StaticKeepStep.of_sameContext (tloadStep_sameContext h)
  case tstore => exact absurd h (tstoreStep_ne_ok_of_isStatic static)

/-- RETURN and REVERT keep the state and touched accounts. -/
theorem staticKeepStep_returnOpStep {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : returnOpStep fork op = some step) {evm after : Evm fork Meter}
    (h : step evm = .ok after) : StaticKeepStep evm after := by
  cases op <;> simp only [returnOpStep, Option.some.injEq, reduceCtorEq] at hstep
  case «return» => subst hstep; exact StaticKeepStep.of_sameContext (returnStep_sameContext h)
  case revert =>
    split at hstep
    · cases hstep; exact StaticKeepStep.of_sameContext (revertStep_sameContext h)
    · cases hstep

/-- The instruction of SELFDESTRUCT in a static frame keeps the state and touched accounts. -/
theorem staticKeepStep_selfdestructOpStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : selfdestructOpStep fork op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) :
    StaticKeepStep evm after := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact staticKeepStep_selfdestructStep_of_isStatic static h

/-- The instructions of LOG in a static frame keep the state and touched accounts. -/
theorem staticKeepStep_logOpStep_of_isStatic {op : Op}
    {step : Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hstep : logOpStep op = some step) {evm after : Evm fork Meter}
    (static : evm.message.isStatic = true) (h : step evm = .ok after) :
    StaticKeepStep evm after := by
  cases op <;> simp only [logOpStep, Option.some.injEq, reduceCtorEq] at hstep
  subst hstep
  exact absurd h (logStep_ne_ok_of_isStatic static)

/-- Each instruction that gives the next frame keeps the state and touched accounts. -/
theorem staticKeepStep_instruction_of_isStatic {op : Op}
    {run : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hrun : instruction fork op = some run) (static : evm.message.isStatic = true)
    (h : run evm = .ok after) : StaticKeepStep evm after := by
  unfold instruction at hrun
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticKeepStep.of_sameContext (stackOnlyStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticKeepStep.of_sameContext (controlFlowStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticKeepStep.of_sameContext (memoryDataStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticKeepStep_returnOpStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact StaticKeepStep.of_sameContext (environmentStep_sameContext hf h)
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticKeepStep_accountStep hf h
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticKeepStep_storageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hrun
  · exact staticKeepStep_transientStorageStep_of_isStatic hf static h
  rcases orElse_eq_some hrun with hf | hf
  · exact staticKeepStep_logOpStep_of_isStatic hf static h
  · exact staticKeepStep_selfdestructOpStep_of_isStatic hf static h

omit [GasMeter Meter] in
/-- The pops of the operands of a call keep the state and touched accounts. -/
theorem staticKeepStep_popCallOperands {kind : CallKind} {evm after : Evm fork Meter}
    {call : CallOperands} (h : popCallOperands kind evm = .ok (call, after)) :
    StaticKeepStep evm after ∧ (kind.sendsValue = false → call.value = 0) := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨v, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e6⟩, h6, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e7⟩, h7, h⟩ := Base.bind_ok_iff.mp h
  cases h
  have p3 : StaticKeepStep e2 e3 ∧ (kind.sendsValue = false → v = 0) := by
    unfold popCallValue at h3
    split at h3
    · exact ⟨StaticKeepStep.of_sameContext (popWord_sameContext h3), fun h => by simp_all⟩
    · cases h3
      exact ⟨StaticKeepStep.refl _, fun _ => rfl⟩
  refine ⟨?_, p3.2⟩
  exact (((((((StaticKeepStep.of_sameContext (popWord_sameContext h1)).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h2))).trans p3.1).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h4))).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h5))).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h6))).trans
    (StaticKeepStep.of_sameContext (popWord_sameContext h7)))

/-- The access to a delegate keeps the state and touched accounts. -/
theorem staticKeepStep_accessDelegation {evm after : Evm fork Meter} {address : Address}
    {known : Nat} {callee : Callee}
    (h : accessDelegation evm address known = .ok (callee, after)) :
    StaticKeepStep evm after := by
  obtain ⟨code, -, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  split at h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact (staticKeepStep_accessAddress _ _).trans (staticKeepStep_recordAccountRead _ _)
  · cases h
    exact StaticKeepStep.refl _

/-- The payment of a call keeps the state and touched accounts. -/
theorem staticKeepStep_payCall {kind : CallKind} {call : CallOperands}
    {memoryCost extraGas newAccount subCall : Nat} {evm after : Evm fork Meter}
    (h : payCall kind call memoryCost extraGas newAccount evm = .ok (subCall, after)) :
    StaticKeepStep evm after := by
  unfold payCall at h
  split at h
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact ((StaticKeepStep.of_sameContext (chargeGas_sameContext h1)).trans
      (StaticKeepStep.of_sameContext (chargeStateGas_sameContext h2))).trans
      (StaticKeepStep.of_sameContext (chargeGas_sameContext h3))
  · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact StaticKeepStep.of_sameContext (chargeGas_sameContext h1)

/-- A call that runs no message keeps the state and touched accounts. -/
theorem staticKeepStep_skipCall {evm after : Evm fork Meter} {gas reservoir : Nat}
    (h : skipCall evm gas reservoir = .ok after) : StaticKeepStep evm after := by
  obtain ⟨stack, -, rfl⟩ := skipCall_eq_ok h
  exact ⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩

omit [GasMeter Meter] in
/-- A static touch step from a static frame ends in a static frame. -/
theorem StaticFrame.of_touchStep {touched : List Address} {a b : Evm fork Meter}
    (h : StaticTouchStep touched a b) (f : StaticFrame a) : StaticFrame b := by
  obtain ⟨hs, hc, hh⟩ := f
  refine ⟨by rw [h.message]; exact hs, by rw [h.code, h.message]; exact hc, ?_⟩
  intro nonempty
  rw [h.message] at nonempty ⊢
  rw [h.state.getAccount_eq]
  exact hh nonempty

/-- The child of a step of a static frame, when calls may touch accounts. -/
def StaticTouchChild (evm caller : Evm fork Meter) (message : Message fork)
    (resume : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  StaticKeepStep evm caller ∧ StaticMessage caller.state message ∧
    ∀ touched child after, resume child = .ok after → TouchesOnly touched caller.state child.state →
      child.state.parent = caller.state.parent →
      (∀ address ∈ touched, child.error = none ∧ fork < .paris ∧
        ((.spuriousDragon ≤ fork → address ∈ child.substate.touchedAccounts) ∨
          address = child.message.currentTarget)) →
      StaticTouchStep touched evm after

/-- What a step of a static frame gives when calls may touch accounts. -/
def StaticTouchResult (evm : Evm fork Meter) : StepResult fork Meter → Prop
  | .next after => StaticKeepStep evm after
  | .child caller message resume => StaticTouchChild evm caller message resume

omit [GasMeter Meter] in
/-- A frame reached by a step that keeps state and touched accounts gives the same result. -/
theorem StaticTouchResult.lift {evm evm' : Evm fork Meter} {result : StepResult fork Meter}
    (h : StaticKeepStep evm evm') (r : StaticTouchResult evm' result) :
    StaticTouchResult evm result := by
  cases result with
  | next after => exact h.trans r
  | child caller message resume =>
    obtain ⟨c, m, m4⟩ := r
    refine ⟨h.trans c, m, fun touched child after hres kept parent hrec =>
      h.transTouch (m4 touched child after hres kept parent hrec)⟩

/-- A call that has paid gives a step that keeps state, or a static touch child. -/
theorem staticTouchResult_genericCall {evm : Evm fork Meter} {message : Message fork}
    {newAccount : Nat} {outputStart outputSize : U256} {result : StepResult fork Meter}
    (hmsg : StaticMessage evm.state message)
    (h : genericCall evm message newAccount outputStart outputSize = .ok result) :
    StaticTouchResult evm result := by
  unfold genericCall at h
  dsimp only at h
  split at h
  · cases hs : skipCall (refillStateGas { evm with returnData := .empty } newAccount)
        message.gas message.reservoir with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact (⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩ : StaticKeepStep evm
        (refillStateGas { evm with returnData := .empty } newAccount)).trans
        (staticKeepStep_skipCall hs)
  · cases h
    refine ⟨⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩, hmsg, ?_⟩
    intro touched child after hres kept parent hrec
    have pre : StaticKeepStep evm { evm with returnData := .empty } :=
      ⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩
    exact pre.transTouch (staticTouchStep_resumeCall hres kept parent hrec)

/-- A call in a static frame that has paid gives a step that keeps state, or a static touch child.
-/
theorem staticTouchResult_finishCall {kind : CallKind} {call : CallOperands} {callee : Callee}
    {subCall newAccount expandBy : Nat} {evm : Evm fork Meter} {result : StepResult fork Meter}
    (static : evm.message.isStatic = true) (hv : kind.sendsValue = false → call.value = 0)
    (self : (evm.state.getAccount evm.message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (hcallee : callee.code.size ≠ 0 →
      (evm.state.getAccount call.address).codeHash ≠ EMPTY_CODE_HASH)
    (h : finishCall kind call callee subCall newAccount expandBy evm = .ok result) :
    StaticTouchResult evm result := by
  unfold finishCall at h
  split at h
  · cases h
  rename_i hnot
  dsimp only at h
  have pre : StaticKeepStep evm (recordAccountRead { evm with
      memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
      evm.message.currentTarget) := ⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩
  split at h
  · cases hs : skipCall (refillStateGas (recordAccountRead { evm with
        memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
        evm.message.currentTarget) newAccount) subCall (GasMeter.reservoir evm.gas) with
    | error e => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      have refill : StaticKeepStep (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget)
          (refillStateGas (recordAccountRead { evm with
          memory := memoryExtend evm.memory expandBy, gas := GasMeter.drain evm.gas }
          evm.message.currentTarget) newAccount) := ⟨⟨StateKept.refl _, rfl, rfl, rfl⟩, rfl⟩
      exact (pre.trans refill).trans (staticKeepStep_skipCall hs)
  · refine StaticTouchResult.lift pre (staticTouchResult_genericCall ?_ h)
    have hcall : kind = .call → call.value = 0 := by
      intro hk
      exact Decidable.byContradiction fun hne => hnot ⟨hk, static, hne⟩
    refine ⟨?_, rfl, ?_, ?_⟩
    · simp only [Bool.or_eq_true, beq_iff_eq]
      exact Or.inr static
    · intro nonempty
      cases kind
      · exact hcallee nonempty
      · exact self
      · exact self
      · exact hcallee nonempty
    · intro htransfer hvalue
      cases kind
      · exact absurd (hcall rfl) (by simpa using hvalue)
      · exact ⟨rfl, self⟩
      · simp at htransfer
      · exact absurd (hv rfl) (by simpa using hvalue)

/-- Each call in a static frame gives a step that keeps state, or a static touch child. -/
theorem staticTouchResult_callStep {kind : CallKind} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (static : evm.message.isStatic = true)
    (self : (evm.state.getAccount evm.message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (h : callStep kind evm = .ok result) : StaticTouchResult evm result := by
  unfold callStep at h
  obtain ⟨⟨call, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨c1, hv⟩ := staticKeepStep_popCallOperands h1
  dsimp only at h
  split at h
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    cases h
  rcases hacc : accessAddress e1 call.address with ⟨cold, e2⟩
  simp only [hacc] at h
  have ha : StaticKeepStep e1 e2 := by
    have := staticKeepStep_accessAddress e1 call.address
    rwa [hacc] at this
  have s3 : StaticKeepStep evm (recordAccountRead e2 call.address) :=
    (c1.trans ha).trans (staticKeepStep_recordAccountRead e2 call.address)
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨⟨callee, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
    have s4 : StaticKeepStep evm e4 := s3.trans (staticKeepStep_accessDelegation h4)
    dsimp only at h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨⟨subCall, e5⟩, h5, h⟩ := Base.bind_ok_iff.mp h
      have s5 : StaticKeepStep evm e5 := s4.trans (staticKeepStep_payCall h5)
      refine StaticTouchResult.lift s5
        (staticTouchResult_finishCall (by rw [s5.message]; exact static) hv ?_ ?_ h)
      · rw [getAccount_of_staticStep s5.toStaticStep, s5.message]
        exact self
      · intro nonempty
        have := accessDelegation_codeHash_ne h4 nonempty
        rw [getAccount_of_staticStep ((staticKeepStep_accessDelegation h4).trans
          (staticKeepStep_payCall h5)).toStaticStep call.address]
        exact this
    · exact s4.trans (staticKeepStep_exceptionalHalt _ _)
  · exact s3.trans (staticKeepStep_exceptionalHalt _ _)

/-- Each instruction that may send a message gives a keep step or a static touch child. -/
theorem staticTouchResult_messageInstruction {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (static : evm.message.isStatic = true)
    (self : (evm.state.getAccount evm.message.currentTarget).codeHash ≠ EMPTY_CODE_HASH)
    (h : run evm = .ok result) : StaticTouchResult evm result := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact staticTouchResult_callStep static self h)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact staticTouchResult_callStep static self h
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact absurd h (createStep_ne_ok_of_isStatic static))
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact absurd h (createStep_ne_ok_of_isStatic static)
         · cases hrun)

/-- A step of a static frame gives a keep step, or a static touch child. -/
theorem staticTouchResult_step {evm : Evm fork Meter} {result : StepResult fork Meter}
    (static : evm.message.isStatic = true) (hcode : evm.code = evm.message.code)
    (hhold : StaticCode evm.state evm.message) (h : step fork evm = .ok result) :
    StaticTouchResult evm result := by
  unfold step at h
  split at h
  · rename_i hlt
    dsimp only at h
    split at h
    · cases h
    · split at h
      · rename_i hop
        cases hr : ‹Evm fork Meter → Except EvmError (Evm fork Meter)› evm with
        | error => simp [hr, Functor.map, Except.map] at h
        | ok after =>
          simp only [hr, Functor.map, Except.map, Except.ok.injEq] at h
          subst h
          exact staticKeepStep_instruction_of_isStatic hop static hr
      · split at h
        · rename_i hcall
          refine staticTouchResult_messageInstruction hcall static (hhold ?_) h
          rw [← hcode]
          omega
        · cases h
  · simp only [stopStep, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact StaticKeepStep.of_sameContext (controlFlowStep_sameContext (op := .stop) rfl rfl)

section TouchLoop

variable {step : Evm fork Meter → Except EvmError (StepResult fork Meter)}
  {decreases : ∀ {evm result}, evm.running = true → step evm = .ok result →
    result.Decreases evm}
  {bound : Nat} {runChild : MessageRunner fork Meter bound}

/-- A whole run of a static frame is a static touch step. -/
theorem staticTouchStep_runFrame
    (next : ∀ {evm after : Evm fork Meter}, StaticFrame evm → step evm = .ok (.next after) →
      StaticKeepStep evm after)
    (child : ∀ {evm caller : Evm fork Meter} {message : Message fork}
      {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}, StaticFrame evm →
      step evm = .ok (.child caller message resume) →
      StaticTouchChild evm caller message resume)
    (runs : ∀ {caller : Evm fork Meter} {message : Message fork} {lt : message.gas < bound}
      {c : Evm fork Meter} {used : GasMeter.gasHeld c.gas ≤ message.gas},
      StaticFrame caller → StaticMessage caller.state message →
      runChild caller message lt = .ok ⟨c, used⟩ →
      ∃ touched, TouchesOnly touched caller.state c.state ∧
        c.state.parent = caller.state.parent ∧
        ∀ address ∈ touched, c.error = none ∧ fork < .paris ∧
          ((.spuriousDragon ≤ fork → address ∈ c.substate.touchedAccounts) ∨
            address = c.message.currentTarget))
    {evm after : Evm fork Meter} {within : GasMeter.gasHeld evm.gas ≤ bound}
    (hf : StaticFrame evm)
    (h : runFrame step decreases bound runChild evm within = .ok after) :
    ∃ touched, StaticTouchStep touched evm after := by
  fun_induction runFrame step decreases bound runChild evm within
  case case1 => cases h
  case case2 => cases h; exact ⟨[], (staticKeepStep_exceptionalHalt _ _).toTouchStep⟩
  case case3 =>
    rename_i result _ ih
    have n := next hf result
    obtain ⟨t, ht⟩ := ih (StaticFrame.of_staticStep n.toStaticStep hf) h
    exact ⟨_, n.toTouchStep.trans ht⟩
  case case4 => cases h
  case case5 => cases h
  case case6 => cases h; exact ⟨[], (staticKeepStep_exceptionalHalt _ _).toTouchStep⟩
  case case7 =>
    obtain ⟨c0, hmsg, hres⟩ := child hf ‹step _ = .ok (.child _ _ _)›
    obtain ⟨tc, kept, parent, hrec⟩ :=
      runs (StaticFrame.of_staticStep c0.toStaticStep hf) hmsg ‹runChild _ _ _ = .ok _›
    have n := hres tc _ _ (by assumption) kept parent hrec
    obtain ⟨tr, htr⟩ :=
      ‹StaticFrame _ → runFrame _ _ _ _ _ _ = .ok after → ∃ t, StaticTouchStep t _ after›
        (StaticFrame.of_touchStep n hf) h
    exact ⟨_, n.trans htr⟩
  case case8 => cases h; exact ⟨[], StaticTouchStep.refl _⟩

end TouchLoop

/-- A static message changes the state by touches, and keeps the block.

It is the induction on the gas of the message that the theorem below states for one message. -/
theorem processMessage_touchesOnly_static [LawfulGasMeter Meter] :
    ∀ (n : Nat) (message : Message fork) (state : TransactionState) (substate : Substate)
      (meter : Meter) (held : GasMeter.gasHeld meter ≤ message.gas),
      message.gas = n → StaticMessage state message →
      ∀ ended, processMessage fork message state substate meter held = .ok ended →
      ∃ touched, TouchesOnly touched state ended.val.state ∧
        ended.val.state.parent = state.parent ∧
        ended.val.message = message ∧
        ∀ address ∈ touched, ended.val.error = none ∧ fork < .paris ∧
          ((.spuriousDragon ≤ fork → address ∈ ended.val.substate.touchedAccounts) ∨
            address = message.currentTarget) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro message state substate meter held hn hmsg ended h
    rw [processMessage] at h
    obtain ⟨ended0, hdo, rolled⟩ := Base.map_ok_iff.mp h
    obtain ⟨t0, ht0, hpar0, hrec0⟩ := touchesOnly_startState message state
    have hmsg0 : StaticMessage (startState fork message state) message :=
      StaticMessage.of_touchesOnly ht0 hmsg
    have stepCore : ∀ {state1 : TransactionState} {substate1 : Substate} {t2 : List Address},
        TouchesOnly t0 state state1 → state1.parent = state.parent →
        StaticTouchStep t2 (startFrame message state1 substate1 meter) ended0.val →
        ∃ t, TouchesOnly t state ended0.val.state ∧ ended0.val.state.parent = state.parent ∧
          ended0.val.message = message ∧
          ∀ address ∈ t, fork < .paris ∧
            ((.spuriousDragon ≤ fork → address ∈ ended0.val.substate.touchedAccounts) ∨
              address = message.currentTarget) := by
      intro state1 substate1 t2 h1 hp1 ht2
      refine ⟨_, h1.trans ht2.state, ht2.parent.trans hp1, ht2.message, ?_⟩
      intro address hmem
      rcases List.mem_append.mp hmem with hm0 | hm2
      · obtain ⟨hlt, htarget⟩ := hrec0 address hm0
        exact ⟨hlt, Or.inr htarget⟩
      · obtain ⟨hlt, hsub⟩ := ht2.recorded address (List.mem_filter.mp hm2).1
        exact ⟨hlt, Or.inl hsub⟩
    have core : ∃ t, TouchesOnly t state ended0.val.state ∧
        ended0.val.state.parent = state.parent ∧ ended0.val.message = message ∧
        ∀ address ∈ t, fork < .paris ∧
          ((.spuriousDragon ≤ fork → address ∈ ended0.val.substate.touchedAccounts) ∨
            address = message.currentTarget) := by
      dsimp only at hdo
      split at hdo
      all_goals obtain ⟨state1, hm, hdo⟩ := Base.bind_ok_iff.mp hdo
      all_goals
        have hS1 : TouchesOnly t0 state state1 ∧
            state1.parent = state.parent ∧ StaticMessage state1 message := by
          first
          | (have ht := ‹message.shouldTransferValue = true ∧ message.value ≠ 0›
             have hm' := Base.mapError_ok_iff.mp hm
             obtain ⟨hcaller, hcode⟩ := hmsg0.2.2.2 ht.1 ht.2
             rw [hcaller] at hm'
             have so := TransactionState.sameOutside_moveEther_self hcode hm'
             have kto := TouchesOnly.of_sameOutside so
             have comb := ht0.trans kto
             simp only [List.filter_nil, List.append_nil] at comb
             exact ⟨comb, (TransactionState.parent_moveEther hm').trans hpar0,
               StaticMessage.of_sameOutside so hmsg0⟩)
          | (cases hm
             exact ⟨ht0, hpar0, hmsg0⟩)
      all_goals
        obtain ⟨h1, hp1, hmsg1⟩ := hS1
        rcases hpa : precompileAddress fork message with _ | addr
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
          · rename_i after hrun
            cases hdo
            obtain ⟨t2, ht2⟩ := staticTouchStep_runFrame
              (hf := StaticFrame.start hmsg1 _ _) (h := hrun)
              (fun {evm' after'} hf' hstep =>
                staticTouchResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
              (fun {evm' caller' message' resume'} hf' hstep =>
                staticTouchResult_step hf'.1 hf'.2.1 hf'.2.2 hstep)
              (by
                intro caller' message' lt c used _ hm hrun'
                split at hrun'
                · obtain ⟨tc, htc, hpc, hmc, hrecc⟩ :=
                    ih message'.gas (by omega) message' caller'.state _ _ _ rfl hm ⟨c, used⟩ hrun'
                  refine ⟨tc, htc, hpc, fun addr ha => ?_⟩
                  obtain ⟨herr, hlt, hmem⟩ := hrecc addr ha
                  exact ⟨herr, hlt, by rwa [hmc]⟩
                · have := hm.2.1
                  simp_all)
            exact stepCore h1 hp1 ht2
        · simp only [hpa] at hdo
          split at hdo
          · cases hdo
            exact stepCore h1 hp1
              (StaticTouchStep.of_staticKeep ⟨TransactionState.SameOutside.refl _ _, rfl, rfl, rfl⟩
                rfl)
          · split at hdo
            · rename_i after hrp
              cases hdo
              exact stepCore h1 hp1 (staticKeepStep_runPrecompile hrp).toTouchStep
            · cases hdo
              exact stepCore h1 hp1
                (StaticTouchStep.of_staticKeep
                  ⟨TransactionState.SameOutside.refl _ _, rfl, rfl, rfl⟩ rfl)
    have hval := congrArg Subtype.val rolled
    simp only at hval
    rw [← hval]
    obtain ⟨t, ht, hpar, hmeq, hrec⟩ := core
    unfold rollbackOnError
    split
    · exact ⟨[], TouchesOnly.of_sameOutside (TransactionState.sameOutside_restoreTxState hpar),
        hpar, hmeq, by simp⟩
    · rename_i hnot
      have herr : ended0.val.error = none := Option.not_isSome_iff_eq_none.mp hnot
      exact ⟨t, ht, hpar, hmeq, fun addr ha => ⟨herr, (hrec addr ha).1, (hrec addr ha).2⟩⟩

/-- From Byzantium, a static message changes the state by touches of absent accounts.

The storage and the transient storage of every address stay as they were.

Each touched address had no account, and holds the empty account after.

When the message fails, or from Paris, no address is touched.

Otherwise, each touched address is in the touched accounts of the substate, or is the target. -/
theorem processMessage_touches_static [LawfulGasMeter Meter] (hfork : .byzantium ≤ fork)
    {message : Message fork} {state : TransactionState} {substate : Substate}
    {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hmsg : StaticMessage state message) {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    ∃ touched, TouchesOnly touched state ended.val.state ∧
      ended.val.state.parent = state.parent ∧
      ∀ address ∈ touched, ended.val.error = none ∧ fork < .paris ∧
        (address ∈ ended.val.substate.touchedAccounts ∨ address = message.currentTarget) := by
  obtain ⟨touched, hto, hpar, -, hrec⟩ :=
    processMessage_touchesOnly_static message.gas message state substate meter held rfl hmsg ended h
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  refine ⟨touched, hto, hpar, fun address ha => ?_⟩
  obtain ⟨herr, hlt, hmem⟩ := hrec address ha
  exact ⟨herr, hlt, hmem.imp_left fun f => f hsd⟩

omit [GasMeter Meter] in
/-- Deleting the touched empty accounts at a fork from Spurious Dragon removes those in `toDelete`.

Every other address keeps its account and its storage, and all transient storage stays. -/
theorem destroyTouchedEmptyAccounts_at (hfork : .spuriousDragon ≤ fork)
    (state : TransactionState) (toDelete : List Address) (address : Address) :
    (if address ∈ toDelete ∧ state.getAccountOptional address = some EMPTY_ACCOUNT then
      (state.destroyTouchedEmptyAccounts fork toDelete).getAccountOptional address = none ∧
        ∀ key, (state.destroyTouchedEmptyAccounts fork toDelete).getStorage address key = 0
    else
      (state.destroyTouchedEmptyAccounts fork toDelete).getAccountOptional address =
        state.getAccountOptional address ∧
      ∀ key, (state.destroyTouchedEmptyAccounts fork toDelete).getStorage address key =
        state.getStorage address key) ∧
    ∀ key, (state.destroyTouchedEmptyAccounts fork toDelete).getTransientStorage address key =
      state.getTransientStorage address key := by
  unfold TransactionState.destroyTouchedEmptyAccounts
  simp only [show ¬fork < Fork.spuriousDragon from Nat.not_lt.mpr hfork, ite_false]
  induction toDelete generalizing state with
  | nil => simp
  | cons head rest ih =>
    simp only [List.foldl_cons]
    by_cases hhead : address = head
    · subst hhead
      by_cases hempty : state.getAccountOptional address = some EMPTY_ACCOUNT
      · have he : state.accountExistsAndIsEmpty address = true :=
          (accountExistsAndIsEmpty_iff_eq_some state address).mpr hempty
        simp only [he, ↓reduceIte, List.mem_cons, true_or, hempty, and_self]
        obtain ⟨hrest, htrans⟩ := ih (state.destroyAccount address)
        have hnone : (state.destroyAccount address).getAccountOptional address = none := by
          simp [TransactionState.destroyAccount,
            TransactionState.getAccountOptional_setAccount_self]
        have hzero : ∀ key, (state.destroyAccount address).getStorage address key = 0 := by
          intro key; rw [TransactionState.getStorage_destroyAccount]; simp
        simp only [hnone, reduceCtorEq, and_false, ↓reduceIte] at hrest
        exact ⟨⟨hrest.1, fun key => (hrest.2 key).trans (hzero key)⟩, htrans⟩
      · have he : state.accountExistsAndIsEmpty address = false :=
          Bool.eq_false_iff.mpr (mt (accountExistsAndIsEmpty_iff_eq_some state address).mp hempty)
        simp only [he, Bool.false_eq_true, ↓reduceIte, hempty, and_false]
        obtain ⟨hrest, htrans⟩ := ih state
        simp only [hempty, and_false, ↓reduceIte] at hrest
        exact ⟨hrest, htrans⟩
    · simp only [List.mem_cons, hhead, false_or]
      by_cases he : state.accountExistsAndIsEmpty head = true
      · simp only [he, ↓reduceIte]
        obtain ⟨hrest, htrans⟩ := ih (state.destroyAccount head)
        have hacc := (TransactionState.sameOutside_destroyAccount state head address
          (by simpa using hhead)).1
        have hst := (TransactionState.sameOutside_destroyAccount state head address
          (by simpa using hhead)).2.1
        refine ⟨?_, htrans⟩
        by_cases hc : address ∈ rest ∧ state.getAccountOptional address = some EMPTY_ACCOUNT
        · have hc' : address ∈ rest ∧
              (state.destroyAccount head).getAccountOptional address = some EMPTY_ACCOUNT := by
            rwa [hacc]
          simp only [hc, hc', and_self, ↓reduceIte] at hrest ⊢
          exact hrest
        · have hc' : ¬(address ∈ rest ∧
              (state.destroyAccount head).getAccountOptional address = some EMPTY_ACCOUNT) := by
            rwa [hacc]
          simp only [hc, hc', ↓reduceIte] at hrest ⊢
          exact ⟨hrest.1.trans hacc, fun key => (hrest.2 key).trans (hst key)⟩
      · simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact ih state

/-- From Byzantium, EIP-161 deletion after a static message leaves only deleted empty accounts.

When the message succeeds before Paris, `toDelete` must cover the touched accounts of the substate.

It must also cover the target when that account is empty.

Every address outside `toDelete` keeps its account, its storage and its transient storage.

Each address in `toDelete` that held the empty account before is deleted.

Every other address, even one that the call touched, keeps the optional account that it had before.

The storage of an address in `toDelete` that ends empty is zero, and other storage is unchanged. -/
theorem destroyTouchedEmptyAccounts_processMessage_static [LawfulGasMeter Meter]
    (hfork : .byzantium ≤ fork) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hmsg : StaticMessage state message) {ended}
    (h : processMessage fork message state substate meter held = .ok ended)
    {toDelete : List Address}
    (hcover : ended.val.error = none → fork < .paris →
      (∀ address ∈ ended.val.substate.touchedAccounts, address ∈ toDelete) ∧
        (ended.val.state.accountExistsAndIsEmpty message.currentTarget = true →
          message.currentTarget ∈ toDelete)) :
    TransactionState.SameOutside toDelete state
      (ended.val.state.destroyTouchedEmptyAccounts fork toDelete) ∧
      (ended.val.state.destroyTouchedEmptyAccounts fork toDelete).parent = state.parent ∧
      (∀ address key,
        (ended.val.state.destroyTouchedEmptyAccounts fork toDelete).getTransientStorage
          address key = state.getTransientStorage address key) ∧
      (∀ address,
        (ended.val.state.destroyTouchedEmptyAccounts fork toDelete).getAccountOptional address =
          if address ∈ toDelete ∧ state.getAccountOptional address = some EMPTY_ACCOUNT then none
          else state.getAccountOptional address) ∧
      ∀ address key,
        (ended.val.state.destroyTouchedEmptyAccounts fork toDelete).getStorage address key =
          if address ∈ toDelete ∧
              ended.val.state.getAccountOptional address = some EMPTY_ACCOUNT then 0
          else state.getStorage address key := by
  obtain ⟨touched, hto, hpar, hrec⟩ := processMessage_touches_static hfork hmsg h
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hsub : ∀ address ∈ touched, address ∈ toDelete := by
    intro address ha
    obtain ⟨herr, hlt, hmem⟩ := hrec address ha
    obtain ⟨hsub0, htarget0⟩ := hcover herr hlt
    rcases hmem with hs | rfl
    · exact hsub0 address hs
    · exact htarget0 ((accountExistsAndIsEmpty_iff_eq_some _ _).mpr (hto.2.2.2 _ ha).2)
  refine ⟨?_, (TransactionState.parent_destroyTouchedEmptyAccounts fork ended.val.state
    toDelete).trans hpar, ?_, ?_, ?_⟩
  · intro address hnot
    have hnot_t : address ∉ touched := fun ht => hnot (hsub address ht)
    obtain ⟨hacc1, hst1, htr1⟩ := hto.1 address hnot_t
    obtain ⟨hacc2, hst2, htr2⟩ :=
      TransactionState.sameOutside_destroyTouchedEmptyAccounts fork ended.val.state toDelete
        address hnot
    exact ⟨hacc2.trans hacc1, fun k => (hst2 k).trans (hst1 k),
      fun k => (htr2 k).trans (htr1 k)⟩
  · intro address key
    exact ((destroyTouchedEmptyAccounts_at hsd ended.val.state toDelete address).2 key).trans
      (hto.2.2.1 address key)
  · intro address
    obtain ⟨hd, -⟩ := destroyTouchedEmptyAccounts_at hsd ended.val.state toDelete address
    by_cases hpre : address ∈ toDelete ∧ state.getAccountOptional address = some EMPTY_ACCOUNT
    · obtain ⟨hmem_del, hsome⟩ := hpre
      have hnot_t : address ∉ touched := by
        intro ht
        have := (hto.2.2.2 address ht).1
        simp [hsome] at this
      have hend_some : ended.val.state.getAccountOptional address = some EMPTY_ACCOUNT :=
        (hto.1 address hnot_t).1.trans hsome
      simp only [hmem_del, hsome, hend_some, and_self, ↓reduceIte] at hd ⊢
      exact hd.1
    · simp only [hpre, ↓reduceIte]
      by_cases ht : address ∈ touched
      · have hmem_del : address ∈ toDelete := hsub address ht
        obtain ⟨hnone, hend_some⟩ := hto.2.2.2 address ht
        simp only [hmem_del, hend_some, and_self, ↓reduceIte] at hd
        exact hd.1.trans hnone.symm
      · have hend_eq : ended.val.state.getAccountOptional address =
            state.getAccountOptional address := (hto.1 address ht).1
        have hnot_end : ¬(address ∈ toDelete ∧
            ended.val.state.getAccountOptional address = some EMPTY_ACCOUNT) := by
          rwa [hend_eq]
        simp only [hnot_end, ↓reduceIte] at hd
        exact hd.1.trans hend_eq
  · intro address key
    obtain ⟨hd, -⟩ := destroyTouchedEmptyAccounts_at hsd ended.val.state toDelete address
    by_cases hend :
        address ∈ toDelete ∧ ended.val.state.getAccountOptional address = some EMPTY_ACCOUNT
    · simp only [hend, and_self, ↓reduceIte] at hd ⊢
      exact hd.2 key
    · simp only [hend, ↓reduceIte] at hd ⊢
      exact (hd.2 key).trans (hto.2.1 address key)

/-- The touched accounts of a message call, with any empty target added before Paris. -/
def messageTouchedAccounts (evm : Evm fork Meter) : Std.ExtTreeSet Address :=
  if fork ≥ .spuriousDragon ∧ fork < .paris ∧
      evm.state.accountExistsAndIsEmpty evm.message.currentTarget then
    evm.substate.touchedAccounts.insert evm.message.currentTarget
  else
    evm.substate.touchedAccounts

/-- From Byzantium, EIP-161 deletion of the message touches leaves only deleted empty accounts.

Every address outside `messageTouchedAccounts` keeps its account, storage and transient storage.

Each address in `messageTouchedAccounts` that held the empty account before is deleted.

Every other address, even one that the call touched, keeps the optional account that it had before.

The storage of an address in `messageTouchedAccounts` that ends empty is zero.

Every other storage slot stays unchanged. -/
theorem destroyMessageTouchedEmptyAccounts_processMessage_static [LawfulGasMeter Meter]
    (hfork : .byzantium ≤ fork) {message : Message fork} {state : TransactionState}
    {substate : Substate} {meter : Meter} {held : GasMeter.gasHeld meter ≤ message.gas}
    (hmsg : StaticMessage state message) {ended}
    (h : processMessage fork message state substate meter held = .ok ended) :
    TransactionState.SameOutside (messageTouchedAccounts ended.val).toList state
      (ended.val.state.destroyTouchedEmptyAccounts fork
        (messageTouchedAccounts ended.val).toList) ∧
      (ended.val.state.destroyTouchedEmptyAccounts fork
        (messageTouchedAccounts ended.val).toList).parent = state.parent ∧
      (∀ address key,
        (ended.val.state.destroyTouchedEmptyAccounts fork
          (messageTouchedAccounts ended.val).toList).getTransientStorage address key =
          state.getTransientStorage address key) ∧
      (∀ address,
        (ended.val.state.destroyTouchedEmptyAccounts fork
          (messageTouchedAccounts ended.val).toList).getAccountOptional address =
          if address ∈ (messageTouchedAccounts ended.val).toList ∧
              state.getAccountOptional address = some EMPTY_ACCOUNT then none
          else state.getAccountOptional address) ∧
      ∀ address key,
        (ended.val.state.destroyTouchedEmptyAccounts fork
          (messageTouchedAccounts ended.val).toList).getStorage address key =
          if address ∈ (messageTouchedAccounts ended.val).toList ∧
              ended.val.state.getAccountOptional address = some EMPTY_ACCOUNT then 0
          else state.getStorage address key := by
  have hsd : .spuriousDragon ≤ fork := Nat.le_trans (by decide) hfork
  have hmeq : ended.val.message = message :=
    (processMessage_touchesOnly_static message.gas message state substate meter held rfl hmsg
      ended h).choose_spec.2.2.1
  refine destroyTouchedEmptyAccounts_processMessage_static hfork hmsg h fun _ hlt => ⟨?_, ?_⟩
  · intro address hmem
    rw [Std.ExtTreeSet.mem_toList]
    unfold messageTouchedAccounts
    split
    · exact Std.ExtTreeSet.mem_insert.mpr (Or.inr hmem)
    · exact hmem
  · intro hempty
    rw [Std.ExtTreeSet.mem_toList]
    unfold messageTouchedAccounts
    rw [hmeq]
    simp [hsd, hlt, hempty, Std.ExtTreeSet.mem_insert]

end EthLib.Execution.Evm
