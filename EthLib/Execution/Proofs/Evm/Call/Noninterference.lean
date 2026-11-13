module

public import EthLib.Execution.Proofs.Evm.Noninterference
public import EthLib.Execution.Proofs.Evm.Call.Reads
public import EthLib.Execution.Proofs.Evm.Call.StaticStep

/-!
# Proofs: calls and creations keep agreeing frames

The two frames differ only in their states, which agree on four sets.

The sets name addresses, whole storages, slots and code hashes.

A call or a creation then fails alike unless the error aborts the run.

A success whose reads lie in the sets gives agreeing frames or agreeing messages.

A message it sends is the same in both frames, and so is the way its caller resumes.

The caller resumes alike from two agreeing frames that end the message.

A creation checks that a contract may be deployed at the new address.

That reads whether the address has any storage, which the block access list does not record.

So the second set must hold each address of the first set with nonce 0 and no code.

That is needed only where its storage was not wiped.

The step of a frame is then covered for every opcode.

These are local steps toward the coverage of [EIP-7928, Scope and Inclusion][bal].

[bal]: https://eips.ethereum.org/EIPS/eip-7928#scope-and-inclusion
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Hash32)
open EthLib.Execution.State (EMPTY_CODE_HASH TransactionState)

variable {fork : Base.Fork} {Meter : Type} [GasMeter Meter]

/-- Take an address of the first set with nonce 0 and no code.

Its storage was wiped, or it is in the second set.

A creation reads the whole storage of such an address. -/
def CandidatesIn (account allStorage : Address → Prop) (tx : TransactionState) : Prop :=
  ∀ address, account address → (tx.getAccount address).nonce = 0 →
    (tx.getAccount address).codeHash = EMPTY_CODE_HASH →
    address ∈ tx.storageClears ∨ allStorage address

/-- Two ways for a caller to resume that agree on agreeing frames that end the message.

The account that the message runs at must be in the first set.

A failure that does not abort the run is the same in both.

A success with its reads in the sets gives agreeing frames. -/
def ResumeAgrees (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (k1 k2 : Evm fork Meter → Except EvmError (Evm fork Meter)) : Prop :=
  ∀ c1 c2, FrameAgrees account allStorage slot code c1 c2 → account c1.message.currentTarget →
    (∀ err, k1 c1 = .error err → err.aborts = false → k2 c2 = .error err) ∧
      ∀ a1, k1 c1 = .ok a1 → ReadsIn account slot a1.state →
        ∃ a2, k2 c2 = .ok a2 ∧ FrameAgrees account allStorage slot code a1 a2

/-- Two results of a step that agree.

Both give agreeing frames, or both send the same message from agreeing frames.

The callers then resume in ways that agree. -/
def StepAgrees (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) : StepResult fork Meter → StepResult fork Meter → Prop
  | .next a1, .next a2 => FrameAgrees account allStorage slot code a1 a2
  | .child c1 m1 k1, .child c2 m2 k2 =>
    FrameAgrees account allStorage slot code c1 c2 ∧ m2 = m1 ∧
      ResumeAgrees account allStorage slot code k1 k2
  | _, _ => False

/-- The state of the frame that a result of a step gives, or of the frame that sends a message. -/
def StepResult.state : StepResult fork Meter → TransactionState
  | .next after => after.state
  | .child caller _ _ => caller.state

/-! ## Helpers -/

open EthLib.Execution.State.TransactionState (AgreesOn)

variable {account allStorage : Address → Prop} {slot : Address → Bytes32 → Prop}
  {code : Hash32 → Prop}

omit [GasMeter Meter] in
/-- A failed child leaves the same touches when the emptiness of its current account agrees. -/
private theorem touchedOnError_withState (caller child : Evm fork Meter) (s s' : TransactionState)
    (hempty : s'.accountExistsAndIsEmpty child.message.currentTarget =
      child.state.accountExistsAndIsEmpty child.message.currentTarget) :
    touchedOnError fork { caller with state := s } { child with state := s' } =
      touchedOnError fork caller child := by
  unfold touchedOnError
  by_cases h : child.message.currentTarget = RIPEMD160_ADDRESS
  · rw [h] at hempty
    simp only [hempty]
  · simp only [h, false_and, or_false]

omit [GasMeter Meter] in
/-- A child that succeeds leaves the same touches when the emptiness of its account agrees. -/
private theorem touchedOnSuccess_withState (caller child : Evm fork Meter)
    (s s' : TransactionState)
    (hempty : s'.accountExistsAndIsEmpty child.message.currentTarget =
      child.state.accountExistsAndIsEmpty child.message.currentTarget) :
    touchedOnSuccess fork { caller with state := s } { child with state := s' } =
      touchedOnSuccess fork caller child := by
  unfold touchedOnSuccess
  simp only [hempty]

/-- Taking in a child with a replaced state gives the same caller, with the state of that child. -/
private theorem incorporateChild_withState (caller child : Evm fork Meter)
    (s s' : TransactionState)
    (hempty : s'.accountExistsAndIsEmpty child.message.currentTarget =
      child.state.accountExistsAndIsEmpty child.message.currentTarget) :
    incorporateChild fork { caller with state := s } { child with state := s' } =
      { incorporateChild fork caller child with state := s' } := by
  unfold incorporateChild
  rw [touchedOnError_withState caller child s s' hempty,
    touchedOnSuccess_withState caller child s s' hempty]
  split <;> rfl

/-- A call resumes alike from a child with a replaced state, and keeps the state of the child. -/
private theorem resumeCall_withState (caller child : Evm fork Meter) (s s' : TransactionState)
    (hempty : s'.accountExistsAndIsEmpty child.message.currentTarget =
      child.state.accountExistsAndIsEmpty child.message.currentTarget)
    (newAccount : Nat) (outputStart outputSize : Base.U256) :
    resumeCall fork { caller with state := s } newAccount outputStart outputSize
        { child with state := s' } =
      (fun a => { a with state := s' }) <$>
        resumeCall fork caller newAccount outputStart outputSize child := by
  unfold resumeCall
  rw [incorporateChild_withState caller child s s' hempty]
  dsimp only
  generalize incorporateChild fork caller child = X
  cases child.error.isNone <;>
    simp only [Bool.false_eq_true, ↓reduceIte, pushWord, refillStateGas, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map] <;>
    cases X.stack.push _ <;> rfl

/-- A creation resumes alike from a child with a replaced state.

It keeps the state of the child. -/
private theorem resumeCreate_withState (caller child : Evm fork Meter) (s s' : TransactionState)
    (hempty : s'.accountExistsAndIsEmpty child.message.currentTarget =
      child.state.accountExistsAndIsEmpty child.message.currentTarget)
    (newAccount : Nat) (address : Address) :
    resumeCreate fork { caller with state := s } newAccount address { child with state := s' } =
      (fun a => { a with state := s' }) <$>
        resumeCreate fork caller newAccount address child := by
  unfold resumeCreate
  rw [incorporateChild_withState caller child s s' hempty]
  dsimp only
  generalize incorporateChild fork caller child = X
  cases child.error.isNone <;>
    simp only [Bool.false_eq_true, ↓reduceIte, pushWord, refillStateGas, bind, Except.bind,
      pure, Except.pure, Functor.map, Except.map] <;>
    cases X.stack.push _ <;> rfl

omit [GasMeter Meter] in
/-- A resume that moves a replaced state of the child through gives agreeing resumes. -/
private theorem resumeAgrees_of_withState
    {k : Evm fork Meter → Evm fork Meter → Except EvmError (Evm fork Meter)}
    (hk : ∀ caller child s s', s'.accountExistsAndIsEmpty child.message.currentTarget =
        child.state.accountExistsAndIsEmpty child.message.currentTarget →
      k { caller with state := s } { child with state := s' } =
        (fun a => { a with state := s' }) <$> k caller child)
    {c1 c2 : Evm fork Meter} (hrel : FrameAgrees account allStorage slot code c1 c2) :
    ResumeAgrees account allStorage slot code (k c1) (k c2) := by
  intro ch1 ch2 hch hcur
  obtain ⟨s, rfl⟩ : ∃ s, c2 = { c1 with state := s } := ⟨_, hrel.rest⟩
  obtain ⟨s', rfl⟩ : ∃ s', ch2 = { ch1 with state := s' } := ⟨_, hch.rest⟩
  have hempty := hch.state.accountExistsAndIsEmpty_eq (.inr hcur)
  have self : k c1 ch1 = (fun a => { a with state := ch1.state }) <$> k c1 ch1 :=
    hk c1 ch1 c1.state ch1.state rfl
  rw [hk c1 ch1 s s' hempty]
  refine ⟨fun err h _ => by rw [h]; rfl, fun a1 h _ => ⟨_, by rw [h]; rfl, rfl, ?_⟩⟩
  rw [h] at self
  change Except.ok a1 = Except.ok { a1 with state := ch1.state } at self
  have h' := Except.ok.inj self
  have hs := congrArg Evm.state h'
  dsimp only at hs
  rw [hs]
  exact hch.state

/-- A call resumes alike from two agreeing callers. -/
private theorem resumeCall_agrees {c1 c2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code c1 c2) (newAccount : Nat)
    (outputStart outputSize : Base.U256) :
    ResumeAgrees account allStorage slot code
      (resumeCall fork c1 newAccount outputStart outputSize)
      (resumeCall fork c2 newAccount outputStart outputSize) :=
  resumeAgrees_of_withState (k := fun c => resumeCall fork c newAccount outputStart outputSize)
    (fun c ch s s' h => resumeCall_withState c ch s s' h newAccount outputStart outputSize) hrel

/-- A creation resumes alike from two agreeing callers. -/
private theorem resumeCreate_agrees {c1 c2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code c1 c2) (newAccount : Nat)
    (address : Address) :
    ResumeAgrees account allStorage slot code (resumeCreate fork c1 newAccount address)
      (resumeCreate fork c2 newAccount address) :=
  resumeAgrees_of_withState (k := fun c => resumeCreate fork c newAccount address)
    (fun c ch s s' h => resumeCreate_withState c ch s s' h newAccount address) hrel

/-! ## Runs that agree -/

/-- Two runs of a step agree.

A failure that does not abort the run is the same in both.

A success whose reads lie in the sets gives agreeing results. -/
private def Sim (account allStorage : Address → Prop) (slot : Address → Bytes32 → Prop)
    (code : Hash32 → Prop) (x y : Except EvmError (StepResult fork Meter)) : Prop :=
  (∀ err, x = .error err → err.aborts = false → y = .error err) ∧
    ∀ r1, x = .ok r1 → ReadsIn account slot r1.state →
      ∃ r2, y = .ok r2 ∧ StepAgrees account allStorage slot code r1 r2

omit [GasMeter Meter] in
/-- Results that fail alike or agree are runs that agree. -/
private theorem Sim.of_rel {x y : Except EvmError (StepResult fork Meter)}
    (h : Base.ExceptRel (StepAgrees account allStorage slot code) x y) :
    Sim account allStorage slot code x y := by
  refine ⟨fun err hx _ => ?_, fun r1 hx _ => ?_⟩
  · subst hx
    cases y with
    | error e => rw [show err = e from h]
    | ok => exact absurd h id
  · subst hx
    cases y with
    | error => exact absurd h id
    | ok r2 => exact ⟨r2, rfl, h⟩

omit [GasMeter Meter] in
/-- Agreeing frames give agreeing results of a step. -/
private theorem next_rel {x y : Except EvmError (Evm fork Meter)}
    (h : Base.ExceptRel (FrameAgrees account allStorage slot code) x y) :
    Base.ExceptRel (StepAgrees account allStorage slot code) (StepResult.next <$> x)
      (StepResult.next <$> y) :=
  h.map fun hab => hab

/-- A call that runs no message gives agreeing results from agreeing frames. -/
private theorem skipCall_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) (gas reservoir : Nat) :
    Base.ExceptRel (StepAgrees account allStorage slot code)
      (StepResult.next <$> skipCall g1 gas reservoir)
      (StepResult.next <$> skipCall g2 gas reservoir) := by
  refine next_rel ?_
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  simp only [skipCall, pushWord, bind, Except.bind, pure, Except.pure]
  cases g1.stack.push 0
  · rfl
  · exact ⟨rfl, hrel.state⟩

/-- A call that has paid gives agreeing results from agreeing frames. -/
private theorem genericCall_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) (message : Message fork)
    (newAccount : Nat) (outputStart outputSize : Base.U256) :
    Base.ExceptRel (StepAgrees account allStorage slot code)
      (genericCall g1 message newAccount outputStart outputSize)
      (genericCall g2 message newAccount outputStart outputSize) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  unfold genericCall
  dsimp only
  by_cases hd : g1.message.depth + 1 > STACK_DEPTH_LIMIT
  · simp only [hd, ↓reduceIte]
    refine skipCall_rel ?_ _ _
    exact ⟨rfl, hrel.state⟩
  · simp only [hd, ↓reduceIte]
    refine ⟨⟨rfl, hrel.state⟩, rfl, resumeCall_agrees ?_ _ _ _⟩
    exact ⟨rfl, hrel.state⟩

/-- The end of a call gives agreeing results from agreeing frames. -/
private theorem finishCall_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2)
    (hcurrent : account g1.message.currentTarget) (kind : CallKind) (call : CallOperands)
    (callee : Callee) (subCall newAccount expandBy : Nat) :
    Base.ExceptRel (StepAgrees account allStorage slot code)
      (finishCall kind call callee subCall newAccount expandBy g1)
      (finishCall kind call callee subCall newAccount expandBy g2) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  unfold finishCall
  dsimp only
  by_cases static : kind = .call ∧ g1.message.isStatic = true ∧ call.value ≠ 0
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true static)]
    rfl
  simp only [ite_eq_right_of_eq_false _ _ (eq_false static), recordAccountRead,
    State.TransactionState.getAccount_recordAccountRead,
    hrel.state.getAccount_eq (.inr hcurrent)]
  by_cases hb : (g1.state.getAccount g1.message.currentTarget).balance < call.value
  · simp only [hb, ↓reduceIte]
    refine skipCall_rel ?_ _ _
    exact ⟨rfl, hrel.state.recordAccountRead _⟩
  · simp only [hb, ↓reduceIte]
    refine genericCall_rel ?_ _ _ _ _
    exact ⟨rfl, hrel.state.recordAccountRead _⟩

/-- The payment of a call fails alike or gives the same message gas and agreeing frames. -/
private theorem payCall_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) (kind : CallKind)
    (call : CallOperands) (memoryCost extraGas newAccount : Nat) :
    Base.ExceptRel (fun p q => p.1 = q.1 ∧ FrameAgrees account allStorage slot code p.2 q.2)
      (payCall kind call memoryCost extraGas newAccount g1)
      (payCall kind call memoryCost extraGas newAccount g2) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  unfold payCall
  split
  · simp only [chargeGas, chargeStateGas, bind, Except.bind, pure, Except.pure]
    cases GasMeter.charge g1.gas (extraGas + memoryCost) with
    | error => rfl
    | ok m1 =>
      dsimp only
      cases GasMeter.chargeState m1 newAccount with
      | error => rfl
      | ok m2 =>
        dsimp only
        cases GasMeter.charge m2 _ with
        | error => rfl
        | ok m3 => exact ⟨rfl, rfl, hrel.state⟩
  · simp only [chargeGas, bind, Except.bind, pure, Except.pure]
    cases GasMeter.charge g1.gas _ with
    | error => rfl
    | ok m1 => exact ⟨rfl, rfl, hrel.state⟩

/-- The rest of a call once it has resolved its callee: it pays, then sends its message. -/
private def callPay (kind : CallKind) (call : CallOperands) (cold : Bool)
    (memoryCost expandBy : Nat) (callee : Callee) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) := do
  let extraGas := callExtraGas fork kind evm.state call cold callee
  let newAccount := callNewAccountStateGas fork kind evm.state call
  let (subCall, evm) ← payCall kind call memoryCost extraGas newAccount evm
  finishCall kind call callee subCall newAccount expandBy evm

/-- The rest of a call once it has read its address: it resolves a delegation, then pays. -/
private def callResolve (kind : CallKind) (call : CallOperands) (cold : Bool)
    (known memoryCost expandBy : Nat) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) := do
  let (callee, evm) ← accessDelegation evm call.address known
  keepReads evm .next (callPay kind call cold memoryCost expandBy callee evm)

/-- A call pops, checks, reads its address, then resolves its callee. -/
private theorem callStep_eq (kind : CallKind) (evm : Evm fork Meter) : callStep kind evm = (do
    let (call, evm) ← popCallOperands kind evm
    if fork ≥ .glamsterdam ∧ kind = .call ∧ evm.message.isStatic ∧ call.value ≠ 0 then
      throw .writeInStaticContext
    let ranges := [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]
    let growth := extendMemory evm.memory.size ranges
    let (cold, evm) := accessAddress evm call.address
    let known := callBaseCost fork cold + callValueCost fork call.value + growth.cost
    checkGas evm known
    let evm := recordAccountRead evm call.address
    keepReads evm .next (callResolve kind call cold known growth.cost growth.expandBy evm)) :=
  rfl

/-- A call that has resolved its callee gives agreeing results from agreeing frames. -/
private theorem callPay_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) {call : CallOperands}
    (haddress : account call.address) (hcurrent : account g1.message.currentTarget)
    (kind : CallKind) (cold : Bool) (memoryCost expandBy : Nat) (callee : Callee) :
    Base.ExceptRel (StepAgrees account allStorage slot code)
      (callPay kind call cold memoryCost expandBy callee g1)
      (callPay kind call cold memoryCost expandBy callee g2) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  have hextra : callExtraGas fork kind s call cold callee =
      callExtraGas fork kind g1.state call cold callee := by
    simp only [callExtraGas, callNewAccountCost, hrel.state.isAccountAlive_eq (.inr haddress),
      hrel.state.accountExists_eq (.inr haddress)]
  have hnew : callNewAccountStateGas fork kind s call =
      callNewAccountStateGas fork kind g1.state call := by
    simp only [callNewAccountStateGas, hrel.state.isAccountAlive_eq (.inr haddress)]
  unfold callPay
  dsimp only
  rw [hextra, hnew]
  refine (payCall_rel hrel kind call memoryCost _ _).bind fun {a b} hab ha _ => ?_
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  obtain ⟨rfl, hfr⟩ := hab
  exact finishCall_rel hfr (by rw [payCall_message ha]; exact hcurrent) _ _ _ _ _ _

/-- Keeping the reads of agreeing frames keeps results that fail alike or agree. -/
private theorem keepReads_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2)
    {x y : Except EvmError (StepResult fork Meter)}
    (h : Base.ExceptRel (StepAgrees account allStorage slot code) x y) :
    Base.ExceptRel (StepAgrees account allStorage slot code) (keepReads g1 .next x)
      (keepReads g2 .next y) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  cases x with
  | error e =>
    cases y with
    | error e' =>
      cases (show e = e' from h)
      unfold keepReads
      dsimp only
      cases e.aborts <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ⟨rfl, hrel.state⟩
      · rfl
    | ok => exact absurd h id
  | ok r1 =>
    cases y with
    | error => exact absurd h id
    | ok r2 => exact h

omit [GasMeter Meter] in
/-- The code of an agreed account is the same in agreeing frames. -/
private theorem accountCode_eq {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) {address : Address}
    (ha : account address) (hcodes : CodesIn account code g1.state) :
    accountCode g2 address = accountCode g1 address := by
  unfold accountCode
  rw [hrel.state.getAccount_eq (.inr ha), hrel.state.getCode_eq (hcodes _ ha)]

/-- The access to a delegate fails alike, or agrees when the sets hold the delegate. -/
private theorem accessDelegation_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) {address : Address}
    (ha : account address) (hcodes : CodesIn account code g1.state) (known : Nat) :
    (∀ err, accessDelegation g1 address known = .error err → err.aborts = false →
        accessDelegation g2 address known = .error err) ∧
      ∀ callee g1', accessDelegation g1 address known = .ok (callee, g1') →
        (∀ a, a ∈ g1'.state.accountReads → account a) →
        ∃ g2', accessDelegation g2 address known = .ok (callee, g2') ∧
          FrameAgrees account allStorage slot code g1' g2' := by
  have hcode := accountCode_eq hrel ha hcodes
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  unfold accessDelegation
  rw [hcode]
  cases accountCode g1 address with
  | error e =>
    refine ⟨fun _ h _ => ?_, fun _ _ h => ?_⟩
    · exact h
    · cases h
  | ok bytes =>
    simp only [bind, Except.bind]
    cases (if fork ≥ .pectra then delegatedAddress bytes else none) with
    | none =>
      dsimp only [pure, Except.pure]
      constructor
      · intro _ h _
        cases h
      · intro callee g1' h _
        cases h
        exact ⟨_, rfl, hrel⟩
    | some d =>
      dsimp only [pure, Except.pure]
      rw [accessAddress_withState g1 s d]
      dsimp only
      have hck : ∀ n, checkGas { (accessAddress g1 d).2 with state := s } n =
          checkGas (accessAddress g1 d).2 n := fun _ => rfl
      have hst : (accessAddress g1 d).2.state = g1.state := state_accessAddress _ _
      rw [hck]
      cases checkGas (accessAddress g1 d).2 (known + accountAccessCost fork (accessAddress g1 d).1)
        with
      | error e =>
        refine ⟨fun _ h _ => ?_, fun _ _ h => ?_⟩
        · exact h
        · cases h
      | ok u =>
        dsimp only
        have hagree : AgreesOn account allStorage slot code
            (recordAccountRead (accessAddress g1 d).2 d).state (s.recordAccountRead d) := by
          simp only [recordAccountRead, hst]
          exact hrel.state.recordAccountRead d
        have hframe : FrameAgrees account allStorage slot code
            (recordAccountRead (accessAddress g1 d).2 d)
            (recordAccountRead { (accessAddress g1 d).2 with state := s } d) := ⟨rfl, hagree⟩
        refine ⟨fun err h nab => ?_, fun callee g1' h hreads => ?_⟩
        · revert h
          cases hc : accountCode (recordAccountRead (accessAddress g1 d).2 d) d with
          | error e =>
            intro h
            cases h
            rw [aborts_of_accountCode hc] at nab
            cases nab
          | ok bytes' =>
            intro h
            cases h
        · revert h
          cases hc : accountCode (recordAccountRead (accessAddress g1 d).2 d) d with
          | error e =>
            intro h
            cases h
          | ok bytes' =>
            intro h
            cases h
            have hd : account d := hreads d (by
              simp [recordAccountRead, State.TransactionState.recordAccountRead,
                Std.ExtTreeSet.mem_insert])
            have hcodes' :
                CodesIn account code (recordAccountRead (accessAddress g1 d).2 d).state := by
              simp only [recordAccountRead, hst]
              exact hcodes
            rw [accountCode_eq hframe hd hcodes', hc]
            exact ⟨_, rfl, hframe⟩

omit [GasMeter Meter] in
/-- A record of a read keeps every earlier read. -/
private theorem mem_recordAccountRead {tx : TransactionState} {a b : Address}
    (h : a ∈ tx.accountReads) : a ∈ (tx.recordAccountRead b).accountReads := by
  simp [State.TransactionState.recordAccountRead, Std.ExtTreeSet.mem_insert, h]

/-- The rest of a call keeps every read of the frame that starts it. -/
private theorem callPay_reads {kind : CallKind} {call : CallOperands} {cold : Bool}
    {memoryCost expandBy : Nat} {callee : Callee} {g : Evm fork Meter}
    {r : StepResult fork Meter}
    (h : keepReads g .next (callPay kind call cold memoryCost expandBy callee g) = .ok r) :
    ∀ a, a ∈ g.state.accountReads → a ∈ r.state.accountReads := by
  intro a hmem
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · unfold callPay at h
    obtain ⟨⟨sub, p⟩, hp, h⟩ := Base.bind_ok_iff.mp h
    have hs := state_finishCall h
    have hps := state_payCall hp
    cases r with
    | next after =>
      change after.state = _ at hs
      change a ∈ after.state.accountReads
      rw [hs, hps]
      exact mem_recordAccountRead hmem
    | child after _ _ =>
      change after.state = _ at hs
      change a ∈ after.state.accountReads
      rw [hs, hps]
      exact mem_recordAccountRead hmem
  · exact hmem

/-- A call that has read its address gives agreeing runs from agreeing frames. -/
private theorem callResolve_sim {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) {call : CallOperands}
    (haddress : account call.address) (hcodes : CodesIn account code g1.state)
    (hcurrent : account g1.message.currentTarget) (kind : CallKind) (cold : Bool)
    (known memoryCost expandBy : Nat) :
    Sim account allStorage slot code (callResolve kind call cold known memoryCost expandBy g1)
      (callResolve kind call cold known memoryCost expandBy g2) := by
  obtain ⟨herr, hok⟩ := accessDelegation_rel hrel haddress hcodes known
  unfold callResolve
  refine ⟨fun err h nab => ?_, fun r1 h reads => ?_⟩
  · rcases Base.bind_eq_error h with h | ⟨⟨callee, g1'⟩, hd, h⟩
    · rw [herr err h nab]
      rfl
    · dsimp only at h
      rw [(keepReads_eq_error.mp h).2] at nab
      cases nab
  · obtain ⟨⟨callee, g1'⟩, hd, h⟩ := Base.bind_ok_iff.mp h
    dsimp only at h
    obtain ⟨g2', hd2, hfr⟩ :=
      hok callee g1' hd fun a hmem => reads.account a (callPay_reads h a hmem)
    rw [hd2]
    have hrel2 := keepReads_rel hfr (callPay_rel hfr haddress
      (by rw [accessDelegation_message hd]; exact hcurrent) kind cold memoryCost expandBy callee)
    exact (Sim.of_rel hrel2).2 r1 h reads

/-- A success followed by a step gives the step on the value. -/
private theorem exceptOk_bind {α β : Type} (x : α) (k : α → Except EvmError β) :
    (Except.ok x >>= k) = k x := rfl

omit [GasMeter Meter] in
/-- The pops of a call move a replaced state through unchanged. -/
private theorem popCallOperands_withState (kind : CallKind) (evm : Evm fork Meter)
    (other : TransactionState) :
    popCallOperands kind { evm with state := other } =
      (fun p => (p.1, { p.2 with state := other })) <$> popCallOperands kind evm := by
  cases kind <;>
    simp only [popCallOperands, popCallValue, CallKind.sendsValue, ↓reduceIte,
      Bool.false_eq_true, popWord_withState, bind_map_left, map_bind, map_pure, exceptOk_bind]

/-- A call that succeeds has read the address that it pops. -/
private theorem callStep_reads_address {kind : CallKind} {evm popped : Evm fork Meter}
    {call : CallOperands} {r : StepResult fork Meter}
    (pop : popCallOperands kind evm = .ok (call, popped)) (h : callStep kind evm = .ok r) :
    call.address ∈ r.state.accountReads := by
  have hs := state_callStep pop h
  have ht : call.address ∈ (evm.state.recordAccountRead call.address).accountReads := by
    simp [State.TransactionState.recordAccountRead, Std.ExtTreeSet.mem_insert]
  dsimp only at hs
  cases r with
  | next after =>
    change call.address ∈ after.state.accountReads
    rcases hs with ⟨-, -, hs, -⟩ | ⟨hs, -⟩ | hs <;> rw [hs]
    · exact ht
    · split
      · exact mem_recordAccountRead ht
      · exact ht
    · refine mem_recordAccountRead ?_
      split
      · exact mem_recordAccountRead ht
      · exact ht
  | child after _ _ =>
    change call.address ∈ after.state.accountReads
    rw [hs]
    refine mem_recordAccountRead ?_
    split
    · exact mem_recordAccountRead ht
    · exact ht

/-- Keeping the reads of agreeing frames keeps runs that agree. -/
private theorem keepReads_sim {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2)
    {x y : Except EvmError (StepResult fork Meter)}
    (h : Sim account allStorage slot code x y) :
    Sim account allStorage slot code (keepReads g1 .next x) (keepReads g2 .next y) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  refine ⟨fun err hx nab => ?_, fun r1 hx reads => ?_⟩
  · rw [(keepReads_eq_error.mp hx).2] at nab
    cases nab
  · unfold keepReads at hx ⊢
    cases hxe : x with
    | error e =>
      rw [hxe] at hx
      dsimp only at hx
      cases hab : e.aborts
      · rw [hab] at hx
        simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at hx
        subst hx
        rw [h.1 e hxe hab]
        simp only [hab, Bool.false_eq_true, ↓reduceIte]
        exact ⟨_, rfl, rfl, hrel.state⟩
      · rw [hab] at hx
        cases hx
    | ok r =>
      rw [hxe] at hx
      cases hx
      obtain ⟨r2, hy, hr⟩ := h.2 _ hxe reads
      rw [hy]
      exact ⟨r2, rfl, hr⟩

/-- A call gives agreeing runs from agreeing frames. -/
private theorem callStep_sim {e1 e2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code e1 e2)
    (hcodes : CodesIn account code e1.state) (hcurrent : account e1.message.currentTarget)
    (kind : CallKind) :
    Sim account allStorage slot code (callStep kind e1) (callStep kind e2) := by
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rcases hp : popCallOperands kind e1 with e | ⟨call, p1⟩
  · have h1 : callStep kind e1 = .error e := by
      rw [callStep_eq, hp]
      rfl
    have h2 : callStep kind { e1 with state := s } = .error e := by
      rw [callStep_eq, popCallOperands_withState, hp]
      rfl
    rw [h1, h2]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  have hp2 : popCallOperands kind { e1 with state := s } = .ok (call, { p1 with state := s }) := by
    rw [popCallOperands_withState, hp]
    rfl
  have hpe := popCallOperands_eq_ok hp
  have k1 := callStep_eq kind e1
  have k2 := callStep_eq kind { e1 with state := s }
  rw [hp, exceptOk_bind] at k1
  rw [hp2, exceptOk_bind] at k2
  dsimp only at k1 k2
  rw [accessAddress_withState p1 s call.address] at k2
  dsimp only at k2
  by_cases static : fork ≥ .glamsterdam ∧ kind = .call ∧ p1.message.isStatic = true ∧
      call.value ≠ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true static)] at k1 k2
    rw [k1, k2]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  rw [ite_eq_right_of_eq_false _ _ (eq_false static)] at k1 k2
  have hqs : (accessAddress p1 call.address).2.state = e1.state := by
    rw [state_accessAddress, hpe]
  have hqm : (accessAddress p1 call.address).2.message = e1.message := by
    rw [accessAddress_message, hpe]
  have hck : ∀ n, checkGas { (accessAddress p1 call.address).2 with state := s } n =
      checkGas (accessAddress p1 call.address).2 n := fun _ => rfl
  rw [hck] at k2
  cases hc : checkGas (accessAddress p1 call.address).2 (callBaseCost fork
      (accessAddress p1 call.address).1 + callValueCost fork call.value +
      (extendMemory p1.memory.size
        [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]).cost) with
  | error e =>
    rw [hc] at k1 k2
    rw [k1, k2]
    exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  | ok u =>
    rw [hc, exceptOk_bind] at k1 k2
    have hframe : FrameAgrees account allStorage slot code
        (recordAccountRead (accessAddress p1 call.address).2 call.address)
        (recordAccountRead { (accessAddress p1 call.address).2 with state := s } call.address) :=
      ⟨rfl, by simp only [recordAccountRead, hqs]; exact hrel.state.recordAccountRead _⟩
    have hcodes' : CodesIn account code
        (recordAccountRead (accessAddress p1 call.address).2 call.address).state := by
      simp only [recordAccountRead, hqs]
      exact hcodes
    have hcur' : account
        (recordAccountRead (accessAddress p1 call.address).2 call.address).message.currentTarget :=
      by
        simp only [recordAccountRead, hqm]
        exact hcurrent
    refine ⟨fun err h nab => ?_, fun r1 h reads => ?_⟩
    · rw [k1] at h
      rw [(keepReads_eq_error.mp h).2] at nab
      cases nab
    · have haddr := reads.account _ (callStep_reads_address hp h)
      rw [k1] at h
      rw [k2]
      exact (keepReads_sim hframe (callResolve_sim hframe haddr hcodes' hcur' _ _ _ _ _)).2 r1 h
        reads

/-- The rest of a creation once it has read the new address.

It pays and raises the nonce, then sends its message or pushes 0. -/
private def createRest (value : Base.U256) (initCode : ByteArray) (current address : Address)
    (evm : Evm fork Meter) : Except EvmError (StepResult fork Meter) := do
  let newAccount := createNewAccountStateGas fork evm.state address
  let evm ← chargeStateGas evm newAccount
  let gas := createMessageGas fork (GasMeter.gasLeft evm.gas)
  let evm ← chargeGas evm gas
  let deployable := evm.state.accountDeployable address
  let state ← (evm.state.incrementNonce fork current).mapError .state
  let evm := { evm with state }
  if deployable then
    let reservoir := GasMeter.reservoir evm.gas
    let evm := { evm with gas := GasMeter.drain evm.gas }
    let message : Message fork :=
      { blockEnv := evm.message.blockEnv
        txEnv := evm.message.txEnv
        caller := current
        target := none
        currentTarget := address
        gas
        reservoir
        value
        data := .empty
        codeAddress := none
        code := initCode
        depth := evm.message.depth + 1
        shouldTransferValue := true
        isStatic := false
        disablePrecompiles := false }
    .ok (.child evm message (resumeCreate fork evm newAccount address))
  else do
    let evm ← pushWord (refillStateGas evm newAccount) 0
    return .next (advance evm)

/-- A creation once it has read its sender: check, derive the address, read it, go on. -/
private def launchFrom (value : Base.U256) (initCode : ByteArray) (salt : Option Base.U256)
    (evm : Evm fork Meter) : Except EvmError (StepResult fork Meter) :=
  let current := evm.message.currentTarget
  let sender := evm.state.getAccount current
  if sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT then
    .next <$> skipCall evm 0 0
  else do
    let address ← creationAddress current sender.nonce salt initCode
    let evm := recordAccountRead (accessAddress evm address).2 address
    keepReads evm .next (createRest value initCode current address evm)

/-- A creation reads its sender, then goes on from that frame. -/
private theorem launchCreate_eq (evm : Evm fork Meter) (value : Base.U256)
    (initCode : ByteArray) (salt : Option Base.U256) : launchCreate evm value initCode salt =
    launchFrom value initCode salt
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
  rfl

/-- The rest of a creation gives agreeing results when the sets hold the new address. -/
private theorem createRest_rel {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2) {current address : Address}
    (hcurrent : account current) (haddress : account address)
    (hcandidates : CandidatesIn account allStorage g1.state) (value : Base.U256)
    (initCode : ByteArray) :
    Base.ExceptRel (StepAgrees account allStorage slot code)
      (createRest value initCode current address g1)
      (createRest value initCode current address g2) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  have hnew : createNewAccountStateGas fork s address =
      createNewAccountStateGas fork g1.state address := by
    simp only [createNewAccountStateGas, hrel.state.isAccountAlive_eq (.inr haddress)]
  have hdep : s.accountDeployable address = g1.state.accountDeployable address :=
    hrel.state.accountDeployable_eq (.inr haddress) (hcandidates address haddress)
  have hinc := hrel.state.incrementNonce fork (.inr hcurrent)
  unfold createRest
  dsimp only
  rw [hnew]
  simp only [chargeStateGas, chargeGas, bind, Except.bind, pure, Except.pure]
  cases GasMeter.chargeState g1.gas (createNewAccountStateGas fork g1.state address) with
  | error => rfl
  | ok m1 =>
    dsimp only
    cases GasMeter.charge m1 _ with
    | error => rfl
    | ok m2 =>
      dsimp only
      rw [hdep]
      revert hinc
      cases g1.state.incrementNonce fork current <;>
        cases s.incrementNonce fork current <;> intro hinc <;>
        simp only [Base.ExceptRel] at hinc
      · subst hinc
        rfl
      · rename_i st1 st2
        dsimp only [Except.mapError]
        split
        · exact ⟨⟨rfl, hinc⟩, rfl, resumeCreate_agrees ⟨rfl, hinc⟩ _ _⟩
        · simp only [pushWord, refillStateGas, bind, Except.bind, pure, Except.pure]
          cases g1.stack.push 0 with
          | error => rfl
          | ok => exact ⟨rfl, hinc⟩

/-- The rest of a creation keeps every read of the frame that starts it. -/
private theorem createRest_reads {value : Base.U256} {initCode : ByteArray}
    {current address : Address} {g : Evm fork Meter} {r : StepResult fork Meter}
    (h : createRest value initCode current address g = .ok r) :
    ∀ a, a ∈ g.state.accountReads → a ∈ r.state.accountReads := by
  intro a hmem
  unfold createRest at h
  obtain ⟨m1, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨m2, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨st, h3, h⟩ := Base.bind_ok_iff.mp h
  have hs2 : m2.state = g.state :=
    (chargeGas_sameContext h2).state.trans (chargeStateGas_sameContext h1).state
  have hst : a ∈ st.accountReads := by
    rw [(State.TransactionState.reads_incrementNonce (Base.mapError_ok_iff.mp h3)).1]
    rw [hs2]
    simp [Std.ExtTreeSet.mem_insert, hmem]
  dsimp only at h
  split at h
  · cases h
    exact hst
  · obtain ⟨m4, h4, h⟩ := Base.bind_ok_iff.mp h
    cases h
    change a ∈ m4.state.accountReads
    rw [(pushWord_sameContext h4).state]
    exact hst

/-- A creation that has read its sender gives agreeing runs from agreeing frames. -/
private theorem launchFrom_sim {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2)
    (hcurrent : account g1.message.currentTarget)
    (hcandidates : CandidatesIn account allStorage g1.state) (value : Base.U256)
    (initCode : ByteArray) (salt : Option Base.U256) :
    Sim account allStorage slot code (launchFrom value initCode salt g1)
      (launchFrom value initCode salt g2) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  have hsender : s.getAccount g1.message.currentTarget =
      g1.state.getAccount g1.message.currentTarget := hrel.state.getAccount_eq (.inr hcurrent)
  unfold launchFrom
  dsimp only
  rw [hsender]
  by_cases fails : (g1.state.getAccount g1.message.currentTarget).balance < value ∨
      (g1.state.getAccount g1.message.currentTarget).nonce = MAX_NONCE ∨
      g1.message.depth + 1 > STACK_DEPTH_LIMIT
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true fails)]
    exact Sim.of_rel (skipCall_rel hrel 0 0)
  simp only [ite_eq_right_of_eq_false _ _ (eq_false fails)]
  cases creationAddress g1.message.currentTarget
    (g1.state.getAccount g1.message.currentTarget).nonce salt initCode with
  | error e => exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  | ok address =>
    rw [exceptOk_bind, exceptOk_bind, accessAddress_withState g1 s address]
    dsimp only
    have hqs : (accessAddress g1 address).2.state = g1.state := state_accessAddress _ _
    have hqm : (accessAddress g1 address).2.message = g1.message := accessAddress_message _ _
    have hframe : FrameAgrees account allStorage slot code
        (recordAccountRead (accessAddress g1 address).2 address)
        (recordAccountRead { (accessAddress g1 address).2 with state := s } address) :=
      ⟨rfl, by simp only [recordAccountRead, hqs]; exact hrel.state.recordAccountRead _⟩
    have hcand' : CandidatesIn account allStorage
        (recordAccountRead (accessAddress g1 address).2 address).state := by
      simp only [recordAccountRead, hqs]
      exact hcandidates
    refine ⟨fun err h nab => ?_, fun r1 h reads => ?_⟩
    · rw [(keepReads_eq_error.mp h).2] at nab
      cases nab
    · have hmem : address ∈ r1.state.accountReads := by
        have hself : address ∈
            (recordAccountRead (accessAddress g1 address).2 address).state.accountReads := by
          simp [recordAccountRead, State.TransactionState.recordAccountRead,
            Std.ExtTreeSet.mem_insert]
        rcases keepReads_eq_ok h with h' | ⟨e, rfl⟩
        · exact createRest_reads h' _ hself
        · exact hself
      exact (keepReads_sim hframe (Sim.of_rel (createRest_rel hframe hcurrent
        (reads.account _ hmem) hcand' value initCode))).2 r1 h reads

/-- A creation that has passed its checks gives agreeing runs from agreeing frames. -/
private theorem launchCreate_sim {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2)
    (hcurrent : account g1.message.currentTarget)
    (hcandidates : CandidatesIn account allStorage g1.state) (value : Base.U256)
    (initCode : ByteArray) (salt : Option Base.U256) :
    Sim account allStorage slot code (launchCreate g1 value initCode salt)
      (launchCreate g2 value initCode salt) := by
  obtain ⟨s, rfl⟩ : ∃ s, g2 = { g1 with state := s } := ⟨_, hrel.rest⟩
  rw [launchCreate_eq, launchCreate_eq]
  exact launchFrom_sim (g1 := recordAccountRead { g1 with returnData := .empty }
      g1.message.currentTarget)
    (g2 := recordAccountRead { g1 with state := s, returnData := .empty }
      g1.message.currentTarget)
    ⟨rfl, hrel.state.recordAccountRead _⟩ hcurrent hcandidates value initCode salt

/-- A creation that has paid checks its frame, then gives agreeing runs. -/
private theorem genericCreate_sim {g1 g2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code g1 g2)
    (hcurrent : account g1.message.currentTarget)
    (hcandidates : CandidatesIn account allStorage g1.state) (value : Base.U256)
    (initCode : ByteArray) (salt : Option Base.U256) :
    Sim account allStorage slot code (genericCreate g1 value initCode salt)
      (genericCreate g2 value initCode salt) := by
  have hm : g2.message = g1.message := by rw [hrel.rest]
  unfold genericCreate
  rw [hm]
  split
  · exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  split
  · exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  exact launchCreate_sim hrel hcurrent hcandidates value initCode salt

/-- The part of a creation before its checks.

It refuses a static frame, pops the operands, pays, and reads the init code. -/
private def createPay (create2 : Bool) (evm : Evm fork Meter) :
    Except EvmError ((Base.U256 × ByteArray × Option Base.U256) × Evm fork Meter) := do
  if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
  let (value, evm) ← popWord evm
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let (salt, evm) ← popSalt create2 evm
  let hashCost := if create2 then GasCosts.OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0
  let initCost := if fork ≥ .shapella then initCodeCost size.toNat else 0
  let evm ← chargeGasAndMemory evm (createBaseCost fork + hashCost + initCost) [(start, size)]
  return ((value, memoryReadBytes evm.memory start.toNat size.toNat, salt), evm)

/-- A creation pays, then checks and launches. -/
private theorem createStep_eq (create2 : Bool) (evm : Evm fork Meter) :
    createStep create2 evm =
      createPay create2 evm >>= fun x => genericCreate x.2 x.1.1 x.1.2.1 x.1.2.2 := by
  unfold createStep createPay
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    rfl
  · simp only [ite_eq_right_of_eq_false _ _ (eq_false hs), bind_assoc, pure_bind]

omit [GasMeter Meter] in
/-- The pop of a salt moves a replaced state through unchanged. -/
private theorem popSalt_withState (create2 : Bool) (evm : Evm fork Meter)
    (other : TransactionState) :
    popSalt create2 { evm with state := other } =
      (fun p => (p.1, { p.2 with state := other })) <$> popSalt create2 evm := by
  cases create2 <;>
    simp only [popSalt, Bool.false_eq_true, ↓reduceIte, popWord_withState, bind_map_left,
      map_bind, map_pure] <;> rfl

/-- The payment of a creation moves a replaced state through unchanged. -/
private theorem createPay_withState (create2 : Bool) (evm : Evm fork Meter)
    (other : TransactionState) :
    createPay create2 { evm with state := other } =
      (fun x => (x.1, { x.2 with state := other })) <$> createPay create2 evm := by
  unfold createPay
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    rfl
  · simp only [ite_eq_right_of_eq_false _ _ (eq_false hs), popWord_withState, popSalt_withState,
      chargeGasAndMemory_withState, bind_map_left, map_bind, map_pure]

/-- The payment of a creation keeps the context of the frame. -/
private theorem createPay_sameContext {create2 : Bool} {evm : Evm fork Meter}
    {x : (Base.U256 × ByteArray × Option Base.U256) × Evm fork Meter}
    (h : createPay create2 evm = .ok x) : SameContext evm x.2 := by
  unfold createPay at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [ite_eq_left_of_eq_true _ _ (eq_true hs)] at h
    cases h
  simp only [ite_eq_right_of_eq_false _ _ (eq_false hs)] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  cases h
  exact ((((popWord_sameContext h1).trans (popWord_sameContext h2)).trans
    (popWord_sameContext h3)).trans (popSalt_eq_ok h4).2.1).trans
    (chargeGasAndMemory_sameContext h5)

/-- A creation gives agreeing runs from agreeing frames. -/
private theorem createStep_sim {e1 e2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code e1 e2)
    (hcurrent : account e1.message.currentTarget)
    (hcandidates : CandidatesIn account allStorage e1.state) (create2 : Bool) :
    Sim account allStorage slot code (createStep create2 e1) (createStep create2 e2) := by
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  rw [createStep_eq, createStep_eq, createPay_withState create2 e1 s]
  cases hp : createPay create2 e1 with
  | error e => exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  | ok x =>
    have sc := createPay_sameContext hp
    have hframe : FrameAgrees account allStorage slot code x.2 { x.2 with state := s } :=
      ⟨rfl, by rw [sc.state]; exact hrel.state⟩
    have hcur' : account x.2.message.currentTarget := by
      rw [sc.message]
      exact hcurrent
    have hcand' : CandidatesIn account allStorage x.2.state := by
      rw [sc.state]
      exact hcandidates
    exact genericCreate_sim hframe hcur' hcand' _ _ _

/-- Each call and creation gives agreeing results when it starts from agreeing frames.

A failure that does not abort the run is the same in both frames.

A success needs the reads of the frame it gives in the sets.

Each account of the first set needs its code hash empty, written, or in the code set.

Each such account with nonce 0 and no code needs its storage wiped or in the second set.

The current account must be in the first set. -/
theorem messageInstruction_agrees {account allStorage : Address → Prop}
    {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop} {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)}
    (hrun : messageInstruction fork op = some run) {e1 e2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code e1 e2)
    (hcodes : CodesIn account code e1.state)
    (hcandidates : CandidatesIn account allStorage e1.state)
    (hcurrent : account e1.message.currentTarget) :
    (∀ err, run e1 = .error err → err.aborts = false → run e2 = .error err) ∧
      ∀ r1, run e1 = .ok r1 → ReadsIn account slot r1.state →
        ∃ r2, run e2 = .ok r2 ∧ StepAgrees account allStorage slot code r1 r2 := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    cases op <;> simp only [callInstruction, Option.some.injEq, reduceCtorEq] at hc
    all_goals first
      | (subst hc; exact callStep_sim hrel hcodes hcurrent _)
      | (split at hc
         · simp only [Option.some.injEq] at hc
           subst hc
           exact callStep_sim hrel hcodes hcurrent _
         · cases hc)
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
    all_goals first
      | (subst hrun; exact createStep_sim hrel hcurrent hcandidates _)
      | (split at hrun
         · simp only [Option.some.injEq] at hrun
           subst hrun
           exact createStep_sim hrel hcurrent hcandidates _
         · cases hrun)

/-- Each step gives agreeing results when it starts from agreeing frames.

It covers every opcode: those of the instruction table, the calls and the creations.

It adds the condition on accounts with nonce 0 and no code to those of an instruction. -/
theorem step_agrees {account allStorage : Address → Prop}
    {slot : Address → Bytes32 → Prop} {code : Hash32 → Prop} {e1 e2 : Evm fork Meter}
    (hrel : FrameAgrees account allStorage slot code e1 e2)
    (hcodes : CodesIn account code e1.state)
    (hcandidates : CandidatesIn account allStorage e1.state)
    (hcurrent : account e1.message.currentTarget) :
    (∀ err, step fork e1 = .error err → err.aborts = false → step fork e2 = .error err) ∧
      ∀ r1, step fork e1 = .ok r1 → ReadsIn account slot r1.state →
        ∃ r2, step fork e2 = .ok r2 ∧ StepAgrees account allStorage slot code r1 r2 := by
  obtain ⟨s, rfl⟩ : ∃ s, e2 = { e1 with state := s } := ⟨_, hrel.rest⟩
  unfold step
  dsimp only
  by_cases hpc : e1.pc < e1.code.size
  · simp only [hpc, dite_true]
    cases Op.ofByte fork e1.code[e1.pc] with
    | none => exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
    | some op =>
      dsimp only
      cases hi : instruction (Meter := Meter) fork op with
      | some run =>
        dsimp only
        obtain ⟨herr, hok⟩ := instruction_agrees hi hrel hcodes hcurrent
        refine ⟨fun err h nab => ?_, fun r1 h reads => ?_⟩
        · cases hr : run e1 with
          | error e =>
            rw [hr] at h
            cases h
            rw [herr _ hr nab]
            rfl
          | ok a =>
            rw [hr] at h
            cases h
        · obtain ⟨a1, ha1, rfl⟩ := Base.map_ok_iff.mp h
          obtain ⟨a2, ha2, hfr⟩ := hok a1 ha1 reads
          rw [ha2]
          exact ⟨_, rfl, hfr⟩
      | none =>
        dsimp only
        cases hm : messageInstruction (Meter := Meter) fork op with
        | some run => exact messageInstruction_agrees hm hrel hcodes hcandidates hcurrent
        | none => exact ⟨fun _ h _ => h, fun _ h => by cases h⟩
  · simp only [hpc, dite_false]
    constructor
    · intro _ h _
      cases h
    · intro r1 h _
      cases h
      exact ⟨_, rfl, rfl, hrel.state⟩

end EthLib.Execution.Evm
