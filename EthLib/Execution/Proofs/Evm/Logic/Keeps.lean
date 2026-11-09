module

public import EthLib.Execution.Proofs.Evm.Logic.Route
public import EthLib.Execution.Proofs.State.Frame

/-!
# Proofs: an assumption on what the messages of a named set do to the state

A triple under an assumption says about a frame that ends a message only what the assumption says.

The assumption here says what the messages of a named set do to the state.

Take each such message that the runner ends with no error.

The relation holds from the state of the frame that sends it to the state of the frame that ends it.

One set names the CALLs with no value that a code makes to an address.

Such a call runs the code that the address holds in a state, along its route.

The state of the frame that sends it reads as that state.

It has the same accounts, current storage and code.

So the message runs the real code of the address, or its precompile, and not any code.

The message of a CALL along a route is in that set, with the state before the call.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Logic

open EthLib.Base (Fork Address)
open State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-! ## A state that reads as another -/

/-- The state `tx` reads as the state `S`.

It has the account, the storage and the transient storage of `S` at every address.

It has the code of `S` at every code hash.

The two may differ in the reads that they record.

They may also differ in the block before the transaction.

And they may differ in the accounts that the transaction created and the storage that it wiped.

So the original storage and the account before the transaction may differ. -/
def ReadsAs (tx S : TransactionState) : Prop :=
  TransactionState.SameOutside [] S tx ∧ ∀ codeHash, tx.getCode codeHash = S.getCode codeHash

/-- A state reads as itself. -/
theorem ReadsAs.refl (S : TransactionState) : ReadsAs S S :=
  ⟨TransactionState.SameOutside.refl [] S, fun _ => rfl⟩

/-- A state that reads as one that reads as `S` reads as `S`. -/
theorem ReadsAs.trans {tx tx' S : TransactionState} (h : ReadsAs tx tx') (h' : ReadsAs tx' S) :
    ReadsAs tx S :=
  ⟨h'.1.trans h.1, fun codeHash => (h.2 codeHash).trans (h'.2 codeHash)⟩

/-- A record of an account read keeps a state that reads as `S`. -/
theorem ReadsAs.recordAccountRead {tx S : TransactionState} (h : ReadsAs tx S)
    (address : Address) : ReadsAs (tx.recordAccountRead address) S :=
  (show ReadsAs (tx.recordAccountRead address) tx from
    ⟨TransactionState.sameOutside_recordAccountRead tx address, fun _ => rfl⟩).trans h

/-- A record of a storage read keeps a state that reads as `S`. -/
theorem ReadsAs.recordStorageRead {tx S : TransactionState} (h : ReadsAs tx S)
    (address : Address) (key : EthLib.Base.Bytes32) :
    ReadsAs (tx.recordStorageRead address key) S :=
  (show ReadsAs (tx.recordStorageRead address key) tx from
    ⟨TransactionState.sameOutside_recordStorageRead tx address key, fun _ => rfl⟩).trans h

/-- Following a route keeps a state that reads as `S`. -/
theorem ReadsAs.routeState {tx S : TransactionState} (h : ReadsAs tx S) (route : Route) :
    ReadsAs (Logic.routeState tx route) S := by
  rcases route with _ | ⟨d, _⟩
  · exact h
  · exact h.recordAccountRead d

/-- A state that reads as `S` gives each code the route that `S` gives it. -/
theorem Routes.of_readsAs {tx S : TransactionState} {c : ByteArray} {route : Route}
    (h : Routes fork S c route) (hreads : ReadsAs tx S) : Routes fork tx c route :=
  h.congr fun a => by
    rw [hreads.2, TransactionState.getAccount, TransactionState.getAccount,
      (hreads.1 a List.not_mem_nil).1]

/-! ## The calls that a code makes to an address -/

/-- `msg` is a CALL with no value to `to`, along the route that `S` gives, from the frame `caller`.

The current account of `message` makes the call, from a frame whose state reads as `S`.

The message runs the code that `to` holds in `S`, along its route.

It has the depth, the static flag, the block and the transaction of a call from `message`.

Its data, its gas and its reservoir may be any.

So may the frame `caller`, apart from its state. -/
def SentVia (message : Message fork) (S : TransactionState) (to : Address)
    (caller : Evm fork Meter) (msg : Message fork) : Prop :=
  ∃ c route, S.getCode (S.getAccount to).codeHash = .ok c ∧ Routes fork S c route ∧
    ReadsAs caller.state S ∧
    msg.caller = message.currentTarget ∧ msg.currentTarget = to ∧ msg.target = some to ∧
    msg.codeAddress = some (routeAddr to route) ∧ msg.code = routeCode c route ∧
    msg.disablePrecompiles = route.isSome ∧ msg.value = 0 ∧ msg.shouldTransferValue = true ∧
    msg.depth = message.depth + 1 ∧ msg.isStatic = message.isStatic ∧
    msg.blockEnv = message.blockEnv ∧ msg.txEnv = message.txEnv

/-- The message of a CALL along a route is a call to its address via the state before the call.

The state `state` before the call holds the code of the address, and the route goes from it.

So the message is sent via that state, from the frame that the call leaves. -/
theorem CallSends.sentVia {message : Message fork} {memory : ByteArray} {gas : Nat}
    {state : TransactionState} {substate : Substate}
    {asked to inputStart inputSize outputStart outputSize : EthLib.Base.U256}
    {calleeCode : ByteArray} {route : Route} {caller : Evm fork Nat} {msg : Message fork}
    (hcode : state.getCode (state.getAccount (EthLib.Base.toAddressMasked to)).codeHash =
      .ok calleeCode)
    (hroute : Routes fork state calleeCode route)
    (h : CallSends .call message memory gas state substate asked to inputStart inputSize
      outputStart outputSize calleeCode route caller msg) :
    SentVia message state (EthLib.Base.toAddressMasked to) caller msg := by
  obtain ⟨hstate, -, -, -, m1, m2, m3, m4, m5, m6, -, m7, m8, m9, m10, m11, m12⟩ := h
  refine ⟨calleeCode, route, hcode, hroute, ?_, by simpa using m1, by simpa using m2,
    by simpa using m3, m4, m5, m6, by simpa using m7, by rw [m8]; rfl, m9, by rw [m10]; rfl,
    m11, m12⟩
  rw [hstate]
  exact (((ReadsAs.refl state).recordAccountRead _).routeState route).recordAccountRead _

/-! ## What the messages of a set do to the state -/

/-- Each message of `S` that the runner ends with no error keeps the relation `R`.

`R` holds from the state of the frame that sends the message to the state of the frame that ends it.

It is an assumption on the runner, and so on the code that each message of `S` runs. -/
def KeepsOn {bound : Nat} (runChild : MessageRunner fork Meter bound)
    (S : Evm fork Meter → Message fork → Prop) (R : TransactionState → TransactionState → Prop) :
    Prop :=
  MeetsOk (fun caller message child => S caller message → child.error = none →
    R caller.state child.state) runChild

/-- A smaller set of messages and a weaker relation keep the assumption. -/
theorem KeepsOn.mono {bound : Nat} {runChild : MessageRunner fork Meter bound}
    {S S' : Evm fork Meter → Message fork → Prop}
    {R R' : TransactionState → TransactionState → Prop} (h : KeepsOn runChild S R)
    (smaller : ∀ caller message, S' caller message → S caller message)
    (weaker : ∀ tx tx', R tx tx' → R' tx tx') : KeepsOn runChild S' R' :=
  fun caller message lt ended ran hS halted =>
    weaker _ _ (h caller message lt ended ran (smaller caller message hS) halted)

/-- A runner that keeps the block of the state keeps it on every set of messages. -/
theorem _root_.EthLib.Execution.Evm.KeepsParent.keepsOn {bound : Nat}
    {runChild : MessageRunner fork Meter bound}
    (h : KeepsParent runChild) (S : Evm fork Meter → Message fork → Prop) :
    KeepsOn runChild S fun tx tx' => tx'.parent = tx.parent :=
  fun caller message lt ended ran _ _ => h caller message lt ended ran

end EthLib.Execution.Evm.Logic
