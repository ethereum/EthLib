module

public import EthLib.Execution.Evm.Call.Child
public import EthLib.Execution.Evm.Call.Instructions
public import EthLib.Execution.Evm.Call.ContractAddress

/-!
# `Evm.Call.Create`

The two instructions that create a contract: CREATE and CREATE2.

Appendix H.2 of the Yellow Paper, Shanghai version, defines both instructions.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that add or change an instruction define it:

- [EIP-150][eip150], all but one 64th of the gas
- [EIP-211][eip211], the return data of a creation
- [EIP-214][eip214], no creation in a static frame
- [EIP-684][eip684], no creation at an address with code or a nonce
- [EIP-1014][eip1014], CREATE2
- [EIP-2681][eip2681], the greatest nonce
- [EIP-2929][eip2929], the access to the new address
- [EIP-3860][eip3860], the price and the limit of init code
- [EIP-7610][eip7610], no creation at an address with storage, in Last Call
- [EIP-8037][eip8037], the state gas of a new account, in Last Call
- [EIP-8038][eip8038], the price of a creation, in Last Call

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip211]: https://eips.ethereum.org/EIPS/eip-211#specification
[eip214]: https://eips.ethereum.org/EIPS/eip-214#specification
[eip684]: https://eips.ethereum.org/EIPS/eip-684#specification
[eip1014]: https://eips.ethereum.org/EIPS/eip-1014#specification
[eip2681]: https://eips.ethereum.org/EIPS/eip-2681#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip3860]: https://eips.ethereum.org/EIPS/eip-3860#specification
[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-new-accounts
[eip8038]: https://eips.ethereum.org/EIPS/eip-8038#createcreate2
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The greatest nonce of an account, `2^64 - 1`, by EIP-2681. -/
def MAX_NONCE : Nat := 2 ^ 64 - 1

/-- The gas that a creation passes on at fork `fork`, from the gas left after it pays.

From Tangerine Whistle, it is all but one 64th of that gas, and before, all of it. -/
def createMessageGas (fork : Fork) (gasLeft : Nat) : Nat :=
  -- `L(mu_g)`, all but one 64th, by EIP-150; before, `mu_g` itself.
  if fork ≥ .tangerineWhistle then maxMessageCallGas gasLeft else gasLeft

/-- The price of a creation at fork `fork`, before memory, init code and the hash of CREATE2.

It is 32000 up to BPO5.

From Glamsterdam, it is the access and the write of the new account, 12000, by EIP-8038. -/
def createBaseCost (fork : Fork) : Nat :=
  (gasSchedule fork).CREATE_BASE

/-- The state gas that a creation pays for the account at `address`, at fork `fork`.

From Glamsterdam, it is the state gas of a new account when the address is dead, by EIP-8037.

Before Glamsterdam, it is 0. -/
def createNewAccountStateGas (fork : Fork) (state : State.TransactionState) (address : Address) :
    Nat :=
  if fork ≥ .glamsterdam ∧ ¬state.isAccountAlive address then NEW_ACCOUNT_STATE_GAS else 0

/-- The salt that CREATE2 pops, or none for CREATE. -/
def popSalt (create2 : Bool) (evm : Evm fork Meter) :
    Except EvmError (Option U256 × Evm fork Meter) :=
  if create2 then do
    let (salt, evm) ← popWord evm
    return (some salt, evm)
  else .ok (none, evm)

/-- The address that `sender` creates at its nonce, with the salt of CREATE2 or none for CREATE.

CREATE hashes the sender and its nonce, and CREATE2 the sender, the salt and the init code. -/
def creationAddress (sender : Address) (nonce : Nat) (salt : Option U256) (initCode : ByteArray) :
    Except EvmError Address :=
  match salt with
  | some salt => .ok (create2Address sender salt initCode)
  | none => (createAddress sender nonce).mapError .encoding

/-- The calling frame `caller` once the creation of `address` ends with the frame `child`.

On success it pushes the address, and the return data is empty.

On failure it pushes 0, and the output of the child becomes the return data.

It then gets back the `newAccount` state gas that it paid, since no account was created. -/
def resumeCreate (fork : Fork) (caller : Evm fork Meter) (newAccount : Nat) (address : Address)
    (child : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- On success, the creation pushes the address of the new account, and the return data is empty.
  --
  -- On failure, it pushes 0, and the output of the child becomes the return data.
  let (word, returnData) :=
    if child.error.isNone then (address.toU256, ByteArray.empty) else (0, child.output)
  -- The caller takes the gas left, the substate and the state of the child.
  let evm := incorporateChild fork caller child
  -- On failure, the state gas of the new account comes back, since no account was created.
  let evm := if child.error.isNone then evm else refillStateGas evm newAccount
  let evm ← pushWord { evm with returnData } word
  return advance evm

/-- The step of a creation that has paid its price.

It sends a message that runs the init code at the new address, or pushes 0 when it cannot. -/
def launchCreate (evm : Evm fork Meter) (value : U256) (initCode : ByteArray)
    (salt : Option U256) : Except EvmError (StepResult fork Meter) :=
  -- The return data becomes empty.
  let evm := { evm with returnData := .empty }
  -- The account of the sender, the current target, is read first, by EIP-7928.
  let current := evm.message.currentTarget
  let evm := recordAccountRead evm current
  let sender := evm.state.getAccount current
  -- The creation pushes 0, sends no message and keeps its gas when one of three conditions holds.
  --
  -- The balance of the sender is below the value.
  --
  -- The nonce of the sender is `2^64 - 1`, by EIP-2681.
  --
  -- The depth of the message would exceed 1024.
  if sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT then
    .next <$> skipCall evm 0 0
  else do
    -- The new address, by the Yellow Paper for CREATE and by EIP-1014 for CREATE2.
    let address ← creationAddress current sender.nonce salt initCode
    -- The new address joins the accessed addresses, by EIP-2929.
    --
    -- Once the checks pass, the new address is read too, by EIP-7928.
    --
    -- That read stays even when the creation then lacks gas.
    let evm := recordAccountRead (accessAddress evm address).2 address
    keepReads evm .next do
      -- From Glamsterdam, a new address that is not alive pays the state gas of a new account.
      let newAccount := createNewAccountStateGas fork evm.state address
      -- EIP-8037 charges that state gas here.
      let evm ← chargeStateGas evm newAccount
      -- From Tangerine Whistle, the message gets all but one 64th of the gas left, by EIP-150.
      let gas := createMessageGas fork (GasMeter.gasLeft evm.gas)
      -- The frame pays the gas of the message, which the message then holds.
      let evm ← chargeGas evm gas
      -- An address with code or a nonzero nonce gets no message, by EIP-684, and 0 is pushed.
      --
      -- The nonce of the sender grows by one in that case too.
      --
      -- An address with storage gets no message either, by EIP-7610.
      --
      -- EIP-7610 applies at every fork back to Frontier.
      --
      -- The nonce grows on both branches, so it grows once here, before the branch.
      let deployable := evm.state.accountDeployable address
      let state ← (evm.state.incrementNonce fork current).mapError .state
      let evm := { evm with state }
      if deployable then
        -- The message takes the whole state gas reservoir of the frame.
        let reservoir := GasMeter.reservoir evm.gas
        let evm := { evm with gas := GasMeter.drain evm.gas }
        -- The child frame runs the init code at the new address.
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
        -- A collision keeps the grant used and pushes 0.
        --
        -- EIP-8037: on an address collision, the state gas of the new account is refilled.
        --
        -- EIP-8037 says that storage alone causes no collision.
        --
        -- With storage alone a target is a collision here, by EIP-7610, and it was charged.
        let evm ← pushWord (refillStateGas evm newAccount) 0
        return .next (advance evm)

/-- The step of a creation once it has paid its price and grown memory.

From Shanghai, init code longer than the limit fails.

It fails in a static frame. -/
def genericCreate (evm : Evm fork Meter) (value : U256) (initCode : ByteArray)
    (salt : Option U256) : Except EvmError (StepResult fork Meter) :=
  -- EIP-3860 rule 3, from Shanghai: init code over `MAX_INITCODE_SIZE` aborts the instruction.
  --
  -- It aborts as if it runs out of gas.
  if fork ≥ .shapella ∧ maxInitCodeSize fork < initCode.size then .error .outOfGas
  -- Before Glamsterdam, the static check of EIP-214 comes here.
  else if evm.message.isStatic then .error .writeInStaticContext
  else launchCreate evm value initCode salt

/-- The step of CREATE, or of CREATE2 when `create2` holds.

It pays its price and the growth of memory, then reads the init code from memory.

From Glamsterdam, it fails in a static frame before it pops its operands. -/
def createStep (create2 : Bool) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) := do
  -- From Glamsterdam, a creation in a static frame fails, before the pops.
  if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
  -- The stack gives the value, the start and the size of the init code, and the salt of CREATE2.
  let (value, evm) ← popWord evm
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let (salt, evm) ← popSalt create2 evm
  -- CREATE2 pays the hash cost, `G_keccak256word`, 6 gas per word of init code, by EIP-1014.
  let hashCost := if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0
  -- From Shanghai, EIP-3860 charges `G_initcodeword`, 2 gas per word of init code.
  --
  -- EIP-3860 rule 4 charges it before the computation of the new address.
  let initCost := if fork ≥ .shapella then initCodeCost size.toNat else 0
  -- The price of the creation, the hash, the init code and the growth of memory, in one charge.
  --
  -- Memory grows before the check of the init code limit; an abort there ends the frame either way.
  let evm ← chargeGasAndMemory evm (createBaseCost fork + hashCost + initCost) [(start, size)]
  -- The init code is the bytes of memory at that start and size.
  genericCreate evm value (memoryReadBytes evm.memory start.toNat size.toNat) salt

/-- The instruction of a creation opcode at fork `fork`.

Other opcodes give none, and so does CREATE2 before Constantinople. -/
def createInstruction (fork : Fork) :
    Op → Option (Evm fork Meter → Except EvmError (StepResult fork Meter))
  -- `0xf0` CREATE, and `0xf5` CREATE2 from Constantinople by EIP-1014.
  | .create => some (createStep false)
  | .create2 => if .constantinople ≤ fork then some (createStep true) else none
  | _ => none

/-- The instruction of an opcode at fork `fork` that may send a message: a call or a creation. -/
def messageInstruction (fork : Fork) (op : Op) :
    Option (Evm fork Meter → Except EvmError (StepResult fork Meter)) :=
  callInstruction fork op <|> createInstruction fork op

/-! ## Each creation lowers the measure of the frame

A creation sends a message with less gas than it has, so it lowers the measure of the frame. -/

/-- A message with less gas than the frame paid, and a resume that adds the child's gas, decrease.

The resume must keep the caller running, with at most the gas of the caller and the child. -/
theorem child_decreases [LawfulGasMeter Meter] {before caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {cost : Nat} (paid : Pays cost before caller) (lt : message.gas < cost)
    (running : before.running = true)
    (resumes : ∀ {child after}, resume child = .ok after →
      GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld caller.gas + GasMeter.gasHeld child.gas ∧
        after.running = caller.running) :
    (StepResult.child caller message resume).Decreases before := by
  have := paid.gasHeld
  refine ⟨by omega, fun child after used resumed => ?_⟩
  obtain ⟨g, r⟩ := resumes resumed
  exact Pays.measure_lt ⟨by omega, r.trans paid.running⟩ running

/-- The caller gets back at most the gas that the child of a creation holds, and keeps running. -/
theorem resumeCreate_gasHeld [LawfulGasMeter Meter] {caller child after : Evm fork Meter}
    {newAccount : Nat} {address : Address}
    (h : resumeCreate fork caller newAccount address child = .ok after) :
    GasMeter.gasHeld after.gas ≤ GasMeter.gasHeld caller.gas + GasMeter.gasHeld child.gas ∧
      after.running = caller.running := by
  obtain ⟨_, h1, h⟩ := Base.bind_ok_iff.mp h
  cases h
  obtain ⟨_, -, h1⟩ := Base.bind_ok_iff.mp h1
  cases h1
  have g := gasHeld_incorporateChild caller child
  have r := running_incorporateChild caller child
  dsimp only
  split
  · exact ⟨Nat.le_of_eq g, r⟩
  · exact ⟨Nat.le_trans (LawfulGasMeter.gasHeld_refill _ _) (Nat.le_of_eq g), r⟩

/-- A creation that paid at least 1 gas lowers the measure. -/
theorem launchCreate_decreases [LawfulGasMeter Meter] {before evm : Evm fork Meter}
    {cost : Nat} {value : U256} {initCode : ByteArray} {salt : Option U256}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (pos : 0 < cost)
    (running : before.running = true)
    (h : launchCreate evm value initCode salt = .ok result) : result.Decreases before := by
  unfold launchCreate at h
  dsimp only at h
  have start : Pays cost before
      (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) :=
    paid.congr rfl rfl
  split at h
  · cases hs : skipCall
        (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget) 0 0 with
    | error => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      exact skipCall_measure_lt start pos running hs
  · obtain ⟨address, -, h⟩ := Base.bind_ok_iff.mp h
    rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
    · obtain ⟨e1, h1, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
      obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
      have access := (accessAddress_pays
        (recordAccountRead { evm with returnData := .empty } evm.message.currentTarget)
        address).trans (recordAccountRead_pays _ address)
      have paid' : Pays (cost + createMessageGas fork (GasMeter.gasLeft e1.gas)) before
          { e2 with state } :=
        (((start.trans access).trans (chargeStateGas_pays h1)).trans
          (chargeGas_pays h2)).mono (by omega) |>.congr rfl rfl
      split at h
      · cases h
        exact child_decreases paid'.drain (by dsimp only; omega) running resumeCreate_gasHeld
      · obtain ⟨_, hp, h⟩ := Base.bind_ok_iff.mp h
        cases h
        show measure _ < measure before
        exact Pays.measure_lt
          ((((paid'.trans (refillStateGas_pays _ _)).trans (pushWord_pays hp)).mono
            (by omega)).congr rfl rfl) running
    · show measure _ < measure before
      rw [measure_exceptionalHalt]
      simp [measure, running]

/-- A creation that paid at least 1 gas lowers the measure. -/
theorem genericCreate_decreases [LawfulGasMeter Meter] {before evm : Evm fork Meter}
    {cost : Nat} {value : U256} {initCode : ByteArray} {salt : Option U256}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (pos : 0 < cost)
    (running : before.running = true)
    (h : genericCreate evm value initCode salt = .ok result) : result.Decreases before := by
  unfold genericCreate at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact launchCreate_decreases paid pos running h

/-- The pop of the salt pays nothing. -/
theorem popSalt_pays {create2 : Bool} {evm after : Evm fork Meter} {salt : Option U256}
    (h : popSalt create2 evm = .ok (salt, after)) : Pays 0 evm after := by
  unfold popSalt at h
  split at h
  · obtain ⟨⟨_, _⟩, hp, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact popWord_pays hp
  · cases h
    exact .of_eq rfl rfl

/-- Each creation lowers the measure of a running frame. -/
theorem createStep_decreases [LawfulGasMeter Meter] {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (running : evm.running = true)
    (h : createStep create2 evm = .ok result) : result.Decreases evm := by
  unfold createStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := Base.bind_ok_iff.mp h
  obtain ⟨e5, h5, h⟩ := Base.bind_ok_iff.mp h
  have paid := ((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (popSalt_pays h4)).trans (chargeGasAndMemory_pays h5)
  refine genericCreate_decreases paid ?_ running h
  have : 0 < createBaseCost fork := by
    unfold createBaseCost
    dsimp only [gasSchedule]
    repeat' split
    all_goals decide
  omega

/-- Each creation instruction lowers the measure of a running frame. -/
theorem createInstruction_decreases [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : createInstruction fork op = some run)
    (h : run evm = .ok result) (running : evm.running = true) : result.Decreases evm := by
  cases op <;> simp only [createInstruction, Option.some.injEq, reduceCtorEq] at hrun
  all_goals first
    | (subst hrun; exact createStep_decreases running h)
    | (split at hrun
       · simp only [Option.some.injEq] at hrun
         subst hrun
         exact createStep_decreases running h
       · cases hrun)

/-- Each instruction that may send a message lowers the measure of a running frame. -/
theorem messageInstruction_decreases [LawfulGasMeter Meter] {op : Op}
    {run : Evm fork Meter → Except EvmError (StepResult fork Meter)} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (hrun : messageInstruction fork op = some run)
    (h : run evm = .ok result) (running : evm.running = true) : result.Decreases evm := by
  unfold messageInstruction at hrun
  cases hc : callInstruction (Meter := Meter) fork op with
  | some call =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse, Option.some.injEq] at hrun
    subst hrun
    exact callInstruction_decreases hc h running
  | none =>
    simp only [hc, HOrElse.hOrElse, OrElse.orElse, Option.orElse] at hrun
    exact createInstruction_decreases hrun h running

end EthLib.Execution.Evm
