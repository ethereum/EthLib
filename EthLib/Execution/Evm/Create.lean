module

public import EthLib.Execution.Evm.Call
public import EthLib.Execution.Evm.ContractAddress

/-!
# `Evm.Create`

The two instructions that create a contract: CREATE and CREATE2.

A creation pops its value, the range of its init code and, for CREATE2, a salt.

It pays 32000, the growth of memory, and from Shanghai 2 gas per word of init code.

CREATE2 also pays 6 gas per word to hash the init code.

From Tangerine Whistle, it passes on all but one 64th of the gas left, and before, all of it.

A frame that lacks the value, at the greatest depth, or with the greatest nonce runs no message.

It gets back that gas, and pushes 0.

An address with code or a nonce takes that gas and pushes 0, and the frame's nonce still grows.

An address with storage alone is not a collision: the creation wipes that storage first.

[EIP-7610][eip7610], in Last Call, would make such a creation fail, at every fork back to Frontier.

It is not applied here: [execution-specs][es-7610] removed it at every fork in commit `2ce2191`.

That commit precedes the commit that made the state tests that EthLib runs.

Otherwise the frame's nonce grows and the init code runs at the new address.

The caller pushes the new address on success, and 0 on failure with the output as return data.

A creation sends a message with less gas than it has, so it lowers the measure of the frame.

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

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip211]: https://eips.ethereum.org/EIPS/eip-211#specification
[eip214]: https://eips.ethereum.org/EIPS/eip-214#specification
[eip684]: https://eips.ethereum.org/EIPS/eip-684#specification
[eip1014]: https://eips.ethereum.org/EIPS/eip-1014#specification
[eip2681]: https://eips.ethereum.org/EIPS/eip-2681#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip3860]: https://eips.ethereum.org/EIPS/eip-3860#specification
[eip7610]: https://eips.ethereum.org/EIPS/eip-7610#specification
[es-7610]: https://github.com/ethereum/execution-specs/commit/2ce2191562f76ec6e64a82f82165d821e1c781fc
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
  if fork ≥ .tangerineWhistle then maxMessageCallGas gasLeft else gasLeft

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

On failure it pushes 0, and the output of the child becomes the return data. -/
def resumeCreate (fork : Fork) (caller : Evm fork Meter) (address : Address)
    (child : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, returnData) :=
    if child.error.isNone then (address.toU256, ByteArray.empty) else (0, child.output)
  let evm ← pushWord { incorporateChild fork caller child with returnData } word
  return advance evm

/-- The step of a creation that has paid, and kept `gas` for its message.

It runs no message when the frame lacks the value, is too deep, or has the greatest nonce.

Otherwise it accesses the new address, and the nonce of the frame grows by one.

An address with code or a nonce gets no message.

Otherwise the frame passes on its whole reservoir to the message. -/
def launchCreate (evm : Evm fork Meter) (gas : Nat) (value : U256) (initCode : ByteArray)
    (salt : Option U256) : Except EvmError (StepResult fork Meter) :=
  let evm := { evm with returnData := .empty }
  let current := evm.message.currentTarget
  let sender := evm.state.getAccount current
  if sender.balance < value ∨ sender.nonce = MAX_NONCE ∨
      evm.message.depth + 1 > STACK_DEPTH_LIMIT then
    .next <$> skipCall evm gas 0
  else do
    let address ← creationAddress current sender.nonce salt initCode
    let evm := (accessAddress evm address).2
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
      .ok (.child evm message (resumeCreate fork evm address))
    else do
      let evm ← pushWord evm 0
      return .next (advance evm)

/-- The step of a creation once it has paid its price and grown memory.

From Shanghai, init code longer than the limit fails.

It keeps the gas of the message, and fails in a static frame. -/
def genericCreate (evm : Evm fork Meter) (value : U256) (initCode : ByteArray)
    (salt : Option U256) : Except EvmError (StepResult fork Meter) :=
  if fork ≥ .shapella ∧ maxInitCodeSize fork < initCode.size then .error .outOfGas
  else
    let gas := createMessageGas fork (GasMeter.gasLeft evm.gas)
    match chargeGas evm gas with
    | .error e => .error e
    | .ok evm =>
      if evm.message.isStatic then .error .writeInStaticContext
      else launchCreate evm gas value initCode salt

/-- The step of CREATE, or of CREATE2 when `create2` holds.

It pays its price and the growth of memory, then reads the init code from memory. -/
def createStep (create2 : Bool) (evm : Evm fork Meter) :
    Except EvmError (StepResult fork Meter) := do
  let (value, evm) ← popWord evm
  let (start, evm) ← popWord evm
  let (size, evm) ← popWord evm
  let (salt, evm) ← popSalt create2 evm
  let hashCost := if create2 then OPCODE_KECCAK256_PER_WORD * wordCount size.toNat else 0
  let initCost := if fork ≥ .shapella then initCodeCost size.toNat else 0
  let evm ← chargeGasAndMemory evm (OPCODE_CREATE_BASE + hashCost + initCost) [(start, size)]
  genericCreate evm value (memoryReadBytes evm.memory start.toNat size.toNat) salt

/-- The instruction of a creation opcode at fork `fork`.

Other opcodes give none, and so does CREATE2 before Constantinople. -/
def createInstruction (fork : Fork) :
    Op → Option (Evm fork Meter → Except EvmError (StepResult fork Meter))
  | .create => some (createStep false)
  | .create2 => if .constantinople ≤ fork then some (createStep true) else none
  | _ => none

/-- The instruction of an opcode at fork `fork` that may send a message: a call or a creation. -/
def messageInstruction (fork : Fork) (op : Op) :
    Option (Evm fork Meter → Except EvmError (StepResult fork Meter)) :=
  callInstruction fork op <|> createInstruction fork op

/-! ## Each creation lowers the measure of the frame -/

/-- A message with less gas than the frame paid, and a resume that adds the child's gas, decrease.

The resume must give the gas that the caller and the child hold, and keep the caller running. -/
theorem child_decreases [LawfulGasMeter Meter] {before caller : Evm fork Meter}
    {message : Message fork} {resume : Evm fork Meter → Except EvmError (Evm fork Meter)}
    {cost : Nat} (paid : Pays cost before caller) (lt : message.gas < cost)
    (running : before.running = true)
    (resumes : ∀ {child after}, resume child = .ok after →
      GasMeter.gasHeld after.gas = GasMeter.gasHeld caller.gas + GasMeter.gasHeld child.gas ∧
        after.running = caller.running) :
    (StepResult.child caller message resume).Decreases before := by
  have := paid.gasHeld
  refine ⟨by omega, fun child after used resumed => ?_⟩
  obtain ⟨g, r⟩ := resumes resumed
  exact Pays.measure_lt ⟨by omega, r.trans paid.running⟩ running

/-- The caller gets back exactly the gas that the child of a creation holds, and keeps running. -/
theorem resumeCreate_gasHeld [LawfulGasMeter Meter] {caller child after : Evm fork Meter}
    {address : Address} (h : resumeCreate fork caller address child = .ok after) :
    GasMeter.gasHeld after.gas = GasMeter.gasHeld caller.gas + GasMeter.gasHeld child.gas ∧
      after.running = caller.running := by
  obtain ⟨_, h1, h⟩ := except_bind_eq_ok h
  cases h
  obtain ⟨_, -, h1⟩ := except_bind_eq_ok h1
  cases h1
  exact ⟨gasHeld_incorporateChild caller child, running_incorporateChild caller child⟩

/-- A creation that paid more than the gas of its message lowers the measure. -/
theorem launchCreate_decreases [LawfulGasMeter Meter] {before evm : Evm fork Meter}
    {gas cost : Nat} {value : U256} {initCode : ByteArray} {salt : Option U256}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (lt : gas < cost)
    (running : before.running = true)
    (h : launchCreate evm gas value initCode salt = .ok result) : result.Decreases before := by
  unfold launchCreate at h
  dsimp only at h
  split at h
  · cases hs : skipCall { evm with returnData := .empty } gas 0 with
    | error => simp [hs, Functor.map, Except.map] at h
    | ok after =>
      simp only [hs, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      refine skipCall_measure_lt ?_ lt running hs
      exact paid.congr rfl rfl
  · obtain ⟨address, -, h⟩ := except_bind_eq_ok h
    obtain ⟨state, -, h⟩ := except_bind_eq_ok h
    have access := accessAddress_pays { evm with returnData := .empty } address
    have paid' : Pays cost before
        { (accessAddress { evm with returnData := .empty } address).2 with state } :=
      (((paid.congr rfl rfl : Pays cost before { evm with returnData := .empty }).trans
        access).mono (by omega)).congr rfl rfl
    split at h
    · cases h
      exact child_decreases paid'.drain lt running resumeCreate_gasHeld
    · obtain ⟨_, hp, h⟩ := except_bind_eq_ok h
      cases h
      show measure _ < measure before
      exact Pays.measure_lt
        (((paid'.trans (pushWord_pays hp)).mono (by omega)).congr rfl rfl) running

/-- A creation that paid at least 1 gas lowers the measure. -/
theorem genericCreate_decreases [LawfulGasMeter Meter] {before evm : Evm fork Meter}
    {cost : Nat} {value : U256} {initCode : ByteArray} {salt : Option U256}
    {result : StepResult fork Meter} (paid : Pays cost before evm) (pos : 0 < cost)
    (running : before.running = true)
    (h : genericCreate evm value initCode salt = .ok result) : result.Decreases before := by
  unfold genericCreate at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · rename_i charged hc
      split at h
      · cases h
      · exact launchCreate_decreases (paid.trans (chargeGas_pays hc)) (by omega) running h

/-- The pop of the salt pays nothing. -/
theorem popSalt_pays {create2 : Bool} {evm after : Evm fork Meter} {salt : Option U256}
    (h : popSalt create2 evm = .ok (salt, after)) : Pays 0 evm after := by
  unfold popSalt at h
  split at h
  · obtain ⟨⟨_, _⟩, hp, h⟩ := except_bind_eq_ok h
    cases h
    exact popWord_pays hp
  · cases h
    exact .of_eq rfl rfl

/-- Each creation lowers the measure of a running frame. -/
theorem createStep_decreases [LawfulGasMeter Meter] {create2 : Bool} {evm : Evm fork Meter}
    {result : StepResult fork Meter} (running : evm.running = true)
    (h : createStep create2 evm = .ok result) : result.Decreases evm := by
  obtain ⟨⟨_, e1⟩, h1, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e2⟩, h2, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e3⟩, h3, h⟩ := except_bind_eq_ok h
  obtain ⟨⟨_, e4⟩, h4, h⟩ := except_bind_eq_ok h
  obtain ⟨e5, h5, h⟩ := except_bind_eq_ok h
  have paid := ((((popWord_pays h1).trans (popWord_pays h2)).trans (popWord_pays h3)).trans
    (popSalt_pays h4)).trans (chargeGasAndMemory_pays h5)
  refine genericCreate_decreases paid ?_ running h
  simp only [OPCODE_CREATE_BASE]
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
