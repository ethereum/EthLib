module

public import EthLib.Base.ByteOrder
public import EthLib.Base.Except
public import EthLib.Execution.Evm.Machine.Frame
public import EthLib.Execution.Evm.Gas.Memory
public import EthLib.Execution.Evm.Machine.Memory

/-!
# `Evm.Step`

The parts that every instruction is made of: pop words, charge gas, grow memory, push a word.

An instruction pops its operands first, then pays, then computes, then moves the program counter.

The gas meter is a parameter, so these parts serve every meter.

A step gives the next frame, or a message to run first, for a call.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256 ByteOrder.ofBE)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The top word of the stack, and the frame without it. -/
def popWord (evm : Evm fork Meter) : Except EvmError (U256 × Evm fork Meter) := do
  -- `mu_s[0]`, with `mu'_s[x] = mu_s[x + 1]`.
  --
  -- An empty stack is `||mu_s|| < delta_w`, so `Z` of §9.4.2 holds.
  let (x, stack) ← evm.stack.pop
  return (x, { evm with stack })

/-- The frame with a word on top of its stack. -/
def pushWord (evm : Evm fork Meter) (x : U256) : Except EvmError (Evm fork Meter) := do
  -- `mu'_s[0] = x`, and `Z` of §9.4.2 holds if `||mu_s|| - delta_w + alpha_w > 1024`.
  let stack ← evm.stack.push x
  return { evm with stack }

/-- The frame with its program counter moved by `n`. -/
def advance (evm : Evm fork Meter) (n : Nat := 1) : Evm fork Meter :=
  -- Yellow Paper §9.5: `mu'_{pc} = N(mu_{pc}, w)`, past the data of PUSH1 to PUSH32, else `+ 1`.
  --
  -- EIP-8024 adds DUPN, SWAPN and EXCHANGE, which skip their one immediate byte too.
  { evm with pc := evm.pc + n }

/-- The frame after it pays `cost` and the growth of memory for `ranges`, with memory grown.

Each range is a start and a size, as the instruction pops them. -/
def chargeGasAndMemory (evm : Evm fork Meter) (cost : Nat) (ranges : List (U256 × U256)) :
    Except EvmError (Evm fork Meter) := do
  -- `mu'_i = M(mu_i, s, f)` for each range, and its cost `C_mem(mu'_i) - C_mem(mu_i)`.
  let growth := extendMemory evm.memory.size ranges
  -- `mu'_g = mu_g - C(sigma, mu, A, I)`, where `C` adds the growth of memory.
  let evm ← chargeGas evm (cost + growth.cost)
  -- The memory grows by whole words of zeros, as §9.1 reads every location as 0.
  return { evm with memory := memoryExtend evm.memory growth.expandBy }

/-- An instruction that pays `cost`, then pushes a word that it reads from the frame. -/
def readFrame (cost : Nat) (value : Evm fork Meter → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  -- `mu'_g = mu_g - C`, then `mu'_s[0]` is a word read from the frame after the charge.
  --
  -- So GAS pushes `mu'_g`, as the text of Appendix H.2 says, where its formula reads `mu_g`.
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (value evm)
  return advance evm

/-- An instruction that pays `cost`, then pushes a number that it reads from the environment.

A number of `2^256` or more fits no word, and aborts the execution once the price is paid. -/
def readNumber (cost : Nat) (value : Evm fork Meter → Nat) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) :=
  -- The number is read from the frame before the price is paid, in both branches.
  if value evm < 2 ^ 256 then readFrame cost (fun _ => BitVec.ofNat 256 (value evm)) evm
  else do
    -- The price comes first, so a frame short of gas halts before the number becomes a word.
    let _ ← chargeGas evm cost
    throw (.wordOverflow (value evm))

/-- An instruction that pops `x`, pays `cost` and pushes `f x`. -/
def unaryOp (cost : Nat) (f : U256 → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  -- `delta_w = 1` and `alpha_w = 1`: `mu'_s[0] = f(mu_s[0])`, once `C` is paid.
  let (x, evm) ← popWord evm
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (f x)
  return advance evm

/-- An instruction that pops `x` then `y`, pays `cost` and pushes `f x y`. -/
def binaryOp (cost : Nat) (f : U256 → U256 → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  -- `delta_w = 2` and `alpha_w = 1`: `mu'_s[0] = f(mu_s[0], mu_s[1])`, once `C` is paid.
  let (x, evm) ← popWord evm
  let (y, evm) ← popWord evm
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (f x y)
  return advance evm

/-- An instruction that pops `x`, `y` then `z`, pays `cost` and pushes `f x y z`. -/
def ternaryOp (cost : Nat) (f : U256 → U256 → U256 → U256) (evm : Evm fork Meter) :
    Except EvmError (Evm fork Meter) := do
  -- `delta_w = 3` and `alpha_w = 1`: `mu'_s[0] = f(mu_s[0], mu_s[1], mu_s[2])`, once `C` is paid.
  let (x, evm) ← popWord evm
  let (y, evm) ← popWord evm
  let (z, evm) ← popWord evm
  let evm ← chargeGas evm cost
  let evm ← pushWord evm (f x y z)
  return advance evm

/-- The frame after an exceptional halt: it stops with no gas, no output and the error. -/
def exceptionalHalt (evm : Evm fork Meter) (error : EvmError) : Evm fork Meter :=
  -- Yellow Paper §9.4: when `Z` holds, `X` gives no output, and §8 leaves no gas, `g' = 0`.
  { evm with
    gas := GasMeter.exhaust evm.gas
    running := false
    output := .empty
    error := some error }

/-! ## Reads of the state

From Glamsterdam, the block access list of EIP-7928 names what each instruction reads.

An instruction records a read once it has passed the gas check that comes before it.

The read stays even when the instruction then halts. -/

/-- The frame once it records a read of the account at an address. -/
def recordAccountRead (evm : Evm fork Meter) (address : Base.Address) : Evm fork Meter :=
  -- EIP-7928: the address joins the block access list.
  { evm with state := evm.state.recordAccountRead address }

/-- The frame once it records a read of a key of the storage of an address. -/
def recordStorageRead (evm : Evm fork Meter) (address : Base.Address) (key : Base.Bytes32) :
    Evm fork Meter :=
  -- EIP-7928: the key joins the storage reads of the address, at most once.
  { evm with state := evm.state.recordStorageRead address key }

/-- From Glamsterdam, fail with out of gas when the frame has less than `amount` gas left.

It charges nothing, and it passes before Glamsterdam.

From Glamsterdam, an instruction checks the price it knows before it reads the state. -/
def checkGas (evm : Evm fork Meter) (amount : Nat) : Except EvmError Unit :=
  -- EIP-7928, Gas Validation Before State Access: out of gas if the gas left is below `amount`.
  if fork ≥ .glamsterdam ∧ GasMeter.gasLeft evm.gas < amount then throw .outOfGas else pure ()

/-- The result of the rest of an instruction, from the frame `evm` that has read the state.

When the rest halts the frame, the frame halts with its reads, and `halted` makes the result.

An error that aborts the whole execution stays an error. -/
def keepReads {α : Type} (evm : Evm fork Meter) (halted : Evm fork Meter → α)
    (rest : Except EvmError α) : Except EvmError α :=
  match rest with
  -- EIP-7928: a halt keeps the reads that the frame made before it.
  --
  -- An error that aborts the run is no halt of the frame.
  | .error e => if e.aborts then .error e else .ok (halted (exceptionalHalt evm e))
  | .ok result => .ok result

/-- The rest of an instruction that keeps its reads gives its own result, or a halted frame. -/
theorem keepReads_eq_ok {α : Type} {evm : Evm fork Meter} {halted : Evm fork Meter → α}
    {rest : Except EvmError α} {result : α} (h : keepReads evm halted rest = .ok result) :
    rest = .ok result ∨ ∃ e, result = halted (exceptionalHalt evm e) := by
  unfold keepReads at h
  split at h
  · split at h
    · cases h
    · cases h
      exact .inr ⟨_, rfl⟩
  · cases h
    exact .inl rfl

/-- What one step of a frame gives. -/
inductive StepResult (fork : Fork) (Meter : Type) where
  /-- The frame after the step. -/
  | next (evm : Evm fork Meter)
  /-- A message to run first, from the frame `caller`.

  The frame goes on with `resume` applied to the frame that ends the message. -/
  | child (caller : Evm fork Meter) (message : Message fork)
      (resume : Evm fork Meter → Except EvmError (Evm fork Meter))

end EthLib.Execution.Evm
