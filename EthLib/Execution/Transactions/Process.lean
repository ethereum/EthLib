module

public import EthLib.Execution.Evm.Call.ContractAddress
public import EthLib.Execution.Evm.Call.MessageCall
public import EthLib.Execution.Transactions.Authorization
public import EthLib.Execution.Transactions.Inclusion

/-!
# `Transactions.Process`

The run of a transaction that may enter its block: its message, then the settlement of its gas.

Source: section 6.2 of the Yellow Paper, Shanghai version, in [`Paper.tex` at `efc5f9a`][yp].

The step comments write its equations in ASCII.

The EIPs that change it:

- [EIP-161][eip161], the deletion of touched empty accounts
- [EIP-2929][eip2929], the accessed addresses at the start
- [EIP-2930][eip2930], the access list
- [EIP-3651][eip3651], the beneficiary accessed at the start
- [EIP-7702][eip7702], the authorizations and the delegated recipient
- [EIP-2780][eip2780], the gas that the first frame pays before its code, in Last Call
- [EIP-8037][eip8037], the reservoir of state gas, in Last Call
- [EIP-8246][eip8246], the accounts that SELFDESTRUCT marked keep their balance, in Last Call

The run records what it reads, for the block access list of EIP-7928.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip3651]: https://eips.ethereum.org/EIPS/eip-3651#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[eip2780]: https://eips.ethereum.org/EIPS/eip-2780#runtime-gas-costs
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#transaction-level-gas-accounting-reservoir-model
[eip8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
-/

@[expose] public section

namespace EthLib.Execution.Transactions

open EthLib.Base
open EthLib.Execution.Blocks (Log)
open EthLib.Execution.Evm
open EthLib.Execution.Evm.GasCosts (NEW_ACCOUNT_STATE_GAS)
open EthLib.Execution.State (BlockState EMPTY_ACCOUNT TransactionState)

/-! ## The start of the message -/

/-- The versioned hashes of the blobs of a transaction, empty unless it carries blobs. -/
def Transaction.blobHashes : Transaction → List Cryptography.Kzg.VersionedHash
  | .blob tx => tx.blobVersionedHashes
  | _ => []

/-- The addresses of the precompiles of `fork`. -/
def precompileAddresses (fork : Fork) : List Address :=
  -- The paper's `pi`: the addresses of the precompiles active at the fork.
  (Precompiles.ADDRESSES.filter (Precompiles.isPrecompile fork)).map
    fun address => toAddressMasked (BitVec.ofNat 256 address)

/-- The addresses that a message from `sender` to `target` has accessed when it starts, at `fork`.

From Berlin, [EIP-2929][eip2929] starts the message with these addresses accessed.

They include the addresses of the access list `accesses` of [EIP-2930][eip2930].

From Shapella, [EIP-3651][eip3651] adds the beneficiary `coinbase`.

[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#specification
[eip2930]: https://eips.ethereum.org/EIPS/eip-2930#specification
[eip3651]: https://eips.ethereum.org/EIPS/eip-3651#specification -/
def startAccessedAddressesOf (fork : Fork) (coinbase sender target : Address)
    (accesses : List Access) : Std.ExtTreeSet Address :=
  if fork ≥ .berlin then
    -- `A*_a = a ∪ T_t` for a call, with `a = A0_a ∪ S(T) ∪ H_c ∪_{E in T_A} {E_a}`, `A0_a = pi`.
    --
    -- The paper adds a created address later, in `Lambda`; here it is added at once, the same set.
    --
    -- The sender `S(T)`, then the target: the recipient `T_t` or the created address.
    let accessed := ((∅ : Std.ExtTreeSet Address).insert sender).insert target
    -- The precompiles, `A0_a = pi`.
    let accessed := accessed.insertMany (precompileAddresses fork)
    -- The address `E_a` of each entry `E` of the access list `T_A`.
    let accessed := accessed.insertMany (accesses.map (·.account))
    -- The beneficiary `H_c`, from Shapella by EIP-3651.
    --
    -- A set ignores the order of its insertions.
    --
    -- The warm check of the delegate, after the authorizations, sees every address of this set.
    --
    -- The Berlin paper has no `H_c`.
    if fork ≥ .shapella then accessed.insert coinbase else accessed
  -- Before Berlin, no access counts, so the set is empty.
  else ∅

/-- The addresses that a transaction has accessed when its message starts, at `fork`.

They are those of a message from `sender` to `target`, with the access list of the transaction. -/
def startAccessedAddresses (fork : Fork) (coinbase sender target : Address) (tx : Transaction) :
    Std.ExtTreeSet Address :=
  startAccessedAddressesOf fork coinbase sender target tx.accesses

/-- The storage keys that a transaction has accessed when its message starts, at `fork`.

They are the keys of its access list, from Berlin. -/
def startAccessedStorageKeys (fork : Fork) (tx : Transaction) :
    Std.ExtTreeMap Address (Std.ExtTreeSet Bytes32) :=
  if fork ≥ .berlin then
    -- `A*_K = ∪_{E in T_A} {(E_a, E_s[i]) : i < ||E_s||}`.
    tx.accesses.foldl
      (fun keys access => keys.insert access.account ((keys.getD access.account ∅).insertMany
        access.slots))
      ∅
  else ∅

/-- The substate of a transaction when its message starts: only the accesses of its start. -/
def startSubstate (fork : Fork) (coinbase sender target : Address) (tx : Transaction) :
    Substate :=
  { Substate.empty with
    accessedAddresses := startAccessedAddresses fork coinbase sender target tx
    accessedStorageKeys := startAccessedStorageKeys fork tx }

/-- The address that a transaction calls, or the address that its creation makes.

The sender is `sender`, with nonce `nonce` before the transaction. -/
def messageTarget (sender : Address) (nonce : Nat) (tx : Transaction) :
    Except EvmError Address :=
  match tx.to with
  -- A call targets its recipient `T_t`.
  | some to => .ok to
  -- A creation targets the address that the sender and its nonce give.
  --
  -- The nonce is the sender's nonce before the transaction increments it.
  | none => (createAddress sender nonce).mapError .encoding

/-- The message of a transaction from `sender` to `target`, with `gas` gas, at `fork`.

A call runs the code of its recipient on the data, and a creation runs the data as init code. -/
def transactionMessage {fork : Fork} (env : BlockEnvironment fork)
    (txEnv : TransactionEnvironment fork) (state : TransactionState) (sender target : Address)
    (gas : Nat) (tx : Transaction) : Except EvmError (Message fork) :=
  let start (data : ByteArray) (codeAddress : Option Address) (code : ByteArray) : Message fork :=
    { blockEnv := env, txEnv, caller := sender, target := tx.to, currentTarget := target, gas,
      value := tx.value, data, codeAddress, code, depth := 0, shouldTransferValue := true,
      isStatic := false, disablePrecompiles := false }
  match tx.to with
  -- A call passes the data of the transaction and runs the code of its recipient, its code address.
  | some to =>
    start tx.data (some to) <$> (state.getCode (state.getAccount to).codeHash).mapError .state
  -- A creation passes no data, runs the data of the transaction as code, and has no code address.
  | none => .ok (start .empty none tx.data)

/-! ## The message -/

/-- What the message of a transaction leaves. -/
structure CallOutput where
  /-- The state after the message. -/
  state : TransactionState
  /-- The execution gas left. -/
  gasLeft : Nat
  /-- The state gas left in the reservoir, 0 before Glamsterdam. -/
  reservoir : Nat
  /-- The gas to give back, before its cap. -/
  refund : Nat
  /-- The logs, oldest first. -/
  logs : Array Log
  /-- The logs that a simulation reports, oldest first. -/
  simulatedLogs : Array Log
  /-- The accounts to delete. -/
  accountsToDelete : Std.ExtTreeSet Address
  /-- The touched accounts, whose empty ones EIP-161 deletes. -/
  touchedAccounts : Std.ExtTreeSet Address
  /-- The error that stopped the message, if any. -/
  error : Option EvmError
  /-- The data that the message returned, or the data of its revert. -/
  output : ByteArray
  /-- The net state gas that the message used, which can be negative, and is 0 before Glamsterdam.
  -/
  stateGasUsed : Int

variable {Meter : Type} [GasMeter Meter]

/-- The output of a message that ends with the frame `evm`, with `refund` gas from before it.

A message that fails keeps its gas left and the earlier refund, and nothing else. -/
def CallOutput.ofFrame {fork : Fork} (evm : Evm fork Meter) (refund : Nat)
    (touched : Std.ExtTreeSet Address) : CallOutput :=
  let gasLeft := GasMeter.gasLeft evm.gas
  let reservoir := GasMeter.reservoir evm.gas
  let used := GasMeter.stateGasUsed evm.gas
  -- A frame that fails keeps no log and no account to delete.
  --
  -- It drops its refund counter too, which only a frame that succeeds passes on.
  if evm.error.isSome then
    ⟨evm.state, gasLeft, reservoir, refund, #[], #[], ∅, ∅, evm.error, evm.output, used⟩
  -- A frame that succeeds keeps its logs, its accounts to delete and its refund counter.
  else
    ⟨evm.state, gasLeft, reservoir, refund + evm.substate.refundCounter.toNat, evm.substate.logs,
      evm.substate.simulatedLogs, evm.substate.accountsToDelete, touched, none, evm.output, used⟩

/-- The output of a message whose first frame never runs, because of `error`.

The state stays `state`, from before the message.

No execution gas is left, the reservoir `reservoir` comes back whole, and no state gas is used. -/
def CallOutput.ofHalt (state : TransactionState) (reservoir : Nat) (error : EvmError) :
    CallOutput :=
  -- An exceptional halt while the first frame is prepared.
  --
  -- The state goes back, the reservoir comes back to its entry value, and the gas left is lost.
  ⟨state, 0, reservoir, 0, #[], #[], ∅, ∅, some error, .empty, 0⟩

/-- The first frame of a transaction, ready to run, with a gas meter of type `Meter`. -/
structure FirstFrame (fork : Fork) (Meter : Type) [GasMeter Meter] where
  /-- The message of the frame. -/
  message : Message fork
  /-- The state that the frame starts from. -/
  state : TransactionState
  /-- The substate that the frame starts from. -/
  substate : Substate
  /-- The gas that the authorizations give back. -/
  refund : Nat
  /-- The meter that the frame starts with. -/
  meter : Meter
  /-- The meter holds the gas of the message. -/
  held : GasMeter.gasHeld meter ≤ message.gas

/-- The first frame of `message`, whose meter has paid what comes before it.

The message holds the gas that the meter holds. -/
def FirstFrame.ofMeter {fork : Fork} (message : Message fork) (state : TransactionState)
    (substate : Substate) (refund : Nat) (meter : Meter) : FirstFrame fork Meter :=
  ⟨{ message with gas := GasMeter.gasHeld meter }, state, substate, refund, meter, Nat.le_refl _⟩

/-- The first frame of a transaction at `fork`, on the chain `chainId`, or the error that stops it.

Its sources:

- [EIP-684][eip684], no creation at an address with code or a nonce;
- [EIP-7610][eip7610], no creation at an address with storage;
- [EIP-7702][eip7702], the authorizations and the delegated recipient;
- [EIP-2780][eip2780], the gas that the frame pays before its code, from Glamsterdam.

An error comes with the state so far, whose reads stay, by EIP-7928.

[eip684]: https://eips.ethereum.org/EIPS/eip-684#specification
[eip7610]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-7610.md#specification
[eip7702]: https://eips.ethereum.org/EIPS/eip-7702#behavior
[eip2780]: https://eips.ethereum.org/EIPS/eip-2780#runtime-gas-costs -/
def prepareFirstFrame {fork : Fork} (chainId : Nat) (message : Message fork)
    (state : TransactionState) (substate : Substate) (auths : List Authorization)
    (paidWrites : Std.ExtTreeSet Address) :
    Except (EvmError × TransactionState) (FirstFrame fork Meter) := do
  -- From Glamsterdam, the meter holds the gas left, the state gas left and its baseline.
  --
  -- Before Glamsterdam the meter is a counter of the gas left.
  --
  -- It starts with the gas and the reservoir of the message.
  --
  -- From Glamsterdam, the first frame then pays some gas before its code runs, in a fixed order.
  --
  -- That is EIP-2780, in Last Call.
  let meter : Meter := GasMeter.start message.gas message.reservoir
  -- The preparation reads the created address, or the authorities, the recipient and the delegate.
  --
  -- It reads them in that order.
  match message.target with
  | none =>
    let address := message.currentTarget
    -- The read of the created address, for EIP-7928.
    let state := state.recordAccountRead address
    -- A creation fails when the created address has code, a nonce or storage.
    --
    -- That failure leaves no execution gas, at every fork.
    --
    -- EIP-684 forbids the code and the nonce, and EIP-7610 the storage.
    unless state.accountDeployable address do throw (.addressCollision address, state)
    -- From Glamsterdam, it pays the state gas of a new account.
    --
    -- It does so when the account at the address was empty before the transaction.
    let meter ← if fork ≥ .glamsterdam ∧ state.getPreStateAccount address = EMPTY_ACCOUNT then
        (GasMeter.chargeState meter NEW_ACCOUNT_STATE_GAS).mapError (·, state)
      else pure meter
    return .ofMeter message state substate 0 meter
  | some target =>
    -- From Pectra, the authorizations of a set code transaction apply before its message.
    --
    -- They apply by EIP-7702, then the state gas that they paid is committed.
    --
    -- The given paid accounts have their first write paid already.
    --
    -- Without authorizations, the fold leaves all as it was and the commit changes nothing.
    let done ← applyAuthorizations fork chainId state substate.accessedAddresses meter paidWrites
      auths
    let meter := GasMeter.commit done.meter
    -- A call with a nonzero value reads its recipient.
    --
    -- It reads it before the state gas charge below.
    let state := if message.value ≠ 0 then done.state.recordAccountRead target else done.state
    -- From Glamsterdam, a call that moves ether pays the state gas of a new account.
    --
    -- It pays it when its recipient is not alive.
    let meter ←
      if fork ≥ .glamsterdam ∧ message.value ≠ 0 ∧ !state.isAccountAlive target then
        (GasMeter.chargeState meter NEW_ACCOUNT_STATE_GAS).mapError (·, state)
      else pure meter
    -- The authorities join the accessed addresses.
    --
    -- It moves after the charge, which reads no accessed address.
    let substate := { substate with accessedAddresses := done.accessed }
    -- The resolution of a delegation reads the code of the recipient.
    let state := state.recordAccountRead target
    let code ← (state.getCode (state.getAccount target).codeHash).mapError (.state ·, state)
    -- From Pectra, a code that is a delegation indicator names a delegate.
    match if fork ≥ .pectra then delegatedAddress code else none with
    | some delegate =>
      -- The access to the delegate costs the price of a warm access if it is accessed, else cold.
      --
      -- Only from Glamsterdam; before, that access is free.
      let meter ← if fork ≥ .glamsterdam then
          (GasMeter.charge meter (accountAccessCost fork (delegate ∉ done.accessed))).mapError
            (·, state)
        else pure meter
      -- The message runs the code of the delegate.
      let state := state.recordAccountRead delegate
      let code ← (state.getCode (state.getAccount delegate).codeHash).mapError (.state ·, state)
      -- Its code address is the delegate, and it runs no precompile.
      let message := { message with code, codeAddress := some delegate, disablePrecompiles := true }
      -- The delegate joins the accessed addresses.
      let substate := { substate with accessedAddresses := done.accessed.insert delegate }
      return .ofMeter message state substate done.refund meter
    | none => return .ofMeter { message with code } state substate done.refund meter

/-- The message of a transaction at `fork`, on the chain `chainId`, in the monad `M`.

The observer sees each step of its frames.

It first prepares the first frame, which applies the authorizations `auths` of a call.

A failure there halts the message before its frame runs, and undoes the authorizations. -/
@[specialize]
def processMessageCallWith {fork : Fork} [LawfulGasMeter Meter] {M : Type → Type} [Monad M]
    [MonadExceptOf EvmError M] (observe : StepObserver M fork Meter) (chainId : Nat)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization := []) (paidWrites : Std.ExtTreeSet Address := ∅) :
    M CallOutput :=
  -- The first frame.
  match prepareFirstFrame (Meter := Meter) chainId message state substate auths paidWrites with
  -- An exceptional halt there puts the state back to before the preparation, and keeps its reads.
  --
  -- The nonce and the fee of the sender, paid before the message, stay.
  | .error (e, read) =>
    -- An error that aborts the whole execution, such as missing code, propagates instead.
    if e.aborts then throw e else pure (.ofHalt (state.withReadsOf read) message.reservoir e)
  | .ok first =>
    match message.target with
    -- A creation runs its init code.
    | none => do
      let ⟨evm, _⟩ ← processCreateMessageWith fork observe first.message first.state
        first.substate first.meter first.held
      return .ofFrame evm 0 evm.substate.touchedAccounts
    -- A call runs the code of its message.
    | some target => do
      let ⟨evm, _⟩ ← processMessageWith fork observe first.message first.state first.substate
        first.meter first.held
      -- From Spurious Dragon to Paris, the recipient joins `A_t`, for the deletion of EIP-161.
      --
      -- So a recipient left empty is touched.
      let touched := evm.substate.touchedAccounts
      let touched := if fork ≥ .spuriousDragon ∧ fork < .paris ∧
        evm.state.accountExistsAndIsEmpty target then touched.insert target else touched
      return .ofFrame evm first.refund touched

/-- The message of a transaction at `fork`, on the chain `chainId`.

It is the run with no observer, in the monad of errors. -/
def processMessageCall {fork : Fork} [LawfulGasMeter Meter] (chainId : Nat)
    (message : Message fork) (state : TransactionState) (substate : Substate)
    (auths : List Authorization := []) (paidWrites : Std.ExtTreeSet Address := ∅) :
    Except EvmError CallOutput :=
  processMessageCallWith (Meter := Meter) (fun _ _ => pure ()) chainId message state substate
    auths paidWrites

/-! ## The transaction -/

/-- What a transaction leaves once it has run. -/
structure TransactionOutput where
  /-- The state of the transaction once it has run, before its writes join the block.

  It holds the reads of the transaction, for the block access list of EIP-7928. -/
  state : TransactionState
  /-- The gas that the transaction used, after the refund. -/
  gasUsed : Nat
  /-- The gas that the transaction adds to the counts of its block. -/
  blockGas : BlockGas
  /-- The logs of the transaction, oldest first. -/
  logs : Array Log
  /-- The logs that a simulation reports for the transaction, oldest first.

  No rule reads them. -/
  simulatedLogs : Array Log
  /-- The error that stopped its message, or none when the message succeeded. -/
  error : Option EvmError
  /-- The output of its message: the data that it returned, or the data of its revert.

  It is empty after any other error, from Byzantium.

  Before Byzantium, a creation whose code deposit fails keeps the code that it returned.

  No rule reads it. -/
  messageOutput : ByteArray
  /-- The gas that it used before its refund.

  It is the gas used with no refund: from Pectra it is at least the call data floor.

  No rule reads it. -/
  gasBeforeRefund : Nat

/-- The block state, with the writes of the transaction. -/
def TransactionOutput.block (output : TransactionOutput) : BlockState :=
  output.state.incorporateTxIntoBlock.parent

/-- The state after the end of a transaction at `fork`: the deletions of its accounts.

Each account that SELFDESTRUCT marked is handled first.

Then, from Spurious Dragon to Paris, each touched empty one goes, by [EIP-161][eip161].

From Glamsterdam, a marked account loses its nonce, code and storage, and keeps its balance.

It goes only when that leaves it empty.

That rule is [EIP-8246][eip8246], in Last Call.

[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip8246]: https://eips.ethereum.org/EIPS/eip-8246#specification -/
def deleteAccounts (fork : Fork) (state : TransactionState) (output : CallOutput) :
    Except State.StateError TransactionState := do
  -- Each account to delete, the paper's `sigma'[i] = {}` for `i in A_s`.
  let state ← output.accountsToDelete.foldlM (init := state) fun state address =>
    -- From Glamsterdam, it loses its nonce, code and storage, and keeps its balance.
    if fork ≥ .glamsterdam then state.clearAccountPreservingBalance fork address
    -- Before, it is deleted.
    else pure (state.destroyAccount address)
  -- `sigma'[i] = {}` for `i in A_t` if `DEAD(sigma*, i)`, from Spurious Dragon to Paris.
  return state.destroyTouchedEmptyAccounts fork output.touchedAccounts.toList

/-- The accounts whose first write a transaction from `sender` to `target` has paid.

The intrinsic gas pays the write of the sender.

It also pays that of the target, for a creation or a transfer of ether.

[EIP-2780][eip2780] defines them.

[eip2780]: https://eips.ethereum.org/EIPS/eip-2780#eip-7702-authorization-processing -/
def paidWrites (sender target : Address) (tx : Transaction) : Std.ExtTreeSet Address :=
  -- The intrinsic gas pays the first write of the sender.
  let paid := (∅ : Std.ExtTreeSet Address).insert sender
  -- It pays that of the target too, for a creation or a nonzero value.
  if tx.to.isNone ∨ tx.value ≠ 0 then paid.insert target else paid

/-- Run a transaction with a gas meter of type `Meter`, on the block state `block` at `fork`.

It runs in the monad `M`, and the observer sees each step of its frames.

The checks of the transaction gave `included`.

A simulation can lift the cap on the execution gas, and charge a fee cap of 0 at a base fee of 0. -/
@[specialize]
def runTransactionWith {fork : Fork} (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    {M : Type → Type} [Monad M] [MonadExceptOf EvmError M] (observe : StepObserver M fork Meter)
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address := some) (lifted : LiftedRules := {}) :
    M TransactionOutput := do
  -- The state of the transaction starts from the block state.
  let state := TransactionState.ofBlock block
  let sender := included.sender
  -- The target, whose address for a creation uses the nonce of the sender before the transaction.
  let target ← liftExcept (messageTarget sender (state.getAccount sender).nonce tx)
  -- The nonce of the sender grows by one, and the sender buys the gas.
  let state ← liftExcept ((buyGas env state sender tx lifted).mapError EvmError.state)
  -- Each call runs the precompile that the given map assigns to its code address.
  let txEnv : TransactionEnvironment fork :=
    { origin := sender, gasPrice := included.gasPrice,
      blobVersionedHashes := fun _ => tx.blobHashes, precompiles }
  -- The gas limit minus the intrinsic gas: the paper's `g = T_g - g_0` before Glamsterdam.
  --
  -- From Glamsterdam, it splits into execution gas and a reservoir of state gas, by EIP-8037.
  --
  -- That EIP is in Last Call.
  let gas := allocateGas fork tx included.intrinsicGas lifted
  -- The message of the transaction.
  let message ← liftExcept (transactionMessage env txEnv state sender target gas.execution tx)
  -- Its run, the paper's `Lambda_4` or `Theta_4`, from the accesses `A*`.
  let output ← processMessageCallWith (Meter := Meter) observe env.chainId.toNat
    { message with reservoir := gas.reservoir } state
    (startSubstate fork env.coinbase sender target tx) tx.authorizations
    (paidWrites sender target tx)
  -- The gas left `g'`, with the state gas left in the reservoir from Glamsterdam.
  let gasLeft := output.gasLeft + output.reservoir
  -- The gas that the transaction adds to its block, and its state gas from Glamsterdam.
  let blockGas := transactionBlockGas fork sender tx gasLeft output.refund output.stateGasUsed
  let gasBeforeRefund := gasUsed fork sender tx gasLeft 0
  -- The sender gets back the gas left, with the reservoir left, and its refund.
  --
  -- Then the beneficiary gets its fee: the paper's `g*` and `sigma*`.
  let (state, gasUsed) ← liftExcept
    ((settleGas env output.state sender tx gasLeft output.refund lifted).mapError EvmError.state)
  -- Then the deletions, the paper's `sigma'`.
  let state ← liftExcept ((deleteAccounts fork state output).mapError EvmError.state)
  return ⟨state, gasUsed, blockGas, output.logs, output.simulatedLogs, output.error, output.output,
    gasBeforeRefund⟩

/-- Run a transaction with a gas meter of type `Meter`, on the block state `block` at `fork`.

It is the run with no observer, in the monad of errors. -/
def runTransaction {fork : Fork} (Meter : Type) [GasMeter Meter] [LawfulGasMeter Meter]
    (env : BlockEnvironment fork) (block : BlockState) (included : Included) (tx : Transaction)
    (precompiles : Address → Option Address := some) (lifted : LiftedRules := {}) :
    Except EvmError TransactionOutput :=
  runTransactionWith Meter (fun _ _ => pure ()) env block included tx precompiles lifted

/-- An observer of the steps in the monad `M`, for any gas meter. -/
abbrev TransactionObserver (M : Type → Type) (fork : Fork) : Type 1 :=
  {Meter : Type} → [GasMeter Meter] → StepObserver M fork Meter

/-- Run a transaction that may enter its block, on the block state `block` at `fork`.

It runs in the monad `M`, and the observer sees each step of its frames.

The checks of the transaction gave `included`.

If the observer never fails, the run fails only with an error that aborts the whole execution.

Missing code is such an error.

From Hegotá it fails, since the rules of that fork are not yet specified here.

By default a call runs the precompile at its own address.

A simulation can move a precompile to another address, and lift the cap on the execution gas. -/
@[specialize]
def processTransactionWith {fork : Fork} {M : Type → Type} [Monad M] [MonadExceptOf EvmError M]
    (observe : TransactionObserver M fork) (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) (precompiles : Address → Option Address := some)
    (lifted : LiftedRules := {}) : M TransactionOutput :=
  -- No EIP fixes the rules of Hegotá yet.
  if .hegota ≤ fork then throw (.forkNotYetSpecified fork)
  -- The gas meter of EIP-8037, with state gas, from Glamsterdam.
  --
  -- Up to BPO5, the meter is one counter of the gas left.
  else if fork ≥ .glamsterdam then
    runTransactionWith StateGasMeter observe env block included tx precompiles lifted
  else runTransactionWith Nat observe env block included tx precompiles lifted

/-- Run a transaction that may enter its block, on the block state `block` at `fork`.

It is the run with no observer, in the monad of errors.

From Hegotá it fails, since the rules of that fork are not yet specified here. -/
def processTransaction {fork : Fork} (env : BlockEnvironment fork) (block : BlockState)
    (included : Included) (tx : Transaction) (precompiles : Address → Option Address := some)
    (lifted : LiftedRules := {}) : Except EvmError TransactionOutput :=
  processTransactionWith (fun _ _ => pure ()) env block included tx precompiles lifted

end EthLib.Execution.Transactions
