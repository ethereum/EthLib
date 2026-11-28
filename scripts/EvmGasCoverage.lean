module

public import EthLib.Execution.Evm.Interpreter

/-!
# Opcode gas coverage

The observer identifies gas rules from the interpreter's operands and frame changes.

It records completed charges, including the memory charge of a normal REVERT.
-/

namespace EthLib.Coverage

open EthLib.Base (Fork U256 toAddressMasked)
open EthLib.Execution.Evm

private inductive GasRule where
  | fixedPrice (gas : Nat)
  | memory (grew : Bool)
  | copy (nonempty : Bool)
  | hash (nonempty : Bool)
  | exponent (nonzero : Bool)
  | logTopics
  | logData (nonempty : Bool)
  | accountRead (cold : Bool)
  | externalCodeRead
  | sloadFixedPrice
  | sload (cold : Bool)
  | sstore (cold : Bool)
  | sstoreSentry
  | sstoreSet
  | sstoreReset
  | sstoreCleanWrite
  | sstoreUnchanged
  | sstoreDirty
  | sstoreClearRefund
  | sstoreRemoveClearRefund
  | sstoreRestoreRefund
  | sstoreStateCharge
  | sstoreStateRefill
  | callAccess (cold : Bool)
  | callDelegateAccess (cold : Bool)
  | callValue
  | callNewAccount
  | callNewAccountState
  | callStipend
  | callGrant (capped : Bool)
  | callSkipped
  | createHash
  | createInitCode
  | createGrant
  | createNewAccountState
  | createCollision
  | createSkipped
  | selfdestructBeneficiary (cold : Bool)
  | selfdestructNewAccount
  | selfdestructNewAccountState
  | selfdestructRefund

private def GasRule.label : GasRule → String
  | .fixedPrice gas => s!"opcode.fixed-price.{gas}"
  | .memory false => "opcode.memory.within-size"
  | .memory true => "opcode.memory.expand"
  | .copy false => "opcode.copy.zero-length"
  | .copy true => "opcode.copy.per-word"
  | .hash false => "opcode.keccak256.zero-length"
  | .hash true => "opcode.keccak256.per-word"
  | .exponent false => "opcode.exp.zero-exponent"
  | .exponent true => "opcode.exp.per-exponent-byte"
  | .logTopics => "opcode.log.per-topic"
  | .logData false => "opcode.log.zero-data"
  | .logData true => "opcode.log.per-data-byte"
  | .accountRead false => "opcode.account-read.warm"
  | .accountRead true => "opcode.account-read.cold"
  | .externalCodeRead => "opcode.external-code.read-charge"
  | .sloadFixedPrice => "opcode.sload.fixed-price"
  | .sload false => "opcode.sload.warm"
  | .sload true => "opcode.sload.cold"
  | .sstore false => "opcode.sstore.warm"
  | .sstore true => "opcode.sstore.cold"
  | .sstoreSentry => "opcode.sstore.sentry-passed"
  | .sstoreSet => "opcode.sstore.set-execution-charge"
  | .sstoreReset => "opcode.sstore.reset-execution-charge"
  | .sstoreCleanWrite => "opcode.sstore.clean-write-execution-charge"
  | .sstoreUnchanged => "opcode.sstore.unchanged"
  | .sstoreDirty => "opcode.sstore.dirty-write"
  | .sstoreClearRefund => "opcode.sstore.clear-refund-credit"
  | .sstoreRemoveClearRefund => "opcode.sstore.clear-refund-debit"
  | .sstoreRestoreRefund => "opcode.sstore.restore-original-refund"
  | .sstoreStateCharge => "opcode.sstore.new-slot-state-charge"
  | .sstoreStateRefill => "opcode.sstore.clear-new-slot-state-refill"
  | .callAccess false => "opcode.call.warm-target"
  | .callAccess true => "opcode.call.cold-target"
  | .callDelegateAccess false => "opcode.call.warm-delegate"
  | .callDelegateAccess true => "opcode.call.cold-delegate"
  | .callValue => "opcode.call.value-charge"
  | .callNewAccount => "opcode.call.new-account-execution-charge"
  | .callNewAccountState => "opcode.call.new-account-state-charge"
  | .callStipend => "opcode.call.value-stipend"
  | .callGrant false => "opcode.call.requested-gas-grant"
  | .callGrant true => "opcode.call.capped-gas-grant"
  | .callSkipped => "opcode.call.grant-returned-without-child"
  | .createHash => "opcode.create2.init-code-hash-per-word"
  | .createInitCode => "opcode.create.init-code-per-word"
  | .createGrant => "opcode.create.gas-grant"
  | .createNewAccountState => "opcode.create.new-account-state-charge"
  | .createCollision => "opcode.create.grant-spent-on-collision"
  | .createSkipped => "opcode.create.skipped-before-grant"
  | .selfdestructBeneficiary false => "opcode.selfdestruct.warm-beneficiary"
  | .selfdestructBeneficiary true => "opcode.selfdestruct.cold-beneficiary-surcharge"
  | .selfdestructNewAccount => "opcode.selfdestruct.new-account-execution-charge"
  | .selfdestructNewAccountState => "opcode.selfdestruct.new-account-state-charge"
  | .selfdestructRefund => "opcode.selfdestruct.refund-credit"

private def whenRule (condition : Bool) (rule : GasRule) : Array GasRule :=
  if condition then #[rule] else #[]

private def fixedPrices (fork : Fork) : Array Nat := Id.run do
  let mut prices := #[GasCosts.ZERO, GasCosts.OPCODE_JUMPDEST, GasCosts.BASE, GasCosts.VERY_LOW,
    GasCosts.LOW, GasCosts.MID, GasCosts.HIGH, GasCosts.OPCODE_BLOCKHASH]
  if fork < .berlin then
    prices := prices ++ #[balanceCost fork false, externalBaseCost fork false]
    if fork ≥ Op.extcodehash.since then prices := prices.push (extcodehashCost fork false)
  if fork ≥ Op.tload.since then prices := prices.push GasCosts.OPCODE_TLOAD
  return prices.toList.eraseDups.toArray

/-- The gas rules this observer can distinguish at `fork`. -/
public def gasRuleInventory (fork : Fork) : Array String := Id.run do
  let mut rules : Array GasRule := ((fixedPrices fork).map .fixedPrice) ++ #[
    .memory false, .memory true, .copy false, .copy true, .hash false, .hash true,
    .exponent false, .exponent true, .logTopics, .logData false, .logData true, .sstoreClearRefund,
    .callValue, .callStipend, .callGrant false, .callSkipped, .createGrant, .createCollision,
    .createSkipped]
  if fork < .glamsterdam then
    rules := rules ++ #[.sstoreSet, .sstoreReset, .callNewAccount]
  else
    rules := rules ++ #[.sstoreCleanWrite, .sstoreStateCharge, .sstoreStateRefill,
      .callNewAccountState, .createNewAccountState, .selfdestructNewAccountState, .externalCodeRead]
  if fork ≥ .tangerineWhistle then
    rules := rules ++ #[.callGrant true, .selfdestructNewAccount]
  if fork ≥ .constantinople then
    rules := rules.push .createHash
  if fork ≥ .istanbul then
    rules := rules ++ #[.sstoreSentry, .sstoreUnchanged, .sstoreDirty, .sstoreRemoveClearRefund,
      .sstoreRestoreRefund]
  if fork ≥ .berlin then
    rules := rules ++ #[.accountRead false, .accountRead true, .sload false, .sload true,
      .sstore false, .sstore true, .callAccess false, .callAccess true,
      .selfdestructBeneficiary false, .selfdestructBeneficiary true]
  else
    rules := rules.push .sloadFixedPrice
  if fork < .london then
    rules := rules.push .selfdestructRefund
  if fork ≥ .shapella then
    rules := rules.push .createInitCode
  if fork ≥ .pectra then
    rules := rules ++ #[.callDelegateAccess false, .callDelegateAccess true]
  return rules.map GasRule.label

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

private def usesMemory : Op → Bool
  | .keccak256 | .calldatacopy | .codecopy | .extcodecopy | .returndatacopy
  | .mload | .mstore | .mstore8 | .mcopy | .log _ | .«return» | .revert
  | .call | .callcode | .delegatecall | .staticcall | .create | .create2 => true
  | _ => false

private def callKind : Op → Option CallKind
  | .call => some .call
  | .callcode => some .callcode
  | .delegatecall => some .delegatecall
  | .staticcall => some .staticcall
  | _ => none

private def usesFixedPrice (fork : Fork) (op : Op) : Bool :=
  if usesMemory op then false else
  match op with
  | .exp | .sload | .sstore | .selfdestruct => false
  | .balance | .extcodehash | .extcodesize => fork < .berlin
  | _ => true

private def storageWriteRules (original current new : U256) : Array GasRule :=
  let branch := sstoreCase fork original current new
  let write : GasRule := match branch.write with
    | .unchanged => .sstoreUnchanged
    | .dirty => .sstoreDirty
    | .set => .sstoreSet
    | .reset => .sstoreReset
    | .clean => .sstoreCleanWrite
  whenRule (fork ≥ .istanbul) .sstoreSentry ++ #[write] ++
    whenRule branch.clears .sstoreClearRefund ++
    whenRule branch.unclears .sstoreRemoveClearRefund ++
    whenRule branch.restores .sstoreRestoreRefund ++
    whenRule branch.fills .sstoreStateCharge ++
    whenRule branch.refills .sstoreStateRefill

private def storageRules (evm : Evm fork Meter) (write : Bool) : Array GasRule := Id.run do
  let some word := evm.stack.val[0]? | return #[]
  let key := U256.toBeBytes word
  let address := evm.message.currentTarget
  -- EIP-2929, Storage read changes: the price depends on prior access to this account and key.
  let cold := (accessStorageKey evm address key).1
  if !write then return #[if fork ≥ .berlin then .sload cold else .sloadFixedPrice]
  let access := whenRule (fork ≥ .berlin) (.sstore cold)
  let some new := evm.stack.val[1]? | return access
  let original := evm.state.getStorageOriginal address key
  let current := evm.state.getStorage address key
  return access ++ storageWriteRules (fork := fork) original current new

private def callRules (evm : Evm fork Meter) (kind : CallKind) (child : Option (Message fork)) :
    Array GasRule := Id.run do
  let .ok (call, evm) := popCallOperands kind evm | return #[]
  let (cold, evm) := accessAddress evm call.address
  let .ok (callee, evm) := accessDelegation evm call.address 0 | return #[]
  let mut rules := whenRule (fork ≥ .berlin) (.callAccess cold)
  if callee.delegated then
    rules := rules.push (.callDelegateAccess (callee.accessCost == accountAccessCost fork true))
  rules := rules ++ whenRule (callValueCost fork call.value > 0) .callValue
  rules := rules ++ whenRule (kind == .call &&
    callNewAccountCost fork evm.state call.address call.value > 0) .callNewAccount
  let newAccount := callNewAccountStateGas fork kind evm.state call
  rules := rules ++ whenRule (newAccount > 0) .callNewAccountState
  -- The call grant includes the stipend, even when a skipped call gives the grant back.
  let stipend := if call.value = 0 then 0 else GasCosts.CALL_STIPEND
  rules := rules ++ whenRule (stipend > 0) .callStipend
  let requested := call.gas.toNat + stipend
  if let some message := child then
    return rules.push (.callGrant (message.gas < requested))
  -- A skipped call has already returned its grant. Recover it with the same charge it paid.
  rules := rules.push .callSkipped
  let growth := extendMemory evm.memory.size
    [(call.inputStart, call.inputSize), (call.outputStart, call.outputSize)]
  let extra := callExtraGas fork kind evm.state call cold callee
  let .ok (grant, _) := payCall kind call growth.cost extra newAccount evm | return rules
  return rules.push (.callGrant (grant < requested))

private def creationRules (evm after : Evm fork Meter) (create2 : Bool)
    (child : Option (Message fork)) : Array GasRule := Id.run do
  let some start := evm.stack.val[1]? | return #[]
  let some size := evm.stack.val[2]? | return #[]
  let mut rules := whenRule (create2 && size ≠ 0) .createHash ++
    whenRule (fork ≥ .shapella && size ≠ 0) .createInitCode
  let current := evm.message.currentTarget
  let nonce := (evm.state.getAccount current).nonce
  if (after.state.getAccount current).nonce = nonce then return rules.push .createSkipped
  -- The creation increments the nonce once it pays for its child, even on an address collision.
  rules := rules.push .createGrant
  if child.isNone then rules := rules.push .createCollision
  if fork < .glamsterdam then return rules
  let address := match child with
    | some message => some message.currentTarget
    | none =>
      let salt := if create2 then evm.stack.val[3]? else none
      let initCode := memoryReadBytes after.memory start.toNat size.toNat
      (creationAddress current nonce salt initCode).toOption
  return rules ++ whenRule (address.any fun target =>
    createNewAccountStateGas fork evm.state target > 0) .createNewAccountState

private def selfdestructRules (evm after : Evm fork Meter) : Array GasRule := Id.run do
  let some word := evm.stack.val[0]? | return #[]
  let beneficiary := toAddressMasked word
  let cold := (accessAddress evm beneficiary).1
  let creates := selfdestructCreatesAccount fork evm.state evm.message.currentTarget beneficiary
  return whenRule (fork ≥ .berlin) (.selfdestructBeneficiary cold) ++
    whenRule (creates && selfdestructCost fork cold true > selfdestructCost fork cold false)
      .selfdestructNewAccount ++
    whenRule (selfdestructStateGas fork creates > 0) .selfdestructNewAccountState ++
    whenRule (after.substate.refundCounter > evm.substate.refundCounter) .selfdestructRefund

private def variableRules (op : Op) (evm after : Evm fork Meter)
    (child : Option (Message fork)) : Array GasRule :=
  let nonzero (n : Nat) := evm.stack.val[n]?.any (· != 0)
  match op with
  | .exp => #[.exponent (nonzero 1)]
  | .keccak256 => #[.hash (nonzero 1)]
  | .calldatacopy | .codecopy | .returndatacopy | .mcopy => #[.copy (nonzero 2)]
  | .extcodecopy => #[.copy (nonzero 3)] ++ externalCodeRules
  | .extcodesize => externalCodeRules
  | .balance | .extcodehash => accountRules
  | .log n => #[.logData (nonzero 1)] ++ whenRule (n.val > 0) .logTopics
  | .sload => storageRules evm false
  | .sstore => storageRules evm true
  | .create => creationRules evm after false child
  | .create2 => creationRules evm after true child
  | .selfdestruct => selfdestructRules evm after
  | op => (callKind op).elim #[] (callRules evm · child)
where
  accountRules := match evm.stack.val[0]? with
    | some word =>
      whenRule (fork ≥ .berlin) (.accountRead (accessAddress evm (toAddressMasked word)).1)
    | none => #[]
  externalCodeRules := accountRules ++ whenRule (fork ≥ .glamsterdam) .externalCodeRead

/-- The gas-rule evidence from a charged opcode step, including a step that reverts normally. -/
public def stepGasRules (evm : Evm fork Meter) (step : StepResult fork Meter) :
    Array String := Id.run do
  let (after, child) := match step with
    | .next after => (after, none)
    | .child caller message _ => (caller, some message)
  -- A step that preserves reads can return a halted frame with an exceptional error.
  if after.error.any (· != .revert) then return #[]
  let op := if h : evm.pc < evm.code.size then Op.ofByte fork evm.code[evm.pc] else some .stop
  let some op := op | return #[]
  let price := GasMeter.gasHeld evm.gas - GasMeter.gasHeld after.gas
  let fixed := whenRule (usesFixedPrice fork op) (.fixedPrice price)
  let memory := whenRule (usesMemory op) (.memory (after.memory.size > evm.memory.size))
  return (fixed ++ memory ++ variableRules op evm after child).map GasRule.label

end EthLib.Coverage
