module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Storage`

SLOAD and SSTORE: read and write a word of the storage of the account whose code runs.

Up to Petersburg, SSTORE costs 20000 to set a zero slot and 5000 otherwise.

It refunds 15000 when it clears a slot.

From Istanbul, net gas metering prices a write by the original, current and new value.

The original value is the value before the transaction.

A write to a slot that the transaction already changed costs as much as a read.

Refunds give back the price of writes that a later write undoes.

From Istanbul, SSTORE also fails when the frame has 2300 gas or less.

From Berlin, the first access to a slot in a transaction is cold, and costs 2100 more.

From London, clearing a slot refunds 4800.

From Glamsterdam, the price of a write has three parts, by EIP-8038.

The access costs 2100 when cold and 100 when warm.

A write that moves the slot away from its original value costs 10000 more.

A write that sets a zero slot also costs the state gas of 64 bytes, by EIP-8037.

A write that puts such a slot back to zero refills that state gas first.

Clearing a slot refunds 11616, and restoring the original value refunds the 10000.

EIP-1283 never ran on mainnet, so Constantinople keeps the rule of Petersburg.

SSTORE fails in a static frame.

From Glamsterdam, it checks the frame before any other step.

Appendix H.2 of the Yellow Paper, Berlin version, defines the rule up to Berlin.

Source: [`Paper.tex` at `beacfbd`][yp-berlin] of the Yellow Paper.

The EIPs that change the rule:

- [EIP-1716][eip1716], Petersburg without the rule of EIP-1283
- [EIP-2200][eip2200], net gas metering and the 2300 sentry
- [EIP-2929][eip2929], the cold and warm accesses to a slot
- [EIP-3529][eip3529], the smaller refund to clear a slot
- [EIP-8037][eip8037], the state gas of a new slot
- [EIP-8038][eip8038], the write price and the larger refund to clear a slot

[yp-berlin]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[eip1716]: https://eips.ethereum.org/EIPS/eip-1716#specification
[eip2200]: https://eips.ethereum.org/EIPS/eip-2200#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#sstore-changes
[eip3529]: https://eips.ethereum.org/EIPS/eip-3529#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-sstore-opcode-level
[eip8038]: https://eips.ethereum.org/EIPS/eip-8038#sstore-pricing
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Bytes32 Fork U256)
open GasCosts

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- Whether an access to a slot of an address is cold, and the frame after the access.

From Berlin, the access is cold when the transaction has not yet accessed the slot.

It then adds the slot to the accessed storage keys.

Before Berlin, no access is cold, and the frame stays as it is. -/
def accessStorageKey (evm : Evm fork Meter) (address : Address) (key : Bytes32) :
    Bool × Evm fork Meter :=
  if fork ≥ .berlin then
    let accessed := evm.substate.accessedStorageKeys
    let keys := accessed.getD address ∅
    (key ∉ keys,
      { evm with
        substate := { evm.substate with
          accessedStorageKeys := accessed.insert address (keys.insert key) } })
  else (false, evm)

/-- The price of SSTORE when the write leaves the slot as it is, or the slot is already dirty.

It is the price of SLOAD up to Berlin, and of a warm access from Berlin. -/
def sstoreReadCost (fork : Fork) : Nat :=
  if fork ≥ .berlin then WARM_ACCESS else sloadCost fork false

/-- The price of SSTORE to change a slot whose original value is not zero.

From Berlin, it leaves out the price of a cold access, which SSTORE adds on its own. -/
def sstoreResetCost (fork : Fork) : Nat :=
  if fork ≥ .berlin then COLD_STORAGE_WRITE - COLD_STORAGE_ACCESS else COLD_STORAGE_WRITE

/-- The price of SSTORE in execution gas, from the original, current and new values of the slot.

The flag says whether the access to the slot is cold. -/
def sstoreCost (fork : Fork) (original current new : U256) (cold : Bool) : Nat :=
  if fork ≥ .glamsterdam then
    (if cold then COLD_STORAGE_ACCESS else WARM_ACCESS) +
      if original = current ∧ current ≠ new then STORAGE_WRITE else 0
  else if fork ≥ .istanbul then
    let surcharge := if cold then COLD_STORAGE_ACCESS else 0
    surcharge +
      if original = current ∧ current ≠ new then
        if original = 0 then STORAGE_SET else sstoreResetCost fork
      else sstoreReadCost fork
  else if new ≠ 0 ∧ current = 0 then STORAGE_SET
  else COLD_STORAGE_WRITE

/-- The change of the refund counter by SSTORE, from the original, current and new values. -/
def sstoreRefund (fork : Fork) (original current new : U256) : Int :=
  let clear : Int := (gasSchedule fork).REFUND_STORAGE_CLEAR
  if fork ≥ .istanbul then
    if current = new then 0 else
      (if original ≠ 0 ∧ current ≠ 0 ∧ new = 0 then clear else 0) -
      (if original ≠ 0 ∧ current = 0 then clear else 0) +
      (if original = new then
        if fork ≥ .glamsterdam then (STORAGE_WRITE : Int)
        else if original = 0 then (STORAGE_SET : Int) - sstoreReadCost fork
        else (sstoreResetCost fork : Int) - sstoreReadCost fork
      else 0)
  else if new = 0 ∧ current ≠ 0 then clear
  else 0

/-- The state gas that SSTORE charges at fork `fork`: from Glamsterdam, that of a new slot. -/
def sstoreStateGas (fork : Fork) (original current new : U256) : Nat :=
  if fork ≥ .glamsterdam ∧ original = 0 ∧ current = 0 ∧ new ≠ 0 then STORAGE_SET_STATE_GAS else 0

/-- The state gas that SSTORE refills at fork `fork`.

From Glamsterdam, a slot that was zero at the start of the transaction can go back to zero.

That write refills the state gas of a new slot. -/
def sstoreStateRefill (fork : Fork) (original current new : U256) : Nat :=
  if fork ≥ .glamsterdam ∧ original = 0 ∧ current ≠ 0 ∧ new = 0 then STORAGE_SET_STATE_GAS else 0

/-- SLOAD: replace a key with the word at that key of the storage of the current account. -/
def sloadStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let key := U256.toBeBytes word
  let address := evm.message.currentTarget
  let (cold, evm) := accessStorageKey evm address key
  let evm ← chargeGas evm (sloadCost fork cold)
  let evm ← pushWord evm (evm.state.getStorage address key)
  return advance evm

/-- SSTORE: write a word at a key of the storage of the current account.

It pays and changes the refund counter by the original, current and new values of the slot.

From Glamsterdam, it first refills state gas, then pays execution gas, then state gas. -/
def sstoreStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
  let (word, evm) ← popWord evm
  let (new, evm) ← popWord evm
  if fork ≥ .istanbul ∧ GasMeter.gasLeft evm.gas ≤ CALL_STIPEND then
    throw .outOfGas
  else
    let key := U256.toBeBytes word
    let address := evm.message.currentTarget
    let original := evm.state.getStorageOriginal address key
    let current := evm.state.getStorage address key
    let (cold, evm) := accessStorageKey evm address key
    let evm := refillStateGas evm (sstoreStateRefill fork original current new)
    let evm ← chargeGas evm (sstoreCost fork original current new cold)
    let evm ← chargeStateGas evm (sstoreStateGas fork original current new)
    if evm.message.isStatic then
      throw .writeInStaticContext
    else
      let state ← (evm.state.setStorage address key new).mapError .state
      let refundCounter := evm.substate.refundCounter + sstoreRefund fork original current new
      return advance { evm with state, substate := { evm.substate with refundCounter } }

/-- The instruction of an opcode that uses storage, or none for another opcode. -/
def storageStep : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .sload => some sloadStep
  | .sstore => some sstoreStep
  | _ => none

end EthLib.Execution.Evm
