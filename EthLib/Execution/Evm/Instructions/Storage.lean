module

public import EthLib.Execution.Evm.Op
public import EthLib.Execution.Evm.Step

/-!
# `Evm.Instructions.Storage`

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
  -- EIP-2929: a pair not yet in the accessed storage keys is a cold access.
  --
  -- The pair then joins the accessed storage keys.
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
  (gasSchedule fork).SSTORE_READ

/-- The price of SSTORE to change a slot whose original value is not zero.

From Berlin, it leaves out the price of a cold access, which SSTORE adds on its own. -/
def sstoreResetCost (fork : Fork) : Nat :=
  (gasSchedule fork).SSTORE_RESET

/-- The price of SSTORE in execution gas, from the original, current and new values of the slot.

The flag says whether the access to the slot is cold. -/
def sstoreCost (fork : Fork) (original current new : U256) (cold : Bool) : Nat :=
  if fork ≥ .glamsterdam then
    -- EIP-8038: the access, cold or warm.
    --
    -- Then it additionally charges `STORAGE_WRITE` when the write moves the slot from its original.
    (if cold then COLD_STORAGE_ACCESS else WARM_ACCESS) +
      if original = current ∧ current ≠ new then STORAGE_WRITE else 0
  else if fork ≥ .istanbul then
    -- EIP-2929, from Berlin: a cold pair costs an additional `COLD_SLOAD_COST` gas.
    let surcharge := if cold then COLD_STORAGE_ACCESS else 0
    surcharge +
      -- EIP-2200: when the original value equals the current value, and the new value differs:
      if original = current ∧ current ≠ new then
        -- An original value of 0 costs `SSTORE_SET_GAS`, any other `SSTORE_RESET_GAS`.
        if original = 0 then STORAGE_SET else sstoreResetCost fork
      -- The no-op and the dirty slot, which EIP-2200 tests first and last.
      --
      -- Both cost `SLOAD_GAS`.
      else sstoreReadCost fork
  -- Before Istanbul, the rule before EIP-2200: the set price when a zero slot becomes nonzero.
  --
  -- Otherwise the reset price.
  else if new ≠ 0 ∧ current = 0 then STORAGE_SET
  else COLD_STORAGE_WRITE

/-- The change of the refund counter by SSTORE, from the original, current and new values. -/
def sstoreRefund (fork : Fork) (original current new : U256) : Int :=
  -- EIP-2200's `SSTORE_CLEARS_SCHEDULE`, which EIP-3529 and EIP-8038 change.
  let clear : Int := (gasSchedule fork).REFUND_STORAGE_CLEAR
  if fork ≥ .istanbul then
    -- EIP-2200: a current value equal to the new value is a no-op, with no refund.
    if current = new then 0 else
      -- With a nonzero original and current, a new value of 0 adds `SSTORE_CLEARS_SCHEDULE` gas.
      --
      -- For a clean slot, `original = current`, so this covers both cases of the EIP.
      (if original ≠ 0 ∧ current ≠ 0 ∧ new = 0 then clear else 0) -
      -- A current value of 0, on a slot with a nonzero original, removes that gas again.
      (if original ≠ 0 ∧ current = 0 then clear else 0) +
      -- An original value equal to the new value resets the slot.
      (if original = new then
        -- From Glamsterdam, EIP-8038 rule 3: `STORAGE_WRITE` is refunded.
        if fork ≥ .glamsterdam then (STORAGE_WRITE : Int)
        -- An original value of 0 adds `SSTORE_SET_GAS - SLOAD_GAS` to the refund counter.
        else if original = 0 then (STORAGE_SET : Int) - sstoreReadCost fork
        -- Any other adds `SSTORE_RESET_GAS - SLOAD_GAS`.
        else (sstoreResetCost fork : Int) - sstoreReadCost fork
      else 0)
  -- Before Istanbul, the rule before EIP-2200: the clear refund when a nonzero slot becomes zero.
  else if new = 0 ∧ current ≠ 0 then clear
  else 0

/-- The state gas that SSTORE charges at fork `fork`: from Glamsterdam, that of a new slot. -/
def sstoreStateGas (fork : Fork) (original current new : U256) : Nat :=
  -- EIP-8037: a new slot charges `STATE_BYTES_PER_STORAGE_SET * CPSB` of state gas.
  --
  -- A new slot has original 0, current 0 and new `x > 0`.
  if fork ≥ .glamsterdam ∧ original = 0 ∧ current = 0 ∧ new ≠ 0 then STORAGE_SET_STATE_GAS else 0

/-- The state gas that SSTORE refills at fork `fork`.

From Glamsterdam, a slot that was zero at the start of the transaction can go back to zero.

That write refills the state gas of a new slot. -/
def sstoreStateRefill (fork : Fork) (original current new : U256) : Nat :=
  -- EIP-8037: a slot cleared back to 0 refills `STATE_BYTES_PER_STORAGE_SET * CPSB` of state gas.
  --
  -- That slot has original 0, current `x > 0` and new 0.
  if fork ≥ .glamsterdam ∧ original = 0 ∧ current ≠ 0 ∧ new = 0 then STORAGE_SET_STATE_GAS else 0

/-- SLOAD: replace a key with the word at that key of the storage of the current account. -/
def sloadStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- `0x54` SLOAD: `mu'_s[0] = sigma[I_a]_s[mu_s[0]]`.
  let (word, evm) ← popWord evm
  let key := U256.toBeBytes word
  let address := evm.message.currentTarget
  -- `A'_K = A_K union {(I_a, mu_s[0])}`, from Berlin.
  let (cold, evm) := accessStorageKey evm address key
  -- The price of a cold or a warm read.
  let evm ← chargeGas evm (sloadCost fork cold)
  -- The read, which EIP-7928 records.
  let evm := recordStorageRead evm address key
  let evm ← pushWord evm (evm.state.getStorage address key)
  return advance evm

/-- SSTORE: write a word at a key of the storage of the current account.

It pays and changes the refund counter by the original, current and new values of the slot.

From Glamsterdam, it first refills state gas, then pays execution gas, then state gas.

Once the check of the 2300 gas passes, it reads the slot.

That read stays even when the write then lacks gas, by EIP-7928. -/
def sstoreStep (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- From Glamsterdam, the static check comes first.
  --
  -- So a static frame records no read for EIP-7928.
  if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
  -- `0x55` SSTORE: the key `mu_s[0]`, then the new value `mu_s[1]`.
  let (word, evm) ← popWord evm
  let (new, evm) ← popWord evm
  -- EIP-2200: the frame fails when its gas left is at most the gas stipend, 2300.
  if fork ≥ .istanbul ∧ GasMeter.gasLeft evm.gas ≤ CALL_STIPEND then
    throw .outOfGas
  else
    let key := U256.toBeBytes word
    let address := evm.message.currentTarget
    -- The original value, at the start of the transaction, and the current value.
    let original := evm.state.getStorageOriginal address key
    let current := evm.state.getStorage address key
    -- EIP-2929: the pair joins the accessed storage keys, before the charge.
    let (cold, evm) := accessStorageKey evm address key
    -- The read of the slot, which EIP-7928 records once the stipend check passes.
    let evm := recordStorageRead evm address key
    keepReads evm id do
      -- From Glamsterdam: the refill, then execution gas, then state gas, in that order.
      --
      -- EIP-8037 meters state gas at the end of the execution of the opcode.
      --
      -- The order does not show: a refill write is warm, and pays 100 of the 2300 left.
      let evm := refillStateGas evm (sstoreStateRefill fork original current new)
      let evm ← chargeGas evm (sstoreCost fork original current new cold)
      let evm ← chargeStateGas evm (sstoreStateGas fork original current new)
      -- Before Glamsterdam, the static check of EIP-214 comes after the price.
      if evm.message.isStatic then
        throw .writeInStaticContext
      else
        -- `sigma'[I_a]_s[mu_s[0]] = mu_s[1]`.
        let state ← (evm.state.setStorage address key new).mapError .state
        let refundCounter := evm.substate.refundCounter + sstoreRefund fork original current new
        return advance { evm with state, substate := { evm.substate with refundCounter } }

/-- The instruction of an opcode that uses storage, or none for another opcode. -/
def storageStep : Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .sload => some sloadStep
  | .sstore => some sstoreStep
  | _ => none

end EthLib.Execution.Evm
