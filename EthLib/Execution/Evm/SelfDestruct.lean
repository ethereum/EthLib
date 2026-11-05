module

public import EthLib.Execution.Evm.Measure

/-!
# `Evm.SelfDestruct`

SELFDESTRUCT: send the whole balance of the current account to a beneficiary, then stop.

It pays 5000 from Tangerine Whistle, and nothing before.

From Berlin, a cold beneficiary costs the price of a cold access more.

From Tangerine Whistle, a beneficiary with no account costs 25000 more.

From Spurious Dragon, that price applies only to a dead beneficiary, and only when ether moves.

Before London, the first deletion of an account in the transaction refunds 24000.

From Byzantium, SELFDESTRUCT fails in a frame that must not change the state.

Before Cancun, the account is deleted at the end of the transaction, and its ether is gone.

From Cancun, only an account created in the same transaction is deleted.

Any other account just sends its balance, and keeps its code and storage.

Appendix H.2 of the Yellow Paper, Shanghai version, defines the instruction.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that change the instruction define it:

- [EIP-150][eip150], the price and the price of a new account
- [EIP-161][eip161], the new account only for a dead beneficiary that gets ether
- [EIP-214][eip214], no SELFDESTRUCT in a static frame
- [EIP-2929][eip2929], the cold access
- [EIP-3529][eip3529], no refund
- [EIP-6780][eip6780], deletion only in the transaction that creates the account

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip214]: https://eips.ethereum.org/EIPS/eip-214#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#selfdestruct-changes
[eip3529]: https://eips.ethereum.org/EIPS/eip-3529#specification
[eip6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)
open EthLib.Execution.State (TransactionState)

variable {fork : Fork} {Meter : Type} [GasMeter Meter]

/-- The price of SELFDESTRUCT at fork `fork`, for a cold or warm beneficiary.

`createsAccount` says whether the beneficiary gets an account it lacks. -/
def selfdestructCost (fork : Fork) (cold createsAccount : Bool) : Nat :=
  let schedule := gasSchedule fork
  schedule.OPCODE_SELFDESTRUCT_BASE + (if cold then schedule.COLD_ACCOUNT_ACCESS else 0) +
    (if createsAccount then schedule.OPCODE_SELFDESTRUCT_NEW_ACCOUNT else 0)

/-- Whether SELFDESTRUCT from `originator` gives `beneficiary` an account at fork `fork`.

Before Spurious Dragon, it does when the beneficiary has no account.

From Spurious Dragon, it does when the beneficiary is dead and the originator holds ether. -/
def selfdestructCreatesAccount (fork : Fork) (state : TransactionState)
    (originator beneficiary : Address) : Bool :=
  if fork ≥ .spuriousDragon then
    !state.isAccountAlive beneficiary && (state.getAccount originator).balance != 0
  else !state.accountExists beneficiary

/-- The state after `originator` sends its balance to `beneficiary` by SELFDESTRUCT.

Before Cancun, the beneficiary gains the balance, then the originator's balance becomes 0.

So the ether is gone when the two are the same account.

From Cancun, the balance moves, and then only an account created in the transaction drops to 0. -/
def selfdestructTransfer (fork : Fork) (state : TransactionState)
    (originator beneficiary : Address) : Except State.StateError TransactionState := do
  let balance := (state.getAccount originator).balance
  if fork ≥ .dencun then
    let state ← state.moveEther fork originator beneficiary balance
    if originator ∈ state.createdAccounts then state.setAccountBalance fork originator 0
    else return state
  else
    let state ← state.createEther fork beneficiary balance
    state.setAccountBalance fork originator 0

/-- The frame after SELFDESTRUCT has paid: it moves the balance and stops.

It fails in a static frame.

It records the account to delete: before Cancun always, and from Cancun when created here.

From Spurious Dragon to Paris, an empty beneficiary counts as touched. -/
def finishSelfdestruct (fork : Fork) (beneficiary : Address) (refund : Nat)
    (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) :=
  if evm.message.isStatic then .error .writeInStaticContext
  else do
    let originator := evm.message.currentTarget
    let state ← (selfdestructTransfer fork evm.state originator beneficiary).mapError .state
    let deletes := fork < .dencun ∨ originator ∈ state.createdAccounts
    let touched := evm.substate.touchedAccounts
    let touchesBeneficiary :=
      fork ≥ .spuriousDragon ∧ fork < .paris ∧ state.accountExistsAndIsEmpty beneficiary
    return { evm with
      state
      running := false
      substate := { evm.substate with
        accountsToDelete :=
          if deletes then evm.substate.accountsToDelete.insert originator
          else evm.substate.accountsToDelete
        refundCounter := evm.substate.refundCounter + refund
        touchedAccounts := if touchesBeneficiary then touched.insert beneficiary else touched } }

/-- SELFDESTRUCT at fork `fork`: pop the beneficiary, pay, move the balance and stop.

The refund before London is for an account that this frame and its callers do not yet delete. -/
def selfdestructStep (fork : Fork) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  let (word, evm) ← popWord evm
  let beneficiary := toAddressMasked word
  let (cold, evm) := accessAddress evm beneficiary
  let originator := evm.message.currentTarget
  let createsAccount := selfdestructCreatesAccount fork evm.state originator beneficiary
  let refund :=
    if originator ∈ evm.substate.accountsToDelete then 0
    else (gasSchedule fork).REFUND_SELF_DESTRUCT
  let evm ← chargeGas evm (selfdestructCost fork cold createsAccount)
  finishSelfdestruct fork beneficiary refund evm

/-- The instruction of SELFDESTRUCT at fork `fork`, and none for any other opcode. -/
def selfdestructOpStep (fork : Fork) :
    Op → Option (Evm fork Meter → Except EvmError (Evm fork Meter))
  | .selfdestruct => some (selfdestructStep fork)
  | _ => none

/-- SELFDESTRUCT stops a running frame with no more gas, so it lowers the measure. -/
theorem selfdestructOpStep_measure_lt [LawfulGasMeter Meter] {op : Op}
    {f : Evm fork Meter → Except EvmError (Evm fork Meter)} {evm after : Evm fork Meter}
    (hf : selfdestructOpStep fork op = some f) (h : f evm = .ok after)
    (running : evm.running = true) : measure after < measure evm := by
  cases op <;> simp only [selfdestructOpStep, Option.some.injEq, reduceCtorEq] at hf
  subst hf
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
  have paid := ((popWord_pays h1).trans (accessAddress_pays _ _)).trans (chargeGas_pays h2)
  have := paid.gasHeld
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    exact measure_lt_of_stop (show GasMeter.gasHeld e2.gas ≤ _ by omega) rfl running

end EthLib.Execution.Evm
