module

public import EthLib.Execution.Evm.Measure
public import EthLib.Execution.Evm.TransferLog

/-!
# `Evm.Instructions.SelfDestruct`

SELFDESTRUCT: send the whole balance of the current account to a beneficiary, then stop.

Appendix H.2 of the Yellow Paper, Shanghai version, defines the instruction.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

The EIPs that change the instruction define it:

- [EIP-150][eip150], the price and the price of a new account
- [EIP-161][eip161], the new account only for a dead beneficiary that gets ether
- [EIP-214][eip214], no SELFDESTRUCT in a static frame
- [EIP-2929][eip2929], the cold access
- [EIP-3529][eip3529], no refund
- [EIP-6780][eip6780], deletion only in the transaction that creates the account
- [EIP-7708][eip7708], the transfer log, in Last Call
- [EIP-8037][eip8037], the state gas of a new account, in Last Call
- [EIP-8038][eip8038], the write of the new account, in Last Call
- [EIP-8246][eip8246], no ether gone, in Last Call

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
[eip214]: https://eips.ethereum.org/EIPS/eip-214#specification
[eip2929]: https://eips.ethereum.org/EIPS/eip-2929#selfdestruct-changes
[eip3529]: https://eips.ethereum.org/EIPS/eip-3529#specification
[eip6780]: https://eips.ethereum.org/EIPS/eip-6780#specification
[eip7708]: https://eips.ethereum.org/EIPS/eip-7708#specification
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-new-accounts
[eip8038]: https://eips.ethereum.org/EIPS/eip-8038#selfdestruct
[eip8246]: https://eips.ethereum.org/EIPS/eip-8246#specification
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
  -- The base, 5000 from Tangerine Whistle and nothing before.
  --
  -- From Berlin, a cold beneficiary costs the price of a cold access more.
  schedule.OPCODE_SELFDESTRUCT_BASE + (if cold then schedule.COLD_ACCOUNT_ACCESS else 0) +
    -- From Tangerine Whistle, a beneficiary that gets an account costs 25000 more.
    --
    -- From Glamsterdam, it costs 9000, the write of an account, by EIP-8038.
    (if createsAccount then schedule.OPCODE_SELFDESTRUCT_NEW_ACCOUNT else 0)

/-- The state gas of SELFDESTRUCT at fork `fork`.

From Glamsterdam, a beneficiary that gets a new account costs the state gas of that account. -/
def selfdestructStateGas (fork : Fork) (createsAccount : Bool) : Nat :=
  if fork ≥ .glamsterdam ∧ createsAccount then GasCosts.NEW_ACCOUNT_STATE_GAS else 0

/-- Whether SELFDESTRUCT from `originator` gives `beneficiary` an account at fork `fork`.

Before Spurious Dragon, it does when the beneficiary has no account.

From Spurious Dragon, it does when the beneficiary is dead and the originator holds ether. -/
def selfdestructCreatesAccount (fork : Fork) (state : TransactionState)
    (originator beneficiary : Address) : Bool :=
  -- EIP-161: from Spurious Dragon, a dead beneficiary that receives a nonzero value.
  if fork ≥ .spuriousDragon then
    !state.isAccountAlive beneficiary && (state.getAccount originator).balance != 0
  -- EIP-150: before, a beneficiary with no account.
  else !state.accountExists beneficiary

/-- The state after `originator` sends its balance to `beneficiary` by SELFDESTRUCT. -/
def selfdestructTransfer (fork : Fork) (state : TransactionState)
    (originator beneficiary : Address) : Except State.StateError TransactionState := do
  let balance := (state.getAccount originator).balance
  if fork ≥ .dencun then
    -- EIP-6780: SELFDESTRUCT transfers the entire balance of the account to the target.
    let state ← state.moveEther fork originator beneficiary balance
    -- EIP-6780: for a contract created in the same transaction, its balance is set to 0.
    --
    -- So the ether is gone when the target is that contract itself.
    --
    -- From Glamsterdam, EIP-8246 drops that step, and no ether is gone.
    --
    -- An account created in the transaction that names itself as beneficiary keeps its balance.
    --
    -- That holds from Glamsterdam.
    --
    -- At the end of the transaction, such an account then loses its nonce, code and storage.
    --
    -- It does not lose its balance.
    if fork < .glamsterdam ∧ originator ∈ state.createdAccounts then
      state.setAccountBalance fork originator 0
    else return state
  else
    -- Before Cancun, the beneficiary gains the balance.
    --
    -- `sigma'[r]_b = sigma[r]_b + sigma[I_a]_b` for the beneficiary `r`.
    let state ← state.createEther fork beneficiary balance
    -- Then the balance of the originator becomes 0: `sigma'[I_a]_b = 0`.
    --
    -- So the ether is gone when the two are the same account, `r = I_a`.
    state.setAccountBalance fork originator 0

/-- The frame after SELFDESTRUCT has paid: it moves the balance and stops.

It fails in a static frame. -/
def finishSelfdestruct (fork : Fork) (beneficiary : Address) (refund : Nat)
    (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) :=
  -- EIP-214: from Byzantium, in a static frame, SELFDESTRUCT fails before ether moves.
  if evm.message.isStatic then .error .writeInStaticContext
  else do
    let originator := evm.message.currentTarget
    let balance := (evm.state.getAccount originator).balance
    -- The move of the balance to the beneficiary.
    let state ← (selfdestructTransfer fork evm.state originator beneficiary).mapError .state
    -- The account to delete at the end of the transaction: `A'_s = A_s union {I_a}` before Cancun.
    --
    -- Before Cancun, the ether of the deleted account is gone.
    --
    -- From Cancun, EIP-6780 deletes only a contract created in the same transaction.
    --
    -- Any other account just sends its balance, and keeps its code and storage.
    let deletes := fork < .dencun ∨ originator ∈ state.createdAccounts
    let touched := evm.substate.touchedAccounts
    -- From Spurious Dragon, before Paris, an empty beneficiary joins `A_t`, for EIP-161's deletion.
    let touchesBeneficiary :=
      fork ≥ .spuriousDragon ∧ fork < .paris ∧ state.accountExistsAndIsEmpty beneficiary
    -- The frame halts.
    return { evm with
      state
      running := false
      substate := { evm.substate with
        accountsToDelete :=
          if deletes then evm.substate.accountsToDelete.insert originator
          else evm.substate.accountsToDelete
        -- EIP-7708, from Glamsterdam: a nonzero move to a different account writes a transfer log.
        logs := pushTransferLog fork evm.substate.logs originator beneficiary balance
        simulatedLogs :=
          pushSimulatedTransferLog fork evm.substate.simulatedLogs originator beneficiary balance
        -- `A'_r = A_r + R_selfdestruct` for the first deletion; 0 from London, by EIP-3529.
        refundCounter := evm.substate.refundCounter + refund
        touchedAccounts := if touchesBeneficiary then touched.insert beneficiary else touched } }

/-- SELFDESTRUCT at fork `fork`: pop the beneficiary, pay, move the balance and stop. -/
def selfdestructStep (fork : Fork) (evm : Evm fork Meter) : Except EvmError (Evm fork Meter) := do
  -- From Glamsterdam, a static frame fails first, before the pop.
  --
  -- So a static frame records no read for EIP-7928.
  if fork ≥ .glamsterdam ∧ evm.message.isStatic then throw .writeInStaticContext
  let (word, evm) ← popWord evm
  -- The beneficiary is `r = mu_s[0] mod 2^160`.
  let beneficiary := toAddressMasked word
  -- EIP-2929: a beneficiary not in the accessed set costs a cold access more, and joins the set.
  --
  -- It joins before the gas check, whether or not ether moves; a halt discards the set either way.
  let (cold, evm) := accessAddress evm beneficiary
  -- From Glamsterdam, the frame must first hold the price for a beneficiary with an account.
  --
  -- Only then does it read the beneficiary.
  --
  -- EIP-7928 asks for both.
  checkGas evm (selfdestructCost fork cold false)
  -- The read of the beneficiary, which EIP-7928 records, and which stays even on a halt.
  let evm := recordAccountRead evm beneficiary
  keepReads evm id do
    let originator := evm.message.currentTarget
    -- Whether the beneficiary gets a new account, by EIP-150 and EIP-161.
    let createsAccount := selfdestructCreatesAccount fork evm.state originator beneficiary
    -- `R_selfdestruct`, 24000 before London and 0 from London by EIP-3529.
    --
    -- It is paid only when `I_a` is not yet in `A_s`, the accounts to delete.
    --
    -- That is the first deletion of the account in the transaction.
    --
    -- So the refund is for an account that this frame and its callers do not yet delete.
    let refund :=
      if originator ∈ evm.substate.accountsToDelete then 0
      else (gasSchedule fork).REFUND_SELF_DESTRUCT
    -- The price: the base, a cold access, and a new account, by EIP-150, EIP-2929 and EIP-8038.
    let evm ← chargeGas evm (selfdestructCost fork cold createsAccount)
    -- From Glamsterdam, the state gas of a new account, after the execution gas, by EIP-8037.
    let evm ← chargeStateGas evm (selfdestructStateGas fork createsAccount)
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
  unfold selfdestructStep at h
  by_cases hs : fork ≥ .glamsterdam ∧ evm.message.isStatic = true
  · simp only [hs, and_self, ↓reduceIte] at h
    cases h
  simp only [hs, ↓reduceIte] at h
  obtain ⟨⟨_, e1⟩, h1, h⟩ := Base.bind_ok_iff.mp h
  dsimp only at h
  obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
  rcases keepReads_eq_ok h with h | ⟨e, rfl⟩
  · obtain ⟨e2, h2, h⟩ := Base.bind_ok_iff.mp h
    obtain ⟨e3, h3, h⟩ := Base.bind_ok_iff.mp h
    have paid := ((((popWord_pays h1).trans (accessAddress_pays _ _)).trans
      (recordAccountRead_pays _ _)).trans (chargeGas_pays h2)).trans (chargeStateGas_pays h3)
    have := paid.gasHeld
    unfold finishSelfdestruct at h
    split at h
    · cases h
    · obtain ⟨_, -, h⟩ := Base.bind_ok_iff.mp h
      cases h
      exact measure_lt_of_stop (show GasMeter.gasHeld e3.gas ≤ _ by omega) rfl running
  · simp only [id, measure_exceptionalHalt]
    simp [measure, running]

end EthLib.Execution.Evm
