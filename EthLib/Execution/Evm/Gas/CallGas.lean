module

public import EthLib.Execution.Evm.Gas.Prices
public import EthLib.Execution.State.Tracker

/-!
# `Evm.Gas.CallGas`

The gas that a call pays, and the gas that it passes on to the callee.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these prices in its CALL.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[EIP-8038][eip8038] and [EIP-8037][eip8037] change both prices at Glamsterdam.

They are in Last Call, so the prices may still change.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip8037]: https://eips.ethereum.org/EIPS/eip-8037#gas-accounting-for-new-accounts
[eip8038]: https://eips.ethereum.org/EIPS/eip-8038#callcallcode
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.State (TransactionState)
open GasCosts

/-- What a call pays, and the gas that the callee gets. -/
structure MessageCallGas where
  /-- The gas that the call pays, without the growth of memory. -/
  cost : Nat
  /-- The gas that the callee gets. -/
  subCall : Nat
  deriving DecidableEq, Repr

/-- The price to send `value` with a call at fork `fork`, or nothing for a call without value.

It is 9000 up to BPO5.

From Glamsterdam, it is the price of a write to an account plus the stipend, 11300. -/
def callValueCost (fork : Fork) (value : U256) : Nat :=
  -- `C_XFER(mu) = G_callvalue` if `mu_s[2] > 0`, else 0.
  --
  -- From Glamsterdam, EIP-8038 redefines `CALL_VALUE` as `ACCOUNT_WRITE + CALL_STIPEND`.
  --
  -- That is a write to the account, 9000, plus the stipend, 2300.
  if value = 0 then 0
  else if fork ≥ .glamsterdam then ACCOUNT_WRITE + CALL_STIPEND
  else CALL_VALUE

/-- The price in execution gas of a call that creates the account of its callee, at `fork`.

Before Spurious Dragon, it is 25000 when the callee has no account.

From Spurious Dragon, by [EIP-161][eip161], it is 25000 when the call sends value to a dead account.

From Glamsterdam, it is 0, because the new account costs state gas.

[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
-/
def callNewAccountCost (fork : Fork) (state : TransactionState) (to : Address) (value : U256) :
    Nat :=
  -- From Glamsterdam, `GAS_NEW_ACCOUNT` is metered in state gas by EIP-8037, so this price is 0.
  if fork ≥ .glamsterdam then 0
  -- `C_NEW = G_newaccount` if `DEAD(sigma, t)` and `mu_s[2] > 0`, from Spurious Dragon by EIP-161.
  else if fork ≥ .spuriousDragon then
    if value = 0 ∨ state.isAccountAlive to then 0 else NEW_ACCOUNT
  -- Before, 25000 gas when the destination does not exist, whatever the value, by EIP-161 (b).
  else if state.accountExists to then 0 else NEW_ACCOUNT

/-- The gas of a call that asks for `gas`, with value `value` and an extra price `extraGas`.

The frame has `gasLeft`, and the call grows memory for `memoryCost`.

The extra price adds the access to the callee, the price of the value and that of a new account.

The price to send value is 9000 up to BPO5.

[EIP-150][eip150] adds the cap on the gas that the call passes on.

[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
-/
def messageCallGas (fork : Fork) (value : U256) (gas gasLeft memoryCost extraGas : Nat)
    (stipend : Nat := CALL_STIPEND) : MessageCallGas :=
  -- A call with value gives the callee the stipend, 2300 more gas, which the caller does not pay.
  --
  -- `G_callstipend` if `mu_s[2] > 0`, else 0.
  let stipend := if value = 0 then 0 else stipend
  -- `C_GASCAP = min(L(mu_g - C_EXTRA), mu_s[0])` if `mu_g >= C_EXTRA`, else `mu_s[0]`.
  --
  -- Here `mu_g` is the gas left after the growth of memory, by EIP-150.
  --
  -- `L(n) = n - floor(n / 64)`.
  --
  -- Before Tangerine Whistle, `C_GASCAP = mu_s[0]`, by EIP-150.
  --
  -- From Tangerine Whistle, the gas passed on is at most all but one 64th of what is left.
  --
  -- The cap of Appendix H.2 of the Yellow Paper applies this bound to every call.
  --
  -- EIP-150 applies it only when the call asks for more than it can pay.
  --
  -- They differ for a request above the bound that the frame can pay.
  --
  -- This follows the Yellow Paper.
  --
  -- When the frame cannot even pay the extra price, the call asks for its whole gas, and fails.
  let gas :=
    if fork ≥ .tangerineWhistle ∧ extraGas + memoryCost ≤ gasLeft then
      min gas (maxMessageCallGas (gasLeft - memoryCost - extraGas))
    else gas
  -- `C_CALL = C_GASCAP + C_EXTRA`, and `C_CALLGAS = C_GASCAP + G_callstipend`.
  ⟨gas + extraGas, gas + stipend⟩

/-- The price to send value exceeds the stipend.

So the callee always gets less gas than the call pays. -/
theorem stipend_lt_callValueCost {fork : Fork} {value : U256} (h : value ≠ 0) :
    CALL_STIPEND < callValueCost fork value := by
  unfold callValueCost
  simp only [h, ite_false]
  split <;> decide

/-- The callee gets less gas than the call pays.

That holds when the extra price is positive, and exceeds the stipend of a call with value. -/
theorem subCall_lt_cost {fork : Fork} {value : U256} {gas gasLeft memoryCost extraGas : Nat}
    {stipend : Nat} (pos : 0 < extraGas) (above : value ≠ 0 → stipend < extraGas) :
    (messageCallGas fork value gas gasLeft memoryCost extraGas stipend).subCall <
      (messageCallGas fork value gas gasLeft memoryCost extraGas stipend).cost := by
  unfold messageCallGas
  by_cases hv : value = 0
  · simp only [hv, ite_true]
    omega
  · simp only [hv, ite_false]
    have := above hv
    omega

/-- With no extra price and no memory, the callee gets the gas the call pays, and the stipend. -/
theorem subCall_eq_cost_add_stipend {fork : Fork} {value : U256} {gas gasLeft stipend : Nat} :
    (messageCallGas fork value gas gasLeft 0 0 stipend).subCall =
      (messageCallGas fork value gas gasLeft 0 0 stipend).cost +
        if value = 0 then 0 else stipend := by
  unfold messageCallGas
  dsimp only
  omega

end EthLib.Execution.Evm
