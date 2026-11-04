module

public import EthLib.Execution.Evm.Gas
public import EthLib.Execution.State.Tracker

/-!
# `Evm.CallGas`

The gas that a call pays, and the gas that it passes on to the callee.

A call pays an extra price on top of the gas it passes on.

The extra price adds the access to the callee, 9000 to send value, and 25000 to create an account.

Before Spurious Dragon, a call creates an account when the callee has none.

From Spurious Dragon, only a call with value to a dead account creates one, by EIP-161.

A call with value gives the callee 2300 more gas, which the caller does not pay.

From Tangerine Whistle, a call passes on at most all but one 64th of the gas it has left.

That gas left is after the extra price and the growth of memory, by EIP-150.

The extra price exceeds the 2300, so the callee always gets less gas than the call pays.

Appendix H.2 of the Yellow Paper, Shanghai version, defines these prices in its CALL.

Source: [`Paper.tex` at `efc5f9a`][yp] of the Yellow Paper.

[EIP-150][eip150] adds the cap, and [EIP-161][eip161] changes the price of a new account.

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
[eip150]: https://eips.ethereum.org/EIPS/eip-150#specification
[eip161]: https://eips.ethereum.org/EIPS/eip-161#specification
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

/-- The price to send `value` with a call: 9000, or nothing for a call without value. -/
def callValueCost (value : U256) : Nat :=
  if value = 0 then 0 else CALL_VALUE

/-- The price of a call that creates the account of its callee, at fork `fork`.

Before Spurious Dragon, it is 25000 when the callee has no account.

From Spurious Dragon, it is 25000 when the call sends value to a dead account. -/
def callNewAccountCost (fork : Fork) (state : TransactionState) (to : Address) (value : U256) :
    Nat :=
  if fork ≥ .spuriousDragon then
    if value = 0 ∨ state.isAccountAlive to then 0 else NEW_ACCOUNT
  else if state.accountExists to then 0 else NEW_ACCOUNT

/-- The gas of a call that asks for `gas`, with value `value` and an extra price `extraGas`.

The frame has `gasLeft`, and the call grows memory for `memoryCost`.

The callee gets the stipend on top when the call sends value.

From Tangerine Whistle, the gas passed on is at most all but one 64th of what is left.

When the frame cannot even pay the extra price, the call asks for its whole gas, and fails. -/
def messageCallGas (fork : Fork) (value : U256) (gas gasLeft memoryCost extraGas : Nat)
    (stipend : Nat := CALL_STIPEND) : MessageCallGas :=
  let stipend := if value = 0 then 0 else stipend
  let gas :=
    if fork ≥ .tangerineWhistle ∧ extraGas + memoryCost ≤ gasLeft then
      min gas (maxMessageCallGas (gasLeft - memoryCost - extraGas))
    else gas
  ⟨gas + extraGas, gas + stipend⟩

end EthLib.Execution.Evm
