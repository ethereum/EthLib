module

public import EthLib.Execution.Evm.CallGas
public import EthLib.Execution.Proofs.Evm.Gas

/-!
# Proofs: `Evm.CallGas`

The callee gets less gas than the call pays, when the extra price exceeds the stipend.

So a callee always gets less gas than its caller had before the call.

From Tangerine Whistle, a call passes on at most all but one 64th of the gas left.

From Tangerine Whistle, a frame that can pay the extra price can always pay the whole call.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

/-- The price to send value exceeds the stipend. -/
theorem stipend_lt_callValueCost {value : U256} (h : value ≠ 0) :
    CALL_STIPEND < callValueCost value := by
  unfold callValueCost
  simp only [h, ite_false]
  decide

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

/-- A callee gets less gas than its caller had before a call that it could pay. -/
theorem subCall_lt_gasLeft {fork : Fork} {value : U256} {gas gasLeft memoryCost extraGas : Nat}
    {stipend : Nat} (pos : 0 < extraGas) (above : value ≠ 0 → stipend < extraGas)
    (paid : (messageCallGas fork value gas gasLeft memoryCost extraGas stipend).cost +
      memoryCost ≤ gasLeft) :
    (messageCallGas fork value gas gasLeft memoryCost extraGas stipend).subCall < gasLeft := by
  have := subCall_lt_cost (fork := fork) (gas := gas) (gasLeft := gasLeft)
    (memoryCost := memoryCost) pos above
  omega

/-- From Tangerine Whistle, a call passes on at most all but one 64th of what is left.

What is left is the gas after the extra price and memory, and the stipend comes on top. -/
theorem subCall_le_maxMessageCallGas {fork : Fork} (h : fork ≥ .tangerineWhistle)
    {value : U256} {gas gasLeft memoryCost extraGas stipend : Nat}
    (enough : extraGas + memoryCost ≤ gasLeft) :
    (messageCallGas fork value gas gasLeft memoryCost extraGas stipend).subCall ≤
      maxMessageCallGas (gasLeft - memoryCost - extraGas) + stipend := by
  unfold messageCallGas
  simp only [h, enough, and_self, ite_true]
  split <;> omega

/-- From Tangerine Whistle, a frame that can pay the extra price and memory can pay the call. -/
theorem cost_add_memoryCost_le {fork : Fork} (h : fork ≥ .tangerineWhistle)
    {value : U256} {gas gasLeft memoryCost extraGas stipend : Nat}
    (enough : extraGas + memoryCost ≤ gasLeft) :
    (messageCallGas fork value gas gasLeft memoryCost extraGas stipend).cost + memoryCost ≤
      gasLeft := by
  have := maxMessageCallGas_le (gasLeft - memoryCost - extraGas)
  unfold messageCallGas
  simp only [h, enough, and_self, ite_true]
  omega

end EthLib.Execution.Evm
