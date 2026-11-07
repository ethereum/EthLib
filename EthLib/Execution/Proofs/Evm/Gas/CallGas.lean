module

public import EthLib.Execution.Evm.Gas.CallGas
public import EthLib.Execution.Proofs.Evm.Gas.Prices

/-!
# Proofs: `Evm.Gas.CallGas`

A callee gets less gas than its caller had before a call that it could pay.

From Tangerine Whistle, a call passes on at most all but one 64th of the gas left.

From Tangerine Whistle, a frame that can pay the extra price can always pay the whole call.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Fork U256)
open GasCosts

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

/-- The gas of a call, from Tangerine Whistle, when the frame can pay the extra price and memory.

The call passes on at most all but one 64th of what is left, and pays that and the extra price.

The stipend comes on top of the gas it passes on, for a call with value. -/
theorem messageCallGas_of_le {fork : Fork} (h : fork ≥ .tangerineWhistle)
    {value : U256} {gas gasLeft memoryCost extraGas stipend : Nat}
    (enough : extraGas + memoryCost ≤ gasLeft) :
    messageCallGas fork value gas gasLeft memoryCost extraGas stipend =
      ⟨min gas (maxMessageCallGas (gasLeft - memoryCost - extraGas)) + extraGas,
        min gas (maxMessageCallGas (gasLeft - memoryCost - extraGas)) +
          if value = 0 then 0 else stipend⟩ := by
  unfold messageCallGas
  simp only [h, enough, and_self, ite_true]

end EthLib.Execution.Evm
