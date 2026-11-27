module

public import EthLib.Execution.Blocks.SystemCall
public import EthLib.Execution.Proofs.Transactions.StorageAt

/-!
# Proofs: a system call keeps the storage of an account it does not read

A system call of a block runs one message from the system address, as a transaction does.

So it keeps or wipes the storage of an account, unless it reads the account.

It also keeps or wipes it when no frame of its message runs at the account.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Execution.Evm
open EthLib.Execution.Transactions (keptOrRead_processMessageCall)
open EthLib.Execution.State.TransactionState (KeptOrWiped)

variable {fork : Fork} {address : Address}

/-- A system call keeps or wipes the storage of `address`, unless it reads the account.

Every frame at `address` runs from a state that has read the account. -/
theorem keptOrRead_systemCall {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out) :
    KeptOrRead address (.ofBlock block) out.state := by
  -- The message of the call runs at its target.
  have recipient : ∀ to, (systemMessage env target data).target = some to →
      to = (systemMessage env target data).currentTarget := fun _ hto => (Option.some.inj hto).symm
  unfold systemCall at h
  dsimp only at h
  split at h
  · obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact keptOrRead_processMessageCall recipient hcall
  · obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact keptOrRead_processMessageCall recipient hcall

/-- A system call keeps or wipes the storage of `address`, if no frame of its message runs there.

It runs with the gas meter of its fork. -/
theorem keptOrWiped_systemCall_of_away {env : BlockEnvironment fork} {block : State.BlockState}
    {target : Address} {data : ByteArray} {out : SystemCallOutput}
    (h : systemCall env block target data = .ok out)
    (away : fork < .glamsterdam → Transactions.CallAway (Meter := Nat) address env.chainId.toNat
      (systemMessage env target data) (.ofBlock block) (systemSubstate env target) [] ∅)
    (awayState : .glamsterdam ≤ fork → Transactions.CallAway (Meter := StateGasMeter) address
      env.chainId.toNat (systemMessage env target data) (.ofBlock block) (systemSubstate env target)
      [] ∅) :
    KeptOrWiped address (.ofBlock block) out.state := by
  unfold systemCall at h
  dsimp only at h
  split at h
  · rename_i hglam
    obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact Transactions.keptOrWiped_processMessageCall_of_away hcall (awayState hglam)
  · rename_i hglam
    obtain ⟨call, hcall, h⟩ := bind_ok_iff.mp h
    cases h
    exact Transactions.keptOrWiped_processMessageCall_of_away hcall (away (Nat.lt_of_not_le hglam))

end EthLib.Execution.Blocks
