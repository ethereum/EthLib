module

public import EthLib.Base.Proofs.Address
public import EthLib.Execution.Evm.Instructions.SelfDestruct

/-!
# Proofs: `Evm.Call.TransferLog`

Before Glamsterdam, a move of ether writes no log.

From Glamsterdam, it writes exactly one log when it moves a positive amount to another account.

That log comes from the system address, and its last two topics hold the sender and the recipient.

From Glamsterdam, SELFDESTRUCT writes that log for the balance it moves.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256 toAddressMasked)
open EthLib.Execution.Blocks (Log)

variable {fork : Fork}

/-- Before Glamsterdam, a move of ether writes no log. -/
theorem pushTransferLog_of_lt (h : fork < .glamsterdam) (logs : Array Log)
    (sender recipient : Address) (amount : U256) :
    pushTransferLog fork logs sender recipient amount = logs := by
  have : ¬fork ≥ .glamsterdam := Nat.not_le_of_lt h
  simp only [pushTransferLog, this, false_and, ↓reduceIte]

/-- From Glamsterdam, a move of a positive amount to another account writes its transfer log. -/
theorem pushTransferLog_of_glamsterdam (h : fork ≥ .glamsterdam) (logs : Array Log)
    {sender recipient : Address} {amount : U256} (pos : amount ≠ 0) (hne : sender ≠ recipient) :
    pushTransferLog fork logs sender recipient amount =
      logs.push (transferLog sender recipient amount) := by
  simp only [pushTransferLog, h, pos, hne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]

/-- A move of 0 wei, or from an account to itself, writes no log. -/
theorem pushTransferLog_eq_self (logs : Array Log) {sender recipient : Address} {amount : U256}
    (h : amount = 0 ∨ sender = recipient) :
    pushTransferLog fork logs sender recipient amount = logs := by
  unfold pushTransferLog
  rcases h with h | h <;> simp [h]

/-- A transfer log comes from the system address. -/
theorem transferLog_address (sender recipient : Address) (amount : U256) :
    (transferLog sender recipient amount).address = SYSTEM_ADDRESS := rfl

/-- The topics of a transfer log are the event hash, then the sender and the recipient as words. -/
theorem transferLog_topics (sender recipient : Address) (amount : U256) :
    (transferLog sender recipient amount).topics =
      [TRANSFER_TOPIC, U256.toBeBytes sender.toU256, U256.toBeBytes recipient.toU256] := rfl

/-- An address is the last 20 bytes of its word, so a topic gives back its address. -/
theorem drop_toBeBytes_toU256 (address : Address) :
    (U256.toBeBytes address.toU256).drop 12 = address :=
  EthLib.Base.toAddressMasked_toU256 address

/-- SELFDESTRUCT writes the transfer log of the balance it moves, none before Glamsterdam. -/
theorem finishSelfdestruct_logs {beneficiary : Address} {refund : Nat} {Meter : Type}
    {evm after : Evm fork Meter} (h : finishSelfdestruct fork beneficiary refund evm = .ok after) :
    after.substate.logs =
      pushTransferLog fork evm.substate.logs evm.message.currentTarget beneficiary
        (evm.state.getAccount evm.message.currentTarget).balance := by
  unfold finishSelfdestruct at h
  split at h
  · cases h
  · obtain ⟨state, -, h⟩ := Base.bind_ok_iff.mp h
    cases h
    rfl

end EthLib.Execution.Evm
