module

import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinDriftBound
import all EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.PinSum

namespace EthLib.Consensus.Models.Network
namespace PinSum

open Base Uint64 Models DirectSafety PinSplit

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- The amounts of the queued partial withdrawals of a key that are due by a cutoff.

It is spelled as `pinTerms` spells `partialsX` and `partialsR`. -/
private def dueAmount (state : BeaconState preset fork) (electra : .pectra ≤ fork) (i : ℕ)
    (cutoff : ℕ) : ℕ :=
  (((state.pendingPartialWithdrawals electra).data.toList.filter fun w =>
    w.validatorIndex.toNat = i ∧ w.withdrawableEpoch.toNat ≤ cutoff).map (·.amount.toNat)).sum

/-- The bound `ebUp` on a key's effective balance is its largest balance or its rounded top.

The top adds the leak at the cap, the net partials and a band to the balance at R.

It reads the partials through `dueAmount`. -/
private theorem ebUp_eq (config : Config) (pulled anc fin : BeaconState preset fork)
    (electra : .pectra ≤ fork) (i t : ℕ)
    (ht : t = actualBalanceAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i +
      ((getCurrentEpoch pulled).toNat + 2 - (getCurrentEpoch fin).toNat) *
        (pinTerms config pulled anc fin).leakAt
          (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i) i +
      (dueAmount fin electra i ((getCurrentEpoch pulled).toNat + 1) -
        dueAmount pulled electra i ((getCurrentEpoch pulled).toNat + 1)) +
      preset.downwardBand + preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) :
    (pinTerms config pulled anc fin).ebUp i =
      max (max (balanceAt pulled i) (balanceAt fin i))
        (min (PinSplit2.capAt (⟨fork, pulled⟩ : ForkedBeaconState preset) i)
          (t - t % preset.EFFECTIVE_BALANCE_INCREMENT.toNat)) := by
  subst ht
  simp only [pinTerms, dueAmount, electra, ↓reduceDIte]
  rfl

end PinSum
end EthLib.Consensus.Models.Network
