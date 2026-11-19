module

public import EthLib.Consensus.Proofs.DepositRandomOracle
public import EthLib.Consensus.Transition.Operations
import EthLib.Consensus.Proofs.Transition.Operations

/-!
# Proofs: two deposits that one state accepts win the deposit experiment

Two deposits with different data that one state accepts give a win, with SHA-256 as the node hash.

The win reads the deposit index and the deposit root of that state.

It holds at every preset and every fork before Heze.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

/-- Two deposits with different data that one state accepts give a win, with SHA-256.

The claim reads the deposit index and the deposit root of the state.

It holds for every preset, fork before Heze, configuration and choice of signature checks. -/
theorem depositWins_of_processDeposit {preset : Preset} {fork : Fork} {config : Config}
    {checks : SignatureChecks} {before : fork < .hegota}
    {state firstAfter secondAfter : BeaconState preset fork} {first second : Deposit}
    (firstAccepted : processDeposit config checks before state first = .ok firstAfter)
    (secondAccepted : processDeposit config checks before state second = .ok secondAfter)
    (differ : first.data ≠ second.data) :
    DepositWins (extractDeposits (m := Id) Cryptography.Hash.Sha256.hash
      ⟨(state.eth1DepositIndex before).toNat, (state.eth1Data before).depositRoot, first,
        second⟩).run :=
  depositWins_sha256_iff.mpr ⟨differ, (processDeposit_ok firstAccepted).1,
    (processDeposit_ok secondAccepted).1⟩

end EthLib.Consensus
