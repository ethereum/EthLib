module

public import EthLib.Consensus.Proofs.Transition.DepositCarryCore
import EthLib.Consensus.Proofs.Transition.Totality.ShapeBlock

/-!
# Deposit carry across blocks

The core preservation proofs are separate because validator caps read them before block totality.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Fork}
  {s t : BeaconState preset fork}

/-- A block keeps the deposit carry.

This holds at every fork.

From Gloas the parent's deposit requests join the pending deposits, and the carry stays. -/
theorem depositCarry_processBlock {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (ok : processBlock config checks engine s block = .ok t) :
    t.depositBalanceToConsume = s.depositBalanceToConsume :=
  (processBlock_blockKept ok).depositCarry

end EthLib.Consensus
