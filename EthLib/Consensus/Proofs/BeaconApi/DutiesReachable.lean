module

public import EthLib.Consensus.Proofs.BeaconApi.Duties
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.AssignedProposers

/-!
# Proofs: a proposer answer on a state that a run reaches

From Fulu a proposer answer reads the lookahead only for a served epoch.

Along a run from genesis each entry names a validator, so looking it up in the registry cannot fail.

So, under the two bounds on slots, such an answer fails only with code 400.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- From Fulu, a proposer answer on a state that a run reaches fails only with code 400.

The run starts from a genesis state built from deposits.

The slots of the requested epoch must fit in 64 bits.

The slot of the state plus the length of the buffer of roots must be at most `2^64`. -/
theorem dutiesResponse_proposer_error_code_of_run {g x : ForkedBeaconState preset}
    {kind : DutyKind} {epoch : Epoch} {indices : List ValidatorIndex} {genesisRoot : Root}
    {error : ErrorMessage} (genesis : Genesis config checks g) (run : Run config checks g x)
    -- From Fulu the answers read the proposers of a served epoch from the lookahead.
    (fulu : .fusaka ≤ x.fork)
    -- One of the two proposer answers.
    (version : kind = .proposerV1 ∨ kind = .proposerV2)
    -- The slots of the requested epoch fit in 64 bits.
    (slotsFit : (epoch.toNat + 1) * preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 64)
    -- The slot of the state plus the length of the buffer of roots is at most `2^64`.
    (room : x.state.slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤ 2 ^ 64)
    (failed : dutiesResponse config x.state kind epoch indices genesisRoot = .error error) :
    error.code = 400 := by
  refine dutiesResponse_proposer_error_code fulu version slotsFit room
    (fun proposer member => ?_) failed
  -- The proposer names a validator, so its index is inside the registry.
  obtain ⟨_, found, -⟩ := Run.assignedProposers genesis run fulu proposer (by simpa using member)
  exact (Array.getElem?_eq_some_iff.mp found).1

end EthLib.Consensus.BeaconApi
