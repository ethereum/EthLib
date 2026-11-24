module

public import EthLib.Consensus.Proofs.BeaconApi.Committees
public import EthLib.Consensus.Proofs.Transition.Trace
import EthLib.Consensus.Proofs.Transition.SyncCommitteeProvenance

/-!
# Proofs: the sync committees answer on a state that a run from genesis reaches

On such a state from Altair, a validator of the registry holds each key of both committees.

So the lookup of each seat succeeds, and every error of the answer has code 400.
-/

@[expose] public section

namespace EthLib.Consensus.BeaconApi

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- Every error of the sync committees answer on a state of a run from a genesis has code 400.

The genesis is built from deposits. -/
theorem syncCommitteesResponse_error_code_of_run {g x : ForkedBeaconState preset}
    (genesis : Genesis config checks g) (run : Run config checks g x) {epoch : Option Epoch}
    {error : ErrorMessage} (failed : syncCommitteesResponse x.state epoch = .error error) :
    error.code = 400 := by
  -- A key of the registry is the key of some validator of the registry.
  have held (key) (member : key ∈ validatorKeys x.state) :
      ∃ validator ∈ x.state.validators.data, validator.pubkey = key := by
    simpa [validatorKeys] using member
  refine syncCommitteesResponse_error_code_of_keys (fun altair => ?_) failed
  -- The run keeps each key of both committees in the registry.
  obtain ⟨current, next⟩ := run.syncCommittee_keys genesis altair
  exact ⟨fun key member => held key (current key member),
    fun key member => held key (next key member)⟩
