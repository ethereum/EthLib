module

public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Constants
public import EthLib.Consensus.Preset
public import Mathlib.Data.Nat.Sqrt

/-!
# Proofs: constants of the beacon chain

The integer square root of the largest 64-bit unsigned integer is the constant that names it.

The domain types differ, so a signature of one kind of message never serves another.

The types of the requests of the execution layer differ and increase.

The flag of a builder index is the registry limit, so no validator index before Gloas has it.
-/

@[expose] public section

namespace EthLib.Consensus

open EthLib.Base.Uint64 (integerSquareroot toNat_integerSquareroot)

/-- The constant is the integer square root of `2^64 - 1`, since `2^64 - 1 = s^2 + 2s` for it. -/
theorem UINT64_MAX_SQRT_eq : UINT64_MAX_SQRT = integerSquareroot UINT64_MAX := by
  apply UInt64.toNat_inj.mp
  rw [toNat_integerSquareroot]
  have h : UINT64_MAX.toNat = 4294967295 * 4294967295 + 2 * 4294967295 := by decide
  rw [h, Nat.sqrt_add_eq 4294967295 (by omega)]
  rfl

/-- The sixteen domain types, from Phase 0 to Heze, are pairwise distinct. -/
theorem domainTypes_nodup :
    [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_RANDAO, DOMAIN_DEPOSIT,
      DOMAIN_VOLUNTARY_EXIT, DOMAIN_SELECTION_PROOF, DOMAIN_AGGREGATE_AND_PROOF,
      DOMAIN_SYNC_COMMITTEE, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF, DOMAIN_CONTRIBUTION_AND_PROOF,
      DOMAIN_BLS_TO_EXECUTION_CHANGE, DOMAIN_BEACON_BUILDER, DOMAIN_PTC_ATTESTER,
      DOMAIN_PROPOSER_PREFERENCES, DOMAIN_BUILDER_DEPOSIT,
      DOMAIN_INCLUSION_LIST_COMMITTEE].Nodup := by
  decide

/-- No domain type of a fork has a bit of the application mask set. -/
theorem domainTypes_not_application :
    ∀ domain ∈ [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_RANDAO, DOMAIN_DEPOSIT,
      DOMAIN_VOLUNTARY_EXIT, DOMAIN_SELECTION_PROOF, DOMAIN_AGGREGATE_AND_PROOF,
      DOMAIN_SYNC_COMMITTEE, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF, DOMAIN_CONTRIBUTION_AND_PROOF,
      DOMAIN_BLS_TO_EXECUTION_CHANGE, DOMAIN_BEACON_BUILDER, DOMAIN_PTC_ATTESTER,
      DOMAIN_PROPOSER_PREFERENCES, DOMAIN_BUILDER_DEPOSIT, DOMAIN_INCLUSION_LIST_COMMITTEE],
      ∀ i : Fin 4, domain[i] &&& DOMAIN_APPLICATION_MASK[i] = 0 := by
  decide

/-- The five request types, from Electra to Gloas, strictly increase. -/
theorem requestTypes_increasing :
    [DEPOSIT_REQUEST_TYPE, WITHDRAWAL_REQUEST_TYPE, CONSOLIDATION_REQUEST_TYPE,
      BUILDER_DEPOSIT_REQUEST_TYPE, BUILDER_EXIT_REQUEST_TYPE].Pairwise (·[0] < ·[0]) := by
  decide

/-- The flag of a builder index equals the registry limit of both presets. -/
theorem BUILDER_INDEX_FLAG_eq_registry_limit :
    BUILDER_INDEX_FLAG = Preset.mainnet.VALIDATOR_REGISTRY_LIMIT ∧
      BUILDER_INDEX_FLAG = Preset.minimal.VALIDATOR_REGISTRY_LIMIT := by
  decide

end EthLib.Consensus
