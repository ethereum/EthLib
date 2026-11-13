module

public import EthLib.Execution.Rpc.Errors

/-!
# Proofs: the error groups

Every code of a group that declares a range lies in that range.

No code appears twice, in one group or in two.

The code of pruned history is in no group.
-/

public section

namespace EthLib.Execution.Rpc

/-- Every code of a group that declares a range lies in that range. -/
theorem code_mem_range : ∀ g ∈ errorGroups, ∀ r, g.range = some r →
    ∀ e ∈ g.errors, r.1 ≤ e.code ∧ e.code ≤ r.2 := by
  decide

/-- No code appears twice among the groups. -/
theorem codes_nodup : (errorGroups.flatMap fun g => g.errors.map (·.code)).Nodup := by
  decide

/-- The code of pruned history is in no group. -/
theorem prunedHistoryUnavailable_not_mem :
    prunedHistoryUnavailable.code ∉ errorGroups.flatMap fun g => g.errors.map (·.code) := by
  decide

end EthLib.Execution.Rpc
