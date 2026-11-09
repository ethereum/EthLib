module

public import EthLib.Cryptography.Bls.KeyPath

/-!
# Proofs: ERC-2334 key paths

Paths have the required purpose and at least four child indices.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.KeyPath

/-- Every path includes purpose, coin type, account and use. -/
theorem indices_length_ge_four (path : Path) : 4 ≤ path.indices.length := by
  simp [Path.indices]

/-- The withdrawal path uses Ethereum coin type 3600 and use zero. -/
theorem withdrawal_path_indices (index : UInt32) :
    (withdrawalPath index).indices = [12381, 3600, index, 0] := rfl

/-- The signing path is child zero of the withdrawal path. -/
theorem signing_path_indices (index : UInt32) :
    (signingPath index).indices = (withdrawalPath index).indices ++ [0] := rfl

end EthLib.Cryptography.Bls.KeyPath
