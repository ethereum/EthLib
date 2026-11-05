module

public import EthLib.Consensus.LightClient.Sync
public import EthLib.Serialization.Ssz.Codec.Proof

/-!
# `Consensus.LightClient.Branch`

The Merkle branches that a full node gives to a light client.

A branch proves one node of a value, from the node up to the root.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

/-- The branch that proves the node at a generalized index of a value, from the node up. -/
def computeMerkleProof {α : Type} [SszType α] (value : α) (gindex : Nat) :
    Except Err (List Bytes32) := do
  (← buildProof (SszType.desc α) (SszType.toValue value) gindex).mapM toChunk

/-- A branch as a vector of its length, or the error of a branch of another length. -/
def branchVector (depth : Nat) (branch : List Bytes32) : Except LightClientError
    (Vector Bytes32 depth) :=
  if h : branch.length = depth then .ok ⟨branch.toArray, by simpa using h⟩
  else .error (.ssz (.count depth branch.length))

end EthLib.Consensus
