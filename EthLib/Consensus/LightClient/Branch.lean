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
  -- The nodes of the proof of the generalized index in the tree of the value, as 32-byte chunks.
  (← buildProof (SszType.desc α) (SszType.toValue value) gindex).mapM toChunk

/-- A branch as a vector of its length, or the error of a branch of another length. -/
def branchVector (depth : Nat) (branch : List Bytes32) : Except LightClientError
    (Vector Bytes32 depth) :=
  -- The branch, when its length is the depth.
  (Base.exactArray depth branch.toArray (.count depth)).mapError .ssz

end EthLib.Consensus
