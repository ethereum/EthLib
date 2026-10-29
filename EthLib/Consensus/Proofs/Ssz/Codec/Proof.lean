import EthLib.Consensus.Ssz.Codec.Proof
import EthLib.Consensus.Proofs.Ssz.Merkle.Verify

/-! Laws of the node reader and the branch builder that sit directly on their definitions. -/

namespace EthLib.Consensus.Ssz

/-- Reading a list of nodes that all answer gives the list of what they answered. -/
theorem mapM_of_ok {alpha : Type} (node : alpha → Bytes) :
    ∀ items : List alpha,
      items.mapM (fun item => (.ok (node item) : Except Err Bytes)) = .ok (items.map node)
  | [] => rfl
  | item :: rest => by
    -- Reading the head answers, so the whole reading is the head with the rest behind it.
    simp [List.mapM_cons, mapM_of_ok node rest, Bind.bind, Except.bind, pure, Except.pure]

/-- The index naming the root reads back the value's own root, as it must. -/
theorem nodeRoot_root (shape : Desc) (value : Value) :
    nodeRoot shape value 1 = hashTreeRoot shape value := by
  -- The walk answers the root outright, before it reads anything of the shape.
  rw [nodeRoot, nodeRootAt]
  cases hashTreeRoot shape value <;> rfl

end EthLib.Consensus.Ssz
