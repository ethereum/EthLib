module

public import EthLib.Consensus.Containers.ProposerPreferences
public import EthLib.Consensus.Proofs.Containers.Misc

/-!
# Proofs: the proposer preferences containers are lawful

Both containers have distinct field names, and each converts to and from its fields.

So their bytes decode back to them, and each of their values has a root.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType ProposerPreferences :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedProposerPreferences :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
