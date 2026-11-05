module

public import EthLib.Consensus.Containers.InclusionList
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections

/-!
# Proofs: the inclusion list containers are lawful

Both containers have distinct field names, and each converts to and from its fields.

So their bytes decode back to them, and each of their values has a root.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType InclusionList :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedInclusionList :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
