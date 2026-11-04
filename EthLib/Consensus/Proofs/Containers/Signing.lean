module

public import EthLib.Consensus.Containers.Signing
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# Proofs: the signing containers are lawful

Both containers have distinct field names, and each conversion undoes the other.

So their bytes decode back to them, and each of their values has a root.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

instance : LawfulSszType ForkData :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SigningData :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus
