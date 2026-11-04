module

public import EthLib.Consensus.Types
public import EthLib.Serialization.Ssz.Typed.Basic
public import EthLib.Serialization.Ssz.Typed.Container

/-!
# `Consensus.Containers.Signing`

The two containers whose roots separate the signatures of the beacon chain.

The first binds a fork version to one chain, named by the root of its genesis validators.

The second binds the root of a signed object to the domain of its signature.
-/

@[expose] public section

namespace EthLib.Consensus

open Serialization.Ssz

/-- A fork version on one chain, which the domains and the fork digests hash. -/
structure ForkData where
  /-- The version of the fork. -/
  currentVersion : Version
  /-- The root of the validators at genesis, which names the chain. -/
  genesisValidatorsRoot : Root
  deriving DecidableEq, Repr

instance : SszType ForkData :=
  .container ["current_version", "genesis_validators_root"]
    (fun d => (d.currentVersion, d.genesisValidatorsRoot))
    (fun (currentVersion, genesisValidatorsRoot) => ⟨currentVersion, genesisValidatorsRoot⟩)

/-- The root of an object with the domain under which it is signed. -/
structure SigningData where
  /-- The root of the signed object. -/
  objectRoot : Root
  /-- The domain of the signature. -/
  domain : Domain
  deriving DecidableEq, Repr

instance : SszType SigningData :=
  .container ["object_root", "domain"]
    (fun d => (d.objectRoot, d.domain))
    (fun (objectRoot, domain) => ⟨objectRoot, domain⟩)

end EthLib.Consensus
