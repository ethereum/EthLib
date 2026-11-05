module

public import EthLib.Consensus.PqKeys.Containers
public import EthLib.Consensus.Proofs.Containers.Misc

/-!
# Proofs: the containers of the post-quantum key registry

Each container has distinct field names, and converts to and from the tuple of its fields.

So its bytes decode back to it, two values with one encoding are equal, and each value has a root.

Every container here has a fixed size, so each of its values serializes to that many bytes.
-/

@[expose] public section

namespace EthLib.Consensus.PqKeys

open Serialization.Ssz SszType

instance : LawfulSszType PQKeyMaterial := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PQKeyRegistration :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType PQKeyPossession := .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType SignedPQKeyRegistration :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- The two domain types of the registry differ from each other and from those up to Heze.

A domain starts with its domain type, so no other kind of message shares a registry domain. -/
theorem domainTypes_nodup :
    [DOMAIN_BEACON_PROPOSER, DOMAIN_BEACON_ATTESTER, DOMAIN_RANDAO, DOMAIN_DEPOSIT,
      DOMAIN_VOLUNTARY_EXIT, DOMAIN_SELECTION_PROOF, DOMAIN_AGGREGATE_AND_PROOF,
      DOMAIN_APPLICATION_MASK, DOMAIN_SYNC_COMMITTEE, DOMAIN_SYNC_COMMITTEE_SELECTION_PROOF,
      DOMAIN_CONTRIBUTION_AND_PROOF, DOMAIN_BLS_TO_EXECUTION_CHANGE, DOMAIN_BEACON_BUILDER,
      DOMAIN_PTC_ATTESTER, DOMAIN_PROPOSER_PREFERENCES, DOMAIN_BUILDER_DEPOSIT,
      DOMAIN_INCLUSION_LIST_COMMITTEE, DOMAIN_PQ_KEY_REGISTRATION,
      DOMAIN_PQ_KEY_POSSESSION].Nodup := by
  decide

/-- The keys of an index serialize to 64 bytes: 32 for each key. -/
theorem pqKeyMaterial_serialize_size {k : PQKeyMaterial} {data : ByteArray}
    (wrote : serialize k = .ok data) : data.size = 64 :=
  serialize_size (by decide) wrote

/-- A registration message serializes to 80 bytes: the index, the keys and the epoch. -/
theorem pqKeyRegistration_serialize_size {r : PQKeyRegistration} {data : ByteArray}
    (wrote : serialize r = .ok data) : data.size = 80 :=
  serialize_size (by decide) wrote

/-- A possession message serializes to 80 bytes: 48 for the BLS key, 32 for the leanXMSS key. -/
theorem pqKeyPossession_serialize_size {p : PQKeyPossession} {data : ByteArray}
    (wrote : serialize p = .ok data) : data.size = 80 :=
  serialize_size (by decide) wrote

/-- A signed registration serializes to 2580 bytes, 2404 of them for the proof of possession. -/
theorem signedPQKeyRegistration_serialize_size {s : SignedPQKeyRegistration} {data : ByteArray}
    (wrote : serialize s = .ok data) : data.size = 2580 :=
  serialize_size (by decide) wrote

end EthLib.Consensus.PqKeys
