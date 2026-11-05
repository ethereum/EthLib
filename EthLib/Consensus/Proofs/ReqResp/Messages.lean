module

public import EthLib.Consensus.ReqResp.Messages
public import EthLib.Networking.Proofs.Gossip.Topic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container
public import EthLib.Serialization.Proofs.Ssz.Typed.Since
public import EthLib.Serialization.Proofs.Ssz.Type.Legality

/-!
# `Consensus.Proofs.ReqResp.Messages`

Properties of the request and response messages of the consensus layer.

- Each protocol ID parses back to its protocol and its version.
- So no two protocol IDs of a fork are one string.
- A protocol ID of a fork is a protocol ID of every later fork up to Fulu.
- From Gloas a fork has no list of protocol IDs yet.
- The status, the metadata and the container requests are lawful SSZ containers at every fork.
- A goodbye code is recovered from the reason it names.
-/

@[expose] public section

namespace EthLib.Consensus.Proofs.ReqResp.Messages

open EthLib.Base
open EthLib.Consensus
open EthLib.Serialization.Ssz
open EthLib.Networking.Gossip
open EthLib.Networking.Proofs.Gossip.Topic

/-- The characters of a protocol ID: the prefix, the name and `/`, the version, the suffix. -/
theorem toList_toString (id : ProtocolId) :
    id.toString.toList = "/eth2/beacon_chain/req/".toList ++
      (((id.protocol.name ++ "/").toList ++ Nat.toDigits 10 id.version) ++
      "/ssz_snappy".toList) := by
  simp [ProtocolId.toString, Nat.toList_repr]

/-- The name of one protocol, followed by `/`, starts the ID body of another only if equal. -/
theorem find?_name (protocol : ReqRespProtocol) (digits : List Char) :
    ReqRespProtocol.all.find? (fun p => (p.name ++ "/").toList.isPrefixOf
      ((protocol.name ++ "/").toList ++ digits)) = some protocol := by
  -- No name, followed by `/`, is a prefix of another name followed by `/`.
  have prefixOf : ∀ p q : ReqRespProtocol, (p.name ++ "/").toList.isPrefixOf
      ((q.name ++ "/").toList ++ digits) = (p == q) := by
    intro p q
    by_cases same : p = q
    · subst same
      simp [List.isPrefixOf_iff_prefix]
    · have apart : (p.name ++ "/").toList.isPrefixOf (q.name ++ "/").toList = false ∧
          (q.name ++ "/").toList.isPrefixOf (p.name ++ "/").toList = false := by
        cases p <;> cases q <;> first | exact absurd rfl same | decide
      rw [beq_false_of_ne same, Bool.eq_false_iff, ne_eq, List.isPrefixOf_iff_prefix]
      intro prefixed
      rcases List.prefix_or_prefix_of_prefix prefixed (List.prefix_append _ _) with left | right
      · rw [← List.isPrefixOf_iff_prefix, apart.1] at left
        cases left
      · rw [← List.isPrefixOf_iff_prefix, apart.2] at right
        cases right
  simp only [prefixOf]
  cases protocol <;> rfl

/-- A protocol ID with a positive version below `2^64` parses back to its protocol and version. -/
theorem parse?_toString (protocol : ReqRespProtocol) {version : Nat} (positive : 0 < version)
    (small : version < 2 ^ 64) :
    ProtocolId.parse? (ProtocolId.toString ⟨protocol, version⟩) = some ⟨protocol, version⟩ := by
  have back : version.toUInt64.toNat = version := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small]
  have nonzero : version.toUInt64 ≠ 0 := by
    intro zero
    have := congrArg UInt64.toNat zero
    rw [back] at this
    simp at this
    omega
  have drop : ((protocol.name ++ "/").toList ++ Nat.toDigits 10 version).drop
      (protocol.name.length + 1) = Nat.toDigits 10 version := by
    rw [List.drop_append_of_le_length (by simp [String.length_toList])]
    simp [String.length_toList]
  have digits : parseSubnetId (Nat.toDigits 10 version) = some version.toUInt64 := by
    have := parseSubnetId_toDigits version.toUInt64
    rwa [back] at this
  rw [ProtocolId.parse?, toList_toString, dropPrefix?_append]
  simp only [Option.bind_eq_bind, Option.bind_some, dropSuffix?_append, find?_name, drop, digits,
    nonzero, ite_false, back]

/-- The protocol IDs of a fork are missing exactly from Gloas on. -/
theorem protocolIds_eq_none_iff {fork : Fork} :
    protocolIds fork = none ↔ .glamsterdam ≤ fork := by
  unfold protocolIds
  split <;> simp_all

/-- Every protocol ID of a fork parses back to itself. -/
theorem parse?_protocolIds {fork : Fork} {ids : List ProtocolId} {id : ProtocolId}
    (listed : protocolIds fork = some ids) (mem : id ∈ ids) :
    ProtocolId.parse? id.toString = some id := by
  have bounds : 0 < id.version ∧ id.version ≤ 3 := by
    unfold protocolIds at listed
    split at listed
    · cases listed
    cases listed
    simp only [List.mem_flatMap, List.mem_map] at mem
    obtain ⟨protocol, _, version, member, rfl⟩ := mem
    show 0 < version ∧ version ≤ 3
    cases protocol <;> simp only [ReqRespProtocol.versions] at member <;>
      repeat' (split at member)
    all_goals simp at member
    all_goals omega
  exact parse?_toString id.protocol bounds.1 (by omega)

/-- A protocol ID of a fork is a protocol ID of every later fork that has a list. -/
theorem mem_protocolIds_of_le {fork later : Fork} (le : fork ≤ later) {ids ids' : List ProtocolId}
    (listed : protocolIds fork = some ids) (listed' : protocolIds later = some ids')
    {id : ProtocolId} (mem : id ∈ ids) : id ∈ ids' := by
  unfold protocolIds at listed listed'
  split at listed
  · cases listed
  split at listed'
  · cases listed'
  cases listed
  cases listed'
  simp only [List.mem_flatMap, List.mem_map] at mem ⊢
  obtain ⟨protocol, all, version, member, rfl⟩ := mem
  refine ⟨protocol, all, version, ?_, rfl⟩
  have up : ∀ {first : Fork}, first ≤ fork → first ≤ later := fun h => Nat.le_trans h le
  -- A version is listed under the forks from some fork on, which then holds later too.
  cases protocol <;> simp only [ReqRespProtocol.versions] at member ⊢ <;>
    (repeat' split at member) <;> (repeat' split)
  all_goals simp_all
  all_goals omega

/-- Two protocol IDs of a fork with one string are one ID. -/
theorem toString_injective {fork : Fork} {ids : List ProtocolId} {a b : ProtocolId}
    (listed : protocolIds fork = some ids) (left : a ∈ ids) (right : b ∈ ids)
    (same : a.toString = b.toString) : a = b := by
  have := parse?_protocolIds listed left
  rw [same, parse?_protocolIds listed right] at this
  exact (Option.some.inj this).symm

/-- A goodbye code is recovered from the reason it names. -/
theorem GoodbyeReason.toCode_ofCode (code : UInt64) :
    (GoodbyeReason.ofCode code).toCode = code := by
  unfold GoodbyeReason.ofCode
  repeat' split
  all_goals simp_all [GoodbyeReason.toCode]

/-- The field names of a status are distinct at every fork. -/
theorem Status.names_nodup (fork : Fork) :
    (["fork_digest", "finalized_root", "finalized_epoch", "head_root", "head_slot"] ++
      sinceNames .fusaka fork ["earliest_available_slot"]).Nodup := by
  have all : (["fork_digest", "finalized_root", "finalized_epoch", "head_root", "head_slot",
      "earliest_available_slot"] : List String).Nodup := by decide
  exact all.sublist ((List.Sublist.refl _).append (sinceNames_sublist _))

/-- At every fork, the status is a lawful SSZ container. -/
instance {fork : Fork} : LawfulSszType (Status fork) :=
  .container
    ⟨by by_cases fulu : Fork.fusaka ≤ fork <;> simp [sinceNames, SszFields.descs, fulu],
     by simp,
     firstDuplicate_of_nodup _ (Status.names_nodup fork)⟩
    (fun _ => rfl) (fun _ => rfl)

/-- The field names of the metadata are distinct at every fork. -/
theorem MetaData.names_nodup (fork : Fork) :
    (["seq_number", "attnets"] ++ sinceNames .altair fork ["syncnets"] ++
      sinceNames .fusaka fork ["custody_group_count"]).Nodup := by
  have all : (["seq_number", "attnets", "syncnets", "custody_group_count"] :
      List String).Nodup := by decide
  exact all.sublist (((List.Sublist.refl _).append (sinceNames_sublist _)).append
    (sinceNames_sublist _))

instance : NeZero Networking.Enr.SYNC_COMMITTEE_SUBNET_COUNT := ⟨by decide⟩

/-- At every fork, the metadata is a lawful SSZ container, when there is an attestation subnet. -/
instance {config : Config} {fork : Fork} [NeZero config.ATTESTATION_SUBNET_COUNT.toNat] :
    LawfulSszType (MetaData config fork) :=
  .container
    ⟨by
      by_cases altair : Fork.altair ≤ fork <;> by_cases fulu : Fork.fusaka ≤ fork <;>
        simp [sinceNames, SszFields.descs, altair, fulu],
     by simp,
     firstDuplicate_of_nodup _ (MetaData.names_nodup fork)⟩
    (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BeaconBlocksByRangeRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType LightClientUpdatesByRangeRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BlobSidecarsByRangeRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

instance {preset : Preset} : LawfulSszType (DataColumnSidecarsByRangeRequest preset) :=
  .container ⟨rfl, by simp, by decide⟩ (fun _ => rfl) (fun _ => rfl)

instance : LawfulSszType BeaconBlocksByHeadRequest :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

end EthLib.Consensus.Proofs.ReqResp.Messages
