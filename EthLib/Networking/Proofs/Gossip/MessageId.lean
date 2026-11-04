module

public import EthLib.Networking.Gossip.MessageId
public import EthLib.Serialization.Proofs.Ssz.Codec.LengthBinding
public import EthLib.Serialization.Proofs.Ssz.Codec.Table

/-!
# `Networking.Proofs.Gossip.MessageId`

Properties of the gossip message ID.

- Every ID is 20 bytes.
- Data that decompresses is hashed as its payload under the domain `01 00 00 00`.
- Other data is hashed as it is under the domain `00 00 00 00`.
- Two byte strings that decompress to one payload get one ID, on the same topic for Altair.
- Each hash input determines its domain and its bytes, and under Altair its topic.
  The topic must be shorter than 2^64 bytes.
  So two messages that differ in one share an ID only if SHA-256, cut to 20 bytes, collides.

The kernel checks everything here, so no `native_decide` or `bv_decide` axiom appears.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.MessageId

open EthLib.Networking.Gossip
open EthLib.Networking.Snappy (decompress SnappyError)
open EthLib.Cryptography.Hash (sha256)
open EthLib.Serialization.Ssz (uintBytes_size uintBytes_injective)

/-! ## Length -/

/-- The first 20 bytes of a SHA-256 digest are 20 bytes, since the digest has 32. -/
private theorem sha256_extract_size (input : ByteArray) : ((sha256 input).extract 0 20).size = 20 := by
  simp [sha256, ByteArray.size_extract]

/-- Every Phase 0 message ID is 20 bytes. -/
theorem Phase0.messageId_size (data : ByteArray) : (Phase0.messageId data).size = 20 := by
  unfold Phase0.messageId
  split <;> exact sha256_extract_size _

/-- Every Altair message ID is 20 bytes. -/
theorem Altair.messageId_size (topic data : ByteArray) : (Altair.messageId topic data).size = 20 := by
  unfold Altair.messageId
  split <;> exact sha256_extract_size _

/-! ## The two cases -/

/-- Phase 0 hashes data that decompresses as its payload, under the valid domain. -/
theorem Phase0.messageId_of_ok {data payload : ByteArray} (h : decompress data = .ok payload) :
    Phase0.messageId data =
      (sha256 (Phase0.hashInput MESSAGE_DOMAIN_VALID_SNAPPY payload)).extract 0 20 := by
  simp only [Phase0.messageId, h]

/-- Phase 0 hashes data that does not decompress as it is, under the invalid domain. -/
theorem Phase0.messageId_of_error {data : ByteArray} {e : SnappyError} (h : decompress data = .error e) :
    Phase0.messageId data =
      (sha256 (Phase0.hashInput MESSAGE_DOMAIN_INVALID_SNAPPY data)).extract 0 20 := by
  simp only [Phase0.messageId, h]

/-- Altair hashes data that decompresses as its payload, under the valid domain. -/
theorem Altair.messageId_of_ok (topic : ByteArray) {data payload : ByteArray}
    (h : decompress data = .ok payload) :
    Altair.messageId topic data =
      (sha256 (Altair.hashInput MESSAGE_DOMAIN_VALID_SNAPPY topic payload)).extract 0 20 := by
  simp only [Altair.messageId, h]

/-- Altair hashes data that does not decompress as it is, under the invalid domain. -/
theorem Altair.messageId_of_error (topic : ByteArray) {data : ByteArray} {e : SnappyError}
    (h : decompress data = .error e) :
    Altair.messageId topic data =
      (sha256 (Altair.hashInput MESSAGE_DOMAIN_INVALID_SNAPPY topic data)).extract 0 20 := by
  simp only [Altair.messageId, h]

/-- Two byte strings that decompress to one payload get one Phase 0 ID.

Several byte strings can decompress to the same value, so they share an ID.
-/
theorem Phase0.messageId_eq_of_decompress {data₁ data₂ payload : ByteArray}
    (h₁ : decompress data₁ = .ok payload) (h₂ : decompress data₂ = .ok payload) :
    Phase0.messageId data₁ = Phase0.messageId data₂ := by
  rw [Phase0.messageId_of_ok h₁, Phase0.messageId_of_ok h₂]

/-- Two byte strings that decompress to one payload get one Altair ID on the same topic. -/
theorem Altair.messageId_eq_of_decompress (topic : ByteArray) {data₁ data₂ payload : ByteArray}
    (h₁ : decompress data₁ = .ok payload) (h₂ : decompress data₂ = .ok payload) :
    Altair.messageId topic data₁ = Altair.messageId topic data₂ := by
  rw [Altair.messageId_of_ok topic h₁, Altair.messageId_of_ok topic h₂]

/-! ## The hash input -/

/-- The bytes of a hash input, in order. -/
private theorem toList_domain_append (domain : Vector UInt8 4) (rest : ByteArray) :
    (⟨domain.toArray⟩ ++ rest : ByteArray).data.toList = domain.toList ++ rest.data.toList := by
  simp only [ByteArray.data_append, Array.toList_append]
  rfl

/-- The Phase 0 hash input determines the domain and the bytes after it. -/
theorem Phase0.hashInput_injective {domain₁ domain₂ : Vector UInt8 4} {bytes₁ bytes₂ : ByteArray}
    (h : Phase0.hashInput domain₁ bytes₁ = Phase0.hashInput domain₂ bytes₂) :
    domain₁ = domain₂ ∧ bytes₁ = bytes₂ := by
  have lists := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [Phase0.hashInput, toList_domain_append] at lists
  -- Both domains are four bytes long, so the two lists split after their fourth byte.
  obtain ⟨domains, rest⟩ := List.append_inj lists (by simp)
  exact ⟨Vector.toList_inj.mp domains, ByteArray.ext (Array.toList_inj.mp rest)⟩

/-- The Altair hash input determines the domain, the topic and the bytes after them.

The topics are shorter than 2^64 bytes. -/
theorem Altair.hashInput_injective {domain₁ domain₂ : Vector UInt8 4} {topic₁ topic₂ bytes₁ bytes₂ : ByteArray}
    (hsize₁ : topic₁.size < 2 ^ 64) (hsize₂ : topic₂.size < 2 ^ 64)
    (h : Altair.hashInput domain₁ topic₁ bytes₁ = Altair.hashInput domain₂ topic₂ bytes₂) :
    domain₁ = domain₂ ∧ topic₁ = topic₂ ∧ bytes₁ = bytes₂ := by
  have lists := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [Altair.hashInput, ByteArray.data_append, Array.toList_append, List.append_assoc] at lists
  -- The first four bytes are the domain.
  obtain ⟨domains, rest⟩ := List.append_inj lists (by simp)
  -- The next eight are the topic length, whatever the topic.
  obtain ⟨lengths, rest⟩ := List.append_inj rest (by simp [uintBytes_size])
  -- Eight bytes hold every length below 2^64 exactly.
  have sizes : topic₁.size = topic₂.size :=
    uintBytes_injective (width := 8) hsize₁ hsize₂ (Array.toList_inj.mp lengths)
  -- The topic length then splits the topic from the bytes.
  obtain ⟨topics, rest⟩ := List.append_inj rest (by simpa using sizes)
  exact ⟨Vector.toArray_inj.mp (Array.toList_inj.mp (by simpa using domains)),
    ByteArray.ext (Array.toList_inj.mp topics), ByteArray.ext (Array.toList_inj.mp rest)⟩

/-- A Phase 0 hash input under the valid domain differs from every one under the invalid domain.

Their first bytes are `0x01` and `0x00`.
-/
theorem Phase0.hashInput_valid_ne_invalid (bytes₁ bytes₂ : ByteArray) :
    Phase0.hashInput MESSAGE_DOMAIN_VALID_SNAPPY bytes₁ ≠
      Phase0.hashInput MESSAGE_DOMAIN_INVALID_SNAPPY bytes₂ := by
  intro h
  -- Equal inputs have equal first bytes, and the domains start with different ones.
  have first := congrArg (fun b : ByteArray => b.data.toList.head?) h
  simp [Phase0.hashInput, MESSAGE_DOMAIN_VALID_SNAPPY, MESSAGE_DOMAIN_INVALID_SNAPPY] at first

/-- An Altair hash input under the valid domain differs from every one under the invalid domain.

Their first bytes are `0x01` and `0x00`, whatever the topics.
-/
theorem Altair.hashInput_valid_ne_invalid (topic₁ topic₂ bytes₁ bytes₂ : ByteArray) :
    Altair.hashInput MESSAGE_DOMAIN_VALID_SNAPPY topic₁ bytes₁ ≠
      Altair.hashInput MESSAGE_DOMAIN_INVALID_SNAPPY topic₂ bytes₂ := by
  intro h
  -- Equal inputs have equal first bytes, and the domains start with different ones.
  have first := congrArg (fun b : ByteArray => b.data.toList.head?) h
  simp [Altair.hashInput, ByteArray.data_append, MESSAGE_DOMAIN_VALID_SNAPPY,
    MESSAGE_DOMAIN_INVALID_SNAPPY] at first

end EthLib.Networking.Proofs.Gossip.MessageId
