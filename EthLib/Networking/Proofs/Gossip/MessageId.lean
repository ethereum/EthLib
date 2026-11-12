module

public import EthLib.Base.Bytes
public import EthLib.Networking.Gossip.MessageId
public import EthLib.Serialization.Proofs.Ssz.Codec.LengthBinding
public import EthLib.Serialization.Proofs.Ssz.Codec.Table

/-!
# `Networking.Proofs.Gossip.MessageId`

Properties of the gossip message ID.

- Data that decompresses is hashed as its payload under the domain `01 00 00 00`.
- Other data is hashed as it is under the domain `00 00 00 00`.
- As a byte string, the ID is the first 20 bytes of the SHA-256 digest of the hash input.
- Two byte strings that decompress to one payload get one ID on one topic.
- Before Altair the topic does not change the ID.
- Each hash input determines its domain and its bytes, and under Altair its topic.
  The topic must be shorter than 2^64 bytes.
  So two messages that differ in one share an ID only if SHA-256, cut to 20 bytes, collides.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Gossip.MessageId

open EthLib.Networking.Gossip
open EthLib.Networking.Snappy (decompress SnappyError)
open EthLib.Cryptography.Hash (sha256)
open EthLib.Cryptography.Hash.Sha256 (hash32)
open EthLib.Serialization.Ssz (uintBytes_size uintBytes_injective)

/-! ## The two cases -/

/-- Data that decompresses is hashed as its payload, under the valid domain. -/
theorem messageId_of_ok (fork : Base.Fork) (topic : ByteArray) {data payload : ByteArray}
    (h : decompress data = .ok payload) :
    messageId fork topic data =
      (hash32 (hashInput fork MESSAGE_DOMAIN_VALID_SNAPPY topic payload)).take 20 := by
  simp only [messageId, h]

/-- Data that does not decompress is hashed as it is, under the invalid domain. -/
theorem messageId_of_error (fork : Base.Fork) (topic : ByteArray) {data : ByteArray}
    {e : SnappyError} (h : decompress data = .error e) :
    messageId fork topic data =
      (hash32 (hashInput fork MESSAGE_DOMAIN_INVALID_SNAPPY topic data)).take 20 := by
  simp only [messageId, h]

/-! ## The ID as a byte string -/

/-- The first 20 bytes of a SHA-256 digest are the same in its fixed-size and byte-string forms. -/
theorem packBytes_hash32_take (input : ByteArray) :
    Base.packBytes ((hash32 input).take 20) = (sha256 input).extract 0 20 := by
  apply ByteArray.ext
  simp [Base.packBytes, hash32, sha256]

/-- As a byte string, the ID of data that decompresses is the first 20 bytes of a SHA-256 digest.

The hash input holds the payload, under the valid domain. -/
theorem packBytes_messageId_of_ok (fork : Base.Fork) (topic : ByteArray)
    {data payload : ByteArray} (h : decompress data = .ok payload) :
    Base.packBytes (messageId fork topic data) =
      (sha256 (hashInput fork MESSAGE_DOMAIN_VALID_SNAPPY topic payload)).extract 0 20 := by
  rw [messageId_of_ok fork topic h, packBytes_hash32_take]

/-- As a byte string, the ID of other data is the first 20 bytes of a SHA-256 digest.

The hash input holds the data as it is, under the invalid domain. -/
theorem packBytes_messageId_of_error (fork : Base.Fork) (topic : ByteArray) {data : ByteArray}
    {e : SnappyError} (h : decompress data = .error e) :
    Base.packBytes (messageId fork topic data) =
      (sha256 (hashInput fork MESSAGE_DOMAIN_INVALID_SNAPPY topic data)).extract 0 20 := by
  rw [messageId_of_error fork topic h, packBytes_hash32_take]

/--
Two byte strings that decompress to one payload get one ID on one topic.

Several byte strings can decompress to the same value, so they share an ID.
-/
theorem messageId_eq_of_decompress (fork : Base.Fork) (topic : ByteArray)
    {data₁ data₂ payload : ByteArray}
    (h₁ : decompress data₁ = .ok payload) (h₂ : decompress data₂ = .ok payload) :
    messageId fork topic data₁ = messageId fork topic data₂ := by
  rw [messageId_of_ok fork topic h₁, messageId_of_ok fork topic h₂]

/-! ## The fork -/

/-- Before Altair the hash input is the Phase 0 one, which holds no topic. -/
theorem hashInput_of_lt_altair {fork : Base.Fork} (before : fork < .altair)
    (domain : Vector UInt8 4) (topic bytes : ByteArray) :
    hashInput fork domain topic bytes = Phase0.hashInput domain bytes := by
  simp [hashInput, before]

/-- From Altair on the hash input is the Altair one, which holds the topic. -/
theorem hashInput_of_altair_le {fork : Base.Fork} (since : .altair ≤ fork)
    (domain : Vector UInt8 4) (topic bytes : ByteArray) :
    hashInput fork domain topic bytes = Altair.hashInput domain topic bytes := by
  simp [hashInput, show ¬ fork < .altair from Nat.not_lt.mpr since]

/-- Before Altair the topic does not change the ID. -/
theorem messageId_topic_of_lt_altair {fork : Base.Fork} (before : fork < .altair)
    (topic₁ topic₂ data : ByteArray) :
    messageId fork topic₁ data = messageId fork topic₂ data := by
  simp only [messageId, hashInput_of_lt_altair before]

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

/-- At every fork, a hash input under the valid domain differs from one under the invalid domain. -/
theorem hashInput_valid_ne_invalid (fork : Base.Fork) (topic₁ topic₂ bytes₁ bytes₂ : ByteArray) :
    hashInput fork MESSAGE_DOMAIN_VALID_SNAPPY topic₁ bytes₁ ≠
      hashInput fork MESSAGE_DOMAIN_INVALID_SNAPPY topic₂ bytes₂ := by
  unfold hashInput
  split
  · exact Phase0.hashInput_valid_ne_invalid bytes₁ bytes₂
  · exact Altair.hashInput_valid_ne_invalid topic₁ topic₂ bytes₁ bytes₂

end EthLib.Networking.Proofs.Gossip.MessageId
