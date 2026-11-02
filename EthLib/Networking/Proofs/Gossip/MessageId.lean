module

public import EthLib.Networking.Gossip.MessageId
public import EthLib.Cryptography.Proofs.Hash.Sha256
public import EthLib.Serialization.Proofs.Ssz.Codec.LengthBinding
public import EthLib.Serialization.Proofs.Ssz.Codec.Table

/-!
# `Networking.Proofs.Gossip.MessageId`

Properties of the gossip message ID, against "Topics and messages" of [`phase0/p2p-interface.md`](https://github.com/ethereum/consensus-specs/blob/55a48db47eff748266187888f01227940e3e7e64/specs/phase0/p2p-interface.md#topics-and-messages) and of [`altair/p2p-interface.md`](https://github.com/ethereum/consensus-specs/blob/55a48db47eff748266187888f01227940e3e7e64/specs/altair/p2p-interface.md#topics-and-messages).

- Every ID is 20 bytes.
- Data that decompresses is hashed as its payload under `MESSAGE_DOMAIN_VALID_SNAPPY`, and other data as it is under `MESSAGE_DOMAIN_INVALID_SNAPPY`.
- Two byte strings that decompress to one payload get one ID, on the same topic for Altair.
- Each hash input determines its domain and its bytes, and under Altair its topic, for topics shorter than 2^64 bytes.
  So two messages that differ in one of these share an ID only if SHA-256, cut to 20 bytes, collides.
- Known answers: one per rule and per case, one for an empty message, and one for a six-byte preamble.

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

This is the first case of the note under the Phase 0 rule: several byte strings can decompress to the same value.
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

/-- The Altair hash input determines the domain, the topic and the bytes after them, for topics shorter than 2^64 bytes. -/
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

/-! ## Known answers

The payload is 32 zero bytes.

`python-snappy` 0.7.3 (on `cramjam` 2.14.0) compresses it to `20 00 00 7a 01 00`.

That is the length 32, a literal of one byte (tag `00`, then `00`), and a copy of 31 bytes from 1 byte back (tag `7a`, then offset `01 00`).

The raw payload is not a Snappy block: its first byte declares an empty block, and 31 more bytes follow.

Each expected ID was computed with Python's `hashlib`, never with this code.

`python-snappy` decided which data decompresses, except in the last answer.

There `python-snappy` and `Snappy.decompress` disagree, and the ID follows `Snappy.decompress`.
-/

namespace TestVector

/-- The beacon block topic `/eth2/afcaaba0/beacon_block/ssz_snappy`, 38 bytes of ASCII.

The ID reads the topic only as bytes, so any fork digest would do.
-/
def topic : ByteArray := ⟨#[
  0x2f, 0x65, 0x74, 0x68, 0x32, 0x2f, 0x61, 0x66, 0x63, 0x61, 0x61, 0x62, 0x61, 0x30, 0x2f, 0x62,
  0x65, 0x61, 0x63, 0x6f, 0x6e, 0x5f, 0x62, 0x6c, 0x6f, 0x63, 0x6b, 0x2f, 0x73, 0x73, 0x7a, 0x5f,
  0x73, 0x6e, 0x61, 0x70, 0x70, 0x79]⟩

/-- 32 zero bytes, compressed by `python-snappy`. -/
def compressed : ByteArray := ⟨#[0x20, 0x00, 0x00, 0x7a, 0x01, 0x00]⟩

/-- 32 zero bytes, sent without compression. -/
def raw : ByteArray := ⟨Array.replicate 32 0⟩

/-- The length 0 written in six preamble bytes, one more than a 32-bit length ever needs, and nothing after it. -/
def longPreamble : ByteArray := ⟨#[0x80, 0x80, 0x80, 0x80, 0x80, 0x00]⟩

end TestVector

open TestVector

/-- Phase 0, data that decompresses: SHA256(01 00 00 00 | 32 zero bytes)[:20]. -/
theorem phase0_valid :
    Phase0.messageId compressed = ⟨#[
      0x11, 0xbc, 0x11, 0x5c, 0x02, 0x26, 0x32, 0x9c, 0x9a, 0x35,
      0xa7, 0xfe, 0xe1, 0xd2, 0x9c, 0x1f, 0x52, 0x48, 0xe0, 0xf7]⟩ := by
  decide +kernel

/-- Phase 0, data that does not decompress: SHA256(00 00 00 00 | 32 zero bytes)[:20]. -/
theorem phase0_invalid :
    Phase0.messageId raw = ⟨#[
      0x6d, 0xb6, 0x5f, 0xd5, 0x9f, 0xd3, 0x56, 0xf6, 0x72, 0x91,
      0x40, 0x57, 0x1b, 0x5b, 0xcd, 0x6b, 0xb3, 0xb8, 0x34, 0x92]⟩ := by
  decide +kernel

/-- Altair, data that decompresses: SHA256(01 00 00 00 | 26 00 00 00 00 00 00 00 | topic | 32 zero bytes)[:20]. -/
theorem altair_valid :
    Altair.messageId topic compressed = ⟨#[
      0xdf, 0x1b, 0xb5, 0x4c, 0x62, 0xc1, 0x77, 0x6b, 0x50, 0x28,
      0xf4, 0x4c, 0xb8, 0x79, 0xb2, 0xb4, 0xf3, 0x92, 0x6c, 0x09]⟩ := by
  decide +kernel

/-- Altair, data that does not decompress: SHA256(00 00 00 00 | 26 00 00 00 00 00 00 00 | topic | 32 zero bytes)[:20]. -/
theorem altair_invalid :
    Altair.messageId topic raw = ⟨#[
      0x72, 0x3e, 0x3f, 0x27, 0x85, 0xc7, 0x22, 0x7d, 0xa1, 0xfe,
      0x5c, 0xb0, 0x6a, 0x5e, 0xd4, 0x6a, 0x3a, 0x64, 0x7a, 0xd4]⟩ := by
  decide +kernel

/-- Altair, a message with neither topic nor data: SHA256(00 00 00 00 | eight zero bytes)[:20].

Empty data is not a Snappy block, since a block starts with its length.
-/
theorem altair_empty :
    Altair.messageId ByteArray.empty ByteArray.empty = ⟨#[
      0x15, 0xec, 0x7b, 0xf0, 0xb5, 0x07, 0x32, 0xb4, 0x9f, 0x82,
      0x28, 0xe0, 0x7d, 0x24, 0x36, 0x53, 0x38, 0xf9, 0xe3, 0xab]⟩ := by
  decide +kernel

/-- Phase 0, a preamble of six bytes: SHA256(00 00 00 00 | 80 80 80 80 80 00)[:20].

`Snappy.decompress` reads at most five preamble bytes, so the data is hashed as it is.

`python-snappy` decompresses it to the empty payload, which would give the ID SHA256(01 00 00 00)[:20] = `67abdd721024f0ff4e0b3f4c2fc13bc5bad42d0b` instead.
-/
theorem phase0_long_preamble :
    Phase0.messageId longPreamble = ⟨#[
      0xf5, 0x0b, 0xf1, 0x26, 0xb6, 0x8e, 0x05, 0xa9, 0xaa, 0x7f,
      0x6c, 0x4f, 0x03, 0x9a, 0xb9, 0xad, 0x25, 0x3f, 0xd4, 0x05]⟩ := by
  decide +kernel

end EthLib.Networking.Proofs.Gossip.MessageId
