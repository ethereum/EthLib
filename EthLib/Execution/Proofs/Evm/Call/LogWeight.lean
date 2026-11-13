module

public import EthLib.Execution.Evm.Call.TransferLog
public import EthLib.Serialization.Proofs.Rlp.Bound

/-!
# Proofs: a weight of logs that bounds their RLP encoding

The weight of a log is an upper bound on the length of its RLP encoding.

A LOG instruction pays at least four times the weight of its log, which sets the factor four.

From Glamsterdam, a transfer log of EIP-7708 weighs 179, and no LOG instruction pays for it.

So a message may write that much weight beyond what its own gas pays.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address Fork U256)
open EthLib.Execution.Blocks (Log)
open EthLib.Serialization.Rlp (Codec)

/-- An upper bound on the length of the RLP encoding of a log.

The constant 48 is 21 bytes for the address, and at most 9 bytes for each of three prefixes.

Those prefixes are of the list of topics, of the data and of the log itself.

A prefix of a payload below `2^64` bytes has at most 9 bytes: one byte, then at most 8 of length.

Each topic takes 33 bytes: one prefix byte, then the 32 bytes of the topic.

Each byte of data takes one byte. -/
def logWeight (l : Log) : Nat :=
  48 + 33 * l.topics.length + l.data.size

/-- The total weight of a list of logs. -/
def logsWeight (ls : List Log) : Nat :=
  (ls.map logWeight).sum

/-- The gas that a message may count beyond its own, to pay for one transfer log at `fork`.

From Glamsterdam, it is four times the weight of a transfer log: 4 * 179 = 716.

Before, it is 0. -/
def transferAllowance (fork : Fork) : Nat :=
  if fork ≥ .glamsterdam then 716 else 0

/-- A list of no logs weighs 0. -/
theorem logsWeight_nil : logsWeight [] = 0 :=
  rfl

/-- The weight of a list with one more log at the end adds the weight of that log. -/
theorem logsWeight_concat (ls : List Log) (l : Log) :
    logsWeight (ls ++ [l]) = logsWeight ls + logWeight l := by
  simp [logsWeight, List.map_append, List.sum_append]

/-- The weight of two lists of logs joined is the sum of their weights. -/
theorem logsWeight_append (ls ls' : List Log) :
    logsWeight (ls ++ ls') = logsWeight ls + logsWeight ls' := by
  simp [logsWeight, List.map_append, List.sum_append]

/-- A transfer log has three topics and 32 bytes of data, so it weighs 179. -/
theorem logWeight_transferLog (sender recipient : Address) (amount : U256) :
    logWeight (transferLog sender recipient amount) = 179 := by
  simp [logWeight, transferLog, ByteArray.size]

/-- From Glamsterdam, the allowance is four times the weight of a transfer log. -/
theorem transferAllowance_of_glamsterdam_le {fork : Fork} (h : .glamsterdam ≤ fork)
    (sender recipient : Address) (amount : U256) :
    transferAllowance fork = 4 * logWeight (transferLog sender recipient amount) := by
  rw [logWeight_transferLog]
  simp [transferAllowance, h]

/-- Before Glamsterdam, the allowance is 0. -/
theorem transferAllowance_of_lt {fork : Fork} (h : fork < .glamsterdam) :
    transferAllowance fork = 0 := by
  have hn : ¬ (Fork.glamsterdam ≤ fork) := Nat.not_le.mpr h
  simp [transferAllowance, hn]

open EthLib.Serialization in
/-- A log whose weight is below `2^64` encodes, to at most its weight in bytes. -/
theorem encode_log_size_le (l : Log) (h : logWeight l < 2 ^ 64) :
    ∃ e, Codec.encode l = .ok e ∧ e.size ≤ logWeight l := by
  have bytesOk : ∀ d : ByteArray, d.size < 2 ^ 64 →
      ∃ e, Rlp.encode (.bytes d) = .ok e ∧ e.size ≤ d.size + 9 ∧
        (d.size < 56 → e.size ≤ d.size + 1) := fun d hd => by
    obtain ⟨e, he⟩ := (Rlp.encode_bytes_succeeds_iff d).mpr hd
    exact ⟨e, he, Rlp.encode_bytes_size_le d e he⟩
  unfold logWeight at h ⊢
  -- The address, of 20 bytes.
  have hsa : (ByteArray.mk l.address.toArray).size = 20 := by simp [ByteArray.size]
  obtain ⟨ea, hea, -, hea1⟩ := bytesOk ⟨l.address.toArray⟩ (by omega)
  have hea1 := hea1 (by omega)
  -- The data.
  obtain ⟨ed, hed, hed9, -⟩ := bytesOk l.data (by omega)
  -- Each topic, of 32 bytes.
  have topicOk : ∀ i ∈ l.topics.map (Codec.toItem (α := EthLib.Base.Hash32)),
      ∃ e, Rlp.encode i = .ok e ∧ e.size ≤ 33 := by
    intro i hi
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hi
    have hst : (ByteArray.mk t.toArray).size = 32 := by simp [ByteArray.size]
    obtain ⟨e, he, -, he1⟩ := bytesOk ⟨t.toArray⟩ (by omega)
    have := he1 (by omega)
    exact ⟨e, he, by omega⟩
  obtain ⟨pt, hpt⟩ := Rlp.joinEncodings_ok _ (fun i hi => by
    obtain ⟨e, he, -⟩ := topicOk i hi
    exact ⟨e, he⟩)
  have hptSize := Rlp.joinEncodings_size_le 33 _ pt
    (fun i hi e he => by
      obtain ⟨e', he', hs⟩ := topicOk i hi
      rw [he] at he'
      cases he'
      exact hs) hpt
  rw [List.length_map] at hptSize
  obtain ⟨et, het⟩ := (Rlp.encode_list_succeeds_iff _ pt hpt).mpr (by omega)
  have het9 := Rlp.encode_list_size_le _ pt et hpt het
  -- The payload of the log.
  have hJoin : Rlp.joinEncodings [Codec.toItem l.address, Codec.toItem l.topics,
      Codec.toItem l.data] = .ok (ea ++ (et ++ (ed ++ .empty))) := by
    have ht : Codec.toItem l.topics =
        Rlp.Item.list (l.topics.map (Codec.toItem (α := EthLib.Base.Hash32))) :=
      rfl
    have ha : Codec.toItem l.address = Rlp.Item.bytes ⟨l.address.toArray⟩ := rfl
    have hd : Codec.toItem l.data = Rlp.Item.bytes l.data := rfl
    rw [ht, ha, hd]
    simp only [Rlp.joinEncodings_cons, hea, hed, het, bind, Except.bind, pure, Except.pure]
    rfl
  have hsz : (ea ++ (et ++ (ed ++ .empty))).size ≤ 21 + (33 * l.topics.length + 9) +
      (l.data.size + 9) := by
    simp only [ByteArray.size_append]
    have : (ByteArray.empty).size = 0 := rfl
    omega
  obtain ⟨e, he⟩ := (Rlp.encode_list_succeeds_iff _ _ hJoin).mpr (by omega)
  refine ⟨e, he, ?_⟩
  have := Rlp.encode_list_size_le _ _ e hJoin he
  omega

end EthLib.Execution.Evm
