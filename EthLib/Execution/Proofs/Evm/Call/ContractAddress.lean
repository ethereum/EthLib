module

public import EthLib.Base.Proofs.U256
public import EthLib.Execution.Evm.Call.ContractAddress
public import EthLib.Serialization.Proofs.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.Item
public import EthLib.Serialization.Proofs.Rlp.Bound
public import EthLib.Serialization.Proofs.Rlp.Loops
public import EthLib.Serialization.Proofs.Rlp.RoundTrip
public import EthLib.Serialization.Proofs.Rlp.Scalar

/-!
# Proofs: `Evm.Call.ContractAddress`

Two pairs of a sender and a nonce with one CREATE preimage are the same pair.

Two triples of a sender, a salt and a code hash with one CREATE2 preimage are the same triple.

The CREATE2 preimage has 85 bytes, and a CREATE preimage of a nonce below `2^256` at most 55.

So no CREATE preimage is a CREATE2 preimage.

Every nonce below `2^256` has a CREATE preimage, so CREATE never lacks an address.

The addresses still collide whenever Keccak-256 collides on their last 20 bytes.
-/

@[expose] public section

namespace EthLib.Execution.Evm

open EthLib.Base (Address U256)
open EthLib.Serialization.Rlp

/-- A CREATE preimage determines the sender and the nonce. -/
theorem createPreimage_injective {sender sender' : Address} {nonce nonce' : Nat}
    {preimage : ByteArray} (h : createPreimage sender nonce = .ok preimage)
    (h' : createPreimage sender' nonce' = .ok preimage) : sender = sender' ∧ nonce = nonce' := by
  have := encode_injective _ _ _ h h'
  simp only [Item.list.injEq, List.cons.injEq, and_true] at this
  exact ⟨Codec.toItem_injective this.1, Codec.toItem_injective this.2⟩

/-- A byte string of fewer than 56 bytes encodes in at most one byte more. -/
theorem encode_bytes_size_le {data e : ByteArray} (small : data.size < 56)
    (h : encode (.bytes data) = .ok e) : e.size ≤ data.size + 1 := by
  rcases encodeBytes_ok data e h with ⟨-, rfl⟩ | ⟨-, pre, hPre, rfl⟩
  · omega
  · simp only [lengthPrefix, small, ite_true, Except.ok.injEq] at hPre
    subst hPre
    rw [ByteArray.size_append]
    change 1 + data.size ≤ data.size + 1
    omega

/-- A CREATE preimage of a nonce below `2^256` has at most 55 bytes. -/
theorem createPreimage_size_le {sender : Address} {nonce : Nat} {preimage : ByteArray}
    (small : nonce < 2 ^ 256) (h : createPreimage sender nonce = .ok preimage) :
    preimage.size ≤ 55 := by
  obtain ⟨payload, pre, hJoin, hPre, rfl⟩ := encode_list_ok _ _ h
  obtain ⟨e1, rest, h1, hRest, rfl⟩ := joinEncodings_cons_ok _ _ _ hJoin
  obtain ⟨e2, tail, h2, hTail, rfl⟩ := joinEncodings_cons_ok _ _ _ hRest
  simp only [joinEncodings, Except.ok.injEq] at hTail
  subst hTail
  have s1 : e1.size ≤ 21 := by
    have hs : (⟨sender.toArray⟩ : ByteArray).size = 20 := by simp [ByteArray.size]
    have := encode_bytes_size_le (data := ⟨sender.toArray⟩) (by omega) h1
    omega
  have s2 : e2.size ≤ 33 := by
    have pow : (256 : Nat) ^ 32 = 2 ^ 256 := by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
    have hb : (bigEndian nonce).size ≤ 32 := bigEndian_size_le nonce 32 (pow ▸ small)
    have := encode_bytes_size_le (data := bigEndian nonce) (by omega) h2
    omega
  have hsize : (e1 ++ (e2 ++ ByteArray.empty)).size < 56 := by
    simp only [ByteArray.size_append, ByteArray.size_empty]
    omega
  simp only [lengthPrefix, hsize, ite_true, Except.ok.injEq] at hPre
  subst hPre
  simp only [ByteArray.size_append, ByteArray.size_empty] at hsize ⊢
  change 1 + (e1.size + (e2.size + 0)) ≤ 55
  omega

/-- Every nonce below `2^256` has a CREATE preimage. -/
theorem createPreimage_ok (sender : Address) {nonce : Nat} (small : nonce < 2 ^ 256) :
    ∃ preimage, createPreimage sender nonce = .ok preimage := by
  have hs : (⟨sender.toArray⟩ : ByteArray).size = 20 := by simp [ByteArray.size]
  obtain ⟨e1, h1⟩ := (encode_bytes_succeeds_iff ⟨sender.toArray⟩).2 (by omega)
  have s1 := encode_bytes_size_le (by omega) h1
  have pow : (256 : Nat) ^ 32 = 2 ^ 256 := by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]
  have hb : (bigEndian nonce).size ≤ 32 := bigEndian_size_le nonce 32 (pow ▸ small)
  obtain ⟨e2, h2⟩ := encode_scalar_succeeds nonce small
  have s2 := encode_bytes_size_le (data := bigEndian nonce) (by omega) h2
  have hJoin : joinEncodings [Codec.toItem sender, Codec.toItem nonce] =
      .ok (e1 ++ (e2 ++ .empty)) := by
    rw [joinEncodings_cons, joinEncodings_cons]
    simp only [Codec.toItem, Item.scalar] at h2 ⊢
    simp [h1, h2, joinEncodings, bind, Except.bind, pure, Except.pure]
  exact (encode_list_succeeds_iff _ _ hJoin).2 (by
    simp only [ByteArray.size_append, ByteArray.size_empty]
    omega)

/-- Every nonce below `2^256` has a CREATE address. -/
theorem createAddress_ok (sender : Address) {nonce : Nat} (small : nonce < 2 ^ 256) :
    ∃ address, createAddress sender nonce = .ok address := by
  obtain ⟨preimage, h⟩ := createPreimage_ok sender small
  exact ⟨addressOfHash (Cryptography.Hash.Keccak.keccak256 preimage),
    by simp [createAddress, h, bind, Except.bind, pure, Except.pure]⟩

/-- The CREATE2 preimage has 85 bytes: one, then 20, then 32, then 32. -/
theorem size_create2Preimage (sender : Address) (salt : U256) (hash : Vector UInt8 32) :
    (create2Preimage sender salt hash).size = 85 := by
  simp [create2Preimage, ByteArray.size]

/-- A CREATE2 preimage determines the sender, the salt and the hash of the init code. -/
theorem create2Preimage_injective {sender sender' : Address} {salt salt' : U256}
    {hash hash' : Vector UInt8 32}
    (h : create2Preimage sender salt hash = create2Preimage sender' salt' hash') :
    sender = sender' ∧ salt = salt' ∧ hash = hash' := by
  have hl := congrArg (fun b : ByteArray => b.data.toList) h
  simp only [create2Preimage, ByteArray.data_append, Array.toList_append] at hl
  obtain ⟨h0, hl⟩ := List.append_inj hl (by simp)
  obtain ⟨h0, h1⟩ := List.append_inj h0 (by simp)
  obtain ⟨-, h2⟩ := List.append_inj h0 (by simp)
  refine ⟨Vector.toList_inj.mp h2, ?_, Vector.toList_inj.mp hl⟩
  have := Vector.toList_inj.mp h1
  rw [← U256.fromBeBytes_toBeBytes salt, ← U256.fromBeBytes_toBeBytes salt', this]

/-- No CREATE preimage of a nonce below `2^256` is a CREATE2 preimage. -/
theorem createPreimage_ne_create2Preimage {sender sender' : Address} {nonce : Nat}
    {salt : U256} {hash : Vector UInt8 32} {preimage : ByteArray} (small : nonce < 2 ^ 256)
    (h : createPreimage sender nonce = .ok preimage) :
    preimage ≠ create2Preimage sender' salt hash := by
  intro heq
  have := createPreimage_size_le small h
  rw [heq, size_create2Preimage] at this
  omega

end EthLib.Execution.Evm
