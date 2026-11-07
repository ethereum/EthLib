module

public import EthLib.Networking.Enr.V4
public import EthLib.Cryptography.Proofs.Secp256k1.Sign
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding
public import EthLib.Networking.Proofs.Enr.Record

/-!
# Proofs: the "v4" identity scheme

The "v4" identity scheme of EIP-778, from its section of that name.

A record verifies exactly when ECDSA accepts its 64-byte signature, read as `r` then `s`.

So any ECDSA signature of the hash of its content, under the key of its pair, makes it verify.

The deterministic signer, with the nonce of RFC 6979 and the low-s rule of EIP-2, is one case.

The node ID exists exactly when the public key can be read, and it is the hash of that key.

It depends only on the `id` and `secp256k1` pairs.

A record that the signer signs verifies, keeps its pairs, and reads back from its bytes.

A record that the builder makes reads back from its bytes, verifies, and has its key pairs.

These are correctness statements: no theorem here states that a signature cannot be forged.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-- The public key of a record is the point that its `secp256k1` value encodes.

It holds when the `id` is `v4` and the value compresses a curve point other than infinity. -/
theorem publicKeyV4_of_get {r : Enr} {q : Point} (hq : q.isOnCurve = true) (hinf : q ≠ .infinity)
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes q.encodeCompressed)) :
    r.publicKeyV4 = .ok q := by
  cases q with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have hsize := Point.size_encodeCompressed x y
    have hdec := Point.decode_encodeCompressed hq hinf
    simp only [Enr.publicKeyV4, hid, hkey, ↓reduceIte, hsize, hdec, Except.mapError]

/-- A record verifies exactly when ECDSA accepts its signature under its public key.

The signature has 64 bytes: `r` then `s`, big-endian.

ECDSA signs the Keccak-256 hash of the RLP encoding of the content. -/
theorem verifyV4_eq_true_iff {r : Enr} :
    verifyV4 r = true ↔ ∃ q content, r.publicKeyV4 = .ok q ∧
      Serialization.Rlp.encode r.content = .ok content ∧ r.signature.size = 64 ∧
      Ecdsa.verify q (Hash.Keccak.keccak256 content)
        (Base.bytesToNat (r.signature.data.toList.take 32))
        (Base.bytesToNat (r.signature.data.toList.drop 32)) = true := by
  unfold verifyV4
  constructor
  · intro h
    split at h
    · rename_i q content hq hc
      split at h
      · rename_i hsz
        exact ⟨q, content, hq, hc, hsz, h⟩
      · cases h
    · cases h
  · rintro ⟨q, content, hq, hc, hsz, hv⟩
    rw [hq, hc]
    simp only [hsz, ↓reduceIte]
    exact hv

/-- A record that verifies has a public key. -/
theorem publicKeyV4_ok_of_verifyV4 {r : Enr} (h : verifyV4 r = true) :
    ∃ q, r.publicKeyV4 = .ok q := by
  obtain ⟨q, _, hq, -⟩ := verifyV4_eq_true_iff.mp h
  exact ⟨q, hq⟩

/-- A record verifies when ECDSA accepts `(r, s)` under the key of its `secp256k1` pair.

The signature is `r` then `s`, each in 32 big-endian bytes, as the "v4" scheme of EIP-778 says.

ECDSA signs the Keccak-256 hash of the RLP encoding of the content.

Any nonce and either sign of `s` will do. -/
theorem verifyV4_of_verify {r : Enr} {q : Point} {rr ss : Fn} {content : ByteArray}
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes q.encodeCompressed))
    (hc : Serialization.Rlp.encode r.content = .ok content)
    (hsig : r.signature = ⟨(Base.natToBytes 32 rr.val ++ Base.natToBytes 32 ss.val).toArray⟩)
    (hv : Ecdsa.verify q (Hash.Keccak.keccak256 content) rr.val ss.val = true) :
    verifyV4 r = true := by
  -- ECDSA rejects the point at infinity and points off the curve, so the key decodes.
  have hinf : q ≠ .infinity := fun h => by
    have h0 : Ecdsa.verify .infinity (Hash.Keccak.keccak256 content) rr.val ss.val = false :=
      Ecdsa.verify_infinity _ _ _
    rw [h, h0] at hv
    cases hv
  have hcurve : q.isOnCurve = true := by
    cases hq : q.isOnCurve
    · have h0 : Ecdsa.verify q (Hash.Keccak.keccak256 content) rr.val ss.val = false :=
        Ecdsa.verify_of_not_isOnCurve hq _ _ _
      rw [h0] at hv
      cases hv
    · rfl
  have hlr := Base.natToBytes_length 32 rr.val
  have hls := Base.natToBytes_length 32 ss.val
  have hmod (x : Fn) : x.val % 256 ^ 32 = x.val :=
    Nat.mod_eq_of_lt (lt_trans x.isLt (by decide : Fn.modulus < 256 ^ 32))
  refine verifyV4_eq_true_iff.mpr ⟨q, content, publicKeyV4_of_get hcurve hinf hid hkey, hc,
    by rw [hsig]; simp [ByteArray.size, hlr, hls], ?_⟩
  have hlist :
      r.signature.data.toList = Base.natToBytes 32 rr.val ++ Base.natToBytes 32 ss.val := by
    rw [hsig]
  rw [hlist, List.take_left' hlr, List.drop_left' hlr, Base.bytesToNat_natToBytes,
    Base.bytesToNat_natToBytes, hmod, hmod]
  exact hv

/-- A record verifies when its signature is the deterministic one from its private key `sk`.

Its `secp256k1` pair holds the compressed form of `sk G`.

The nonce is that of RFC 6979, and `s` is low, as EIP-2 asks.

The signature is `r` then `s`, each in 32 big-endian bytes, without the recovery ID.

It signs the Keccak-256 hash of the RLP encoding of the content. -/
theorem verifyV4_of_sign {r : Enr} {sk rr ss : Fn} {odd : Bool} {content : ByteArray}
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes (Point.mul sk Point.generator).encodeCompressed))
    (hc : Serialization.Rlp.encode r.content = .ok content)
    (hsign : Ecdsa.sign sk (Hash.Keccak.keccak256 content) = .ok (rr, ss, odd))
    (hsig : r.signature = ⟨(Base.natToBytes 32 rr.val ++ Base.natToBytes 32 ss.val).toArray⟩) :
    verifyV4 r = true :=
  verifyV4_of_verify hid hkey hc hsig (Ecdsa.verify_sign_rfc6979 hsign)

/-! ## Node ID -/

/-- The public key of a record is the point that the decoder returns for its `secp256k1` value.

That value is 33 bytes. -/
theorem decode_of_publicKeyV4 {r : Enr} {q : Point} (h : r.publicKeyV4 = .ok q) :
    ∃ key, r.get KEY_SECP256K1 = some (.bytes key) ∧ key.size = 33 ∧ Point.decode key = .ok q := by
  unfold Enr.publicKeyV4 at h
  split at h
  · cases h
  · split at h
    · split at h
      · rename_i key hk
        split at h
        · rename_i hsz
          refine ⟨key, hk, hsz, ?_⟩
          cases hd : Point.decode key with
          | error e => simp [hd, Except.mapError] at h
          | ok p => simp [hd, Except.mapError] at h; rw [h]
        · cases h
      · cases h
    · cases h

/-- The public key of a record lies on the curve. -/
theorem publicKeyV4_isOnCurve {r : Enr} {q : Point} (h : r.publicKeyV4 = .ok q) :
    q.isOnCurve = true := by
  obtain ⟨key, -, -, hdec⟩ := decode_of_publicKeyV4 h
  exact ((Point.decode_eq_ok_iff key q).mp hdec).1

/-- The public key of a record is never the point at infinity.

The decoder never returns that point. -/
theorem publicKeyV4_ne_infinity {r : Enr} {q : Point} (h : r.publicKeyV4 = .ok q) :
    q ≠ .infinity := by
  obtain ⟨key, -, -, hdec⟩ := decode_of_publicKeyV4 h
  exact ((Point.decode_eq_ok_iff key q).mp hdec).2.1

/-- Let the public key of a record be the point `(x, y)`.

Its node ID is the Keccak-256 hash of the 64 bytes of `x` then `y`. -/
theorem nodeId_of_publicKeyV4 {r : Enr} {x y : Fp} (h : r.publicKeyV4 = .ok (.affine x y)) :
    nodeId r = .ok (Hash.Keccak.keccak256 (publicKeyBytes x y)) := by
  rw [nodeId, h]
  rfl

/-- When the public key of a record cannot be read, the node ID fails with the same error.

The read fails without an `id`, for another scheme, or for a missing or invalid key. -/
theorem nodeId_of_publicKeyV4_error {r : Enr} {e : EnrError} (h : r.publicKeyV4 = .error e) :
    nodeId r = .error e := by
  simp [nodeId, h, bind, Except.bind]

/-- The node ID of a record is `id` exactly when its public key is a point `(x, y)`.

Then `id` is the Keccak-256 hash of the 64 bytes of `x` then `y`. -/
theorem nodeId_eq_ok_iff {r : Enr} {id : Vector UInt8 32} :
    nodeId r = .ok id ↔ ∃ x y, r.publicKeyV4 = .ok (.affine x y) ∧
      id = Hash.Keccak.keccak256 (publicKeyBytes x y) := by
  constructor
  · intro h
    cases hq : r.publicKeyV4 with
    | error e => rw [nodeId_of_publicKeyV4_error hq] at h; cases h
    | ok q =>
      cases q with
      | infinity => exact absurd rfl (publicKeyV4_ne_infinity hq)
      | affine x y =>
        rw [nodeId_of_publicKeyV4 hq] at h
        exact ⟨x, y, rfl, (Except.ok.inj h).symm⟩
  · rintro ⟨x, y, hq, rfl⟩
    exact nodeId_of_publicKeyV4 hq

/-- Let the `secp256k1` value of a "v4" record compress the curve point `(x, y)`.

Its node ID is the Keccak-256 hash of the 64 bytes of `x` then `y`. -/
theorem nodeId_of_get {r : Enr} {x y : Fp} (hq : (Point.affine x y).isOnCurve = true)
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes (Point.affine x y).encodeCompressed)) :
    nodeId r = .ok (Hash.Keccak.keccak256 (publicKeyBytes x y)) :=
  nodeId_of_publicKeyV4 (publicKeyV4_of_get hq nofun hid hkey)

/-- The public key of a record depends only on its `id` and `secp256k1` values. -/
theorem publicKeyV4_congr {r r' : Enr} (hid : r.get KEY_ID = r'.get KEY_ID)
    (hkey : r.get KEY_SECP256K1 = r'.get KEY_SECP256K1) : r.publicKeyV4 = r'.publicKeyV4 := by
  unfold Enr.publicKeyV4
  rw [hid, hkey]

/-- The node ID of a record depends only on its `id` and `secp256k1` values.

So the sequence number, the signature and the pairs under other keys do not change it. -/
theorem nodeId_congr {r r' : Enr} (hid : r.get KEY_ID = r'.get KEY_ID)
    (hkey : r.get KEY_SECP256K1 = r'.get KEY_SECP256K1) : nodeId r = nodeId r' := by
  unfold nodeId
  rw [publicKeyV4_congr hid hkey]

/-- A record that verifies has a node ID. -/
theorem nodeId_ok_of_verifyV4 {r : Enr} (h : verifyV4 r = true) : ∃ id, nodeId r = .ok id := by
  obtain ⟨q, hq⟩ := publicKeyV4_ok_of_verifyV4 h
  cases q with
  | infinity => exact absurd rfl (publicKeyV4_ne_infinity hq)
  | affine x y => exact ⟨_, nodeId_of_publicKeyV4 hq⟩

/-! ## Signing -/

/-- A signed record is the record with the deterministic signature of its content. -/
theorem signV4_eq_ok {sk : Fn} {r r' : Enr} (h : signV4 sk r = .ok r') :
    ∃ content rr ss odd, Serialization.Rlp.encode r.content = .ok content ∧
      Ecdsa.sign sk (Hash.Keccak.keccak256 content) = .ok (rr, ss, odd) ∧
      r' = { r with signature :=
        ⟨(Base.natToBytes 32 rr.val ++ Base.natToBytes 32 ss.val).toArray⟩ } := by
  unfold signV4 at h
  cases hc : Serialization.Rlp.encode r.content with
  | error e => simp [hc, Except.mapError, bind, Except.bind] at h
  | ok content =>
    cases hs : Ecdsa.sign sk (Hash.Keccak.keccak256 content) with
    | error e => simp [hc, hs, Except.mapError, bind, Except.bind] at h
    | ok sig =>
      obtain ⟨rr, ss, odd⟩ := sig
      simp only [hc, hs, Except.mapError, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at h
      exact ⟨content, rr, ss, odd, rfl, hs, h.symm⟩

/-- Signing keeps the sequence number and the pairs. -/
theorem seq_pairs_signV4 {sk : Fn} {r r' : Enr} (h : signV4 sk r = .ok r') :
    r'.seq = r.seq ∧ r'.pairs = r.pairs := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := signV4_eq_ok h
  exact ⟨rfl, rfl⟩

/-- A record signed with `sk` verifies, when its `id` is `v4` and its key pair holds `sk G`. -/
theorem verifyV4_signV4 {sk : Fn} {r r' : Enr} (h : signV4 sk r = .ok r')
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes (Point.mul sk Point.generator).encodeCompressed)) :
    verifyV4 r' = true := by
  obtain ⟨content, rr, ss, odd, hc, hs, rfl⟩ := signV4_eq_ok h
  exact verifyV4_of_sign hid hkey hc hs rfl

/-- A signed record reads back from its bytes, and it verifies.

Its encoding must fit in 300 bytes, and its keys must strictly increase.

Its `id` is `v4`, and its `secp256k1` pair holds `sk G`. -/
theorem decode_encode_signV4 {sk : Fn} {r r' : Enr} {bytes : ByteArray}
    (h : signV4 sk r = .ok r') (he : r'.encode = .ok bytes)
    (hs : bytes.size ≤ MAX_RECORD_SIZE) (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1))
    (hid : r.get KEY_ID = some (.bytes SCHEME_V4))
    (hkey : r.get KEY_SECP256K1 = some (.bytes (Point.mul sk Point.generator).encodeCompressed)) :
    decode bytes = .ok r' ∧ verifyV4 r' = true := by
  have hpairs := (seq_pairs_signV4 h).2
  -- The pair `id` is among the pairs, since the record has a value for it.
  have hmem : ∃ value, (KEY_ID, value) ∈ r'.pairs := by
    rw [hpairs]
    unfold Enr.get at hid
    obtain ⟨⟨key, value⟩, hfind, -⟩ := Option.map_eq_some_iff.mp hid
    have hkey' := List.find?_some hfind
    simp only [decide_eq_true_eq] at hkey'
    exact ⟨value, hkey' ▸ List.mem_of_find?_eq_some hfind⟩
  exact ⟨decode_encode r' bytes he hs (hpairs ▸ hk) hmem, verifyV4_signV4 h hid hkey⟩

/-- Signing keeps the node ID, which depends only on the pairs. -/
theorem nodeId_signV4 {sk : Fn} {r r' : Enr} (h : signV4 sk r = .ok r') :
    nodeId r' = nodeId r := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := signV4_eq_ok h
  rfl

/-! ## Building a record -/

/-- The pairs after an insertion are the inserted pair and the pairs before. -/
theorem mem_insertPair {p x : ByteArray × Item} :
    (pairs : List (ByteArray × Item)) → (x ∈ insertPair p pairs ↔ x = p ∨ x ∈ pairs)
  | [] => by simp [insertPair]
  | q :: rest => by
    unfold insertPair
    split
    · simp
    · simp only [List.mem_cons, mem_insertPair rest]
      constructor
      · rintro (h | h | h) <;> simp [h]
      · rintro (h | h | h) <;> simp [h]

/-- In pairs whose keys strictly increase, the value of a key is that of its one pair. -/
theorem get_of_mem {r : Enr} {key : ByteArray} {value : Item}
    (hk : r.pairs.Pairwise (fun p q => keyLt p.1 q.1)) (hmem : (key, value) ∈ r.pairs) :
    r.get key = some value := by
  unfold Enr.get
  obtain ⟨_, _, pairs⟩ := r
  simp only at hk hmem ⊢
  induction pairs with
  | nil => cases hmem
  | cons q rest ih =>
    rw [List.pairwise_cons] at hk
    rcases List.mem_cons.mp hmem with rfl | hrest
    · simp
    · -- The key of `q` comes before the key, so it is another key.
      have hlt := hk.1 _ hrest
      have hne : q.1 ≠ key := fun h => by
        rw [h] at hlt
        exact List.lt_irrefl _ hlt
      simp [hne, ih hk.2 hrest]

/-- A record that the builder makes reads back from its bytes and verifies.

It has the sequence number, the pair `id` with `v4`, and the pair `secp256k1` of `sk G`. -/
theorem makeRecordV4_eq_ok {sk : Fn} {seq : UInt64} {pairs : List (ByteArray × Item)} {r : Enr}
    (h : makeRecordV4 sk seq pairs = .ok r) :
    ∃ bytes, r.encode = .ok bytes ∧ decode bytes = .ok r ∧ verifyV4 r = true ∧ r.seq = seq ∧
      r.get KEY_ID = some (.bytes SCHEME_V4) ∧
      r.get KEY_SECP256K1 = some (.bytes (Point.mul sk Point.generator).encodeCompressed) := by
  unfold makeRecordV4 at h
  dsimp only at h
  generalize hall : insertPair (KEY_ID, .bytes SCHEME_V4)
    (insertPair (KEY_SECP256K1, .bytes (Point.mul sk Point.generator).encodeCompressed) pairs)
    = all at h
  cases hc : checkKeys all with
  | error e => simp [hc, bind, Except.bind] at h
  | ok u =>
    cases hs : signV4 sk ⟨.empty, seq, all⟩ with
    | error e => simp [hc, hs, bind, Except.bind] at h
    | ok signed =>
      cases he : signed.encode with
      | error e => simp [hc, hs, he, Except.mapError, bind, Except.bind] at h
      | ok bytes =>
        by_cases hsize : MAX_RECORD_SIZE < bytes.size
        · simp [hc, hs, he, hsize, Except.mapError, bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at h
        simp only [hc, hs, he, hsize, Except.mapError, bind, Except.bind, ↓reduceIte, pure,
          Except.pure, Except.ok.injEq] at h
        subst h
        -- The keys strictly increase, and both key pairs are among the pairs.
        have hk := pairwise_of_checkKeys all hc
        have hid : (KEY_ID, Item.bytes SCHEME_V4) ∈ all := by
          rw [← hall, mem_insertPair]
          exact Or.inl rfl
        have hkey : (KEY_SECP256K1,
            Item.bytes (Point.mul sk Point.generator).encodeCompressed) ∈ all := by
          rw [← hall, mem_insertPair, mem_insertPair]
          exact Or.inr (Or.inl rfl)
        have gid : (⟨.empty, seq, all⟩ : Enr).get KEY_ID = some (.bytes SCHEME_V4) :=
          get_of_mem hk hid
        have gkey : (⟨.empty, seq, all⟩ : Enr).get KEY_SECP256K1 =
            some (.bytes (Point.mul sk Point.generator).encodeCompressed) :=
          get_of_mem hk hkey
        obtain ⟨hseq, hpairs⟩ := seq_pairs_signV4 hs
        obtain ⟨hdec, hver⟩ := decode_encode_signV4 hs he (Nat.le_of_not_lt hsize) hk gid gkey
        refine ⟨bytes, he, hdec, hver, hseq, ?_, ?_⟩
        · unfold Enr.get at gid ⊢
          rw [hpairs]
          exact gid
        · unfold Enr.get at gkey ⊢
          rw [hpairs]
          exact gkey

end EthLib.Networking.Enr
