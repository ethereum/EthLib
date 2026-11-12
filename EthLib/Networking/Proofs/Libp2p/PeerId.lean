module

public import EthLib.Base.Proofs.BigEndian
public import EthLib.Networking.Libp2p.PeerId
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding

/-!
# Proofs: libp2p secp256k1 public keys and peer IDs

- A point of the curve, other than infinity, encodes to a key protobuf that decodes back to it.
- A peer ID decodes back to its key, and the decoder accepts only peer IDs of keys.
- Two different points of the curve have two different peer IDs.
- A decoded key's peer ID is the two bytes `00 25`, then the key protobuf.
- A number below `2 ^ 256` is a DER INTEGER on the fewest bytes whose top bit stays clear.
- The signature decoder accepts exactly the encodings of r and s in range, and returns them.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.PeerId

open EthLib.Base
open EthLib.Cryptography.Secp256k1
open EthLib.Networking.Libp2p

/-- A point of the curve, other than infinity, encodes to a key protobuf that decodes back to it. -/
theorem decodePublicKey_encodePublicKey {point : Point} (hcurve : point.isOnCurve = true)
    (hinf : point ≠ .infinity) : decodePublicKey (encodePublicKey point) = .ok point := by
  cases point with
  | infinity => exact absurd rfl hinf
  | affine x y =>
    have hsize : (encodePublicKey (.affine x y)).size = 37 := by
      simp [encodePublicKey, ByteArray.size_append, Point.size_encodeCompressed]
      rfl
    have hext :
        (encodePublicKey (.affine x y)).extract 4 37 = (Point.affine x y).encodeCompressed :=
      ByteArray.extract_append_eq_right (by rfl) (by rw [← hsize]; rfl)
    simp [decodePublicKey, hsize, hext, Point.decode_encodeCompressed hcurve hinf,
      Except.mapError, bind, Except.bind, pure, Except.pure]

/-- A decoded key protobuf is the encoding of the point it decodes to. -/
theorem encodePublicKey_of_decodePublicKey {key : ByteArray} {point : Point}
    (h : decodePublicKey key = .ok point) : encodePublicKey point = key := by
  unfold decodePublicKey at h
  by_cases hs : (key.size != 37) = true
  · simp [hs, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · cases hd : Point.decode (key.extract 4 37) with
    | error e => simp [hs, hd, Except.mapError, bind, Except.bind] at h
    | ok q =>
      by_cases he : encodePublicKey q = key
      · simp [hs, hd, he, Except.mapError, bind, Except.bind, pure, Except.pure] at h
        subst h; exact he
      · simp [hs, hd, he, Except.mapError, bind, Except.bind] at h

/-- The peer ID of a point of the curve, other than infinity, decodes back to that point. -/
theorem decodePeerId_peerId {point : Point} (hcurve : point.isOnCurve = true)
    (hinf : point ≠ .infinity) : decodePeerId (peerId point) = .ok point := by
  simp [peerId, decodePeerId, ByteArray.data_append, Array.toList_append,
    decodePublicKey_encodePublicKey hcurve hinf]

/-- A peer ID that decodes is the peer ID of the point it decodes to. -/
theorem peerId_of_decodePeerId {id : ByteArray} {point : Point}
    (h : decodePeerId id = .ok point) : peerId point = id := by
  unfold decodePeerId at h
  split at h
  · rename_i key hl
    have hk := encodePublicKey_of_decodePublicKey h
    rw [peerId, hk]
    apply ByteArray.ext
    simp [ByteArray.data_append]
    apply Array.ext'
    simp [hl]
  · simp at h

/-- Two points of the curve with one peer ID are one point.

Infinity has a shorter peer ID than any other point, and the others decode back. -/
theorem peerId_injective {p q : Point} (hp : p.isOnCurve = true) (hq : q.isOnCurve = true)
    (h : peerId p = peerId q) : p = q := by
  rcases p with _ | ⟨x, y⟩ <;> rcases q with _ | ⟨x', y'⟩
  · rfl
  · have := congrArg ByteArray.size h
    simp [peerId, encodePublicKey, ByteArray.size_append, Point.size_encodeCompressed] at this
    exact absurd this (by decide)
  · have := congrArg ByteArray.size h
    simp [peerId, encodePublicKey, ByteArray.size_append, Point.size_encodeCompressed] at this
    exact absurd this (by decide)
  · have hd := decodePeerId_peerId hp (by simp)
    rw [h, decodePeerId_peerId hq (by simp)] at hd
    exact (Except.ok.inj hd).symm

/-- The peer ID of a decoded key is the two bytes `00 25`, then the key protobuf. -/
theorem peerId_of_decodePublicKey {key : ByteArray} {point : Point}
    (h : decodePublicKey key = .ok point) : peerId point = ⟨#[0x00, 0x25]⟩ ++ key := by
  rw [peerId, encodePublicKey_of_decodePublicKey h]

/-! ## DER signatures

BIP 62 rule 1 asks for strict DER, where an INTEGER takes the fewest bytes of its two's complement.

So a positive number has one leading zero byte exactly when its first byte is `0x80` or more.

The decoder accepts a signature only when the encoder writes the same bytes back.
-/

/-- On `i + 1` bytes, the first byte is `n / 256 ^ i`, then `n` follows on `i` bytes. -/
private theorem natToBytes_succ_eq_cons (i n : Nat) :
    natToBytes (i + 1) n = UInt8.ofNat (n / 256 ^ i) :: natToBytes i n := by
  rw [Nat.add_comm, natToBytes_add]
  rfl

/-- A byte written from a number below 256 reads back as that number. -/
private theorem toNat_ofNat_of_lt {x : Nat} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  simp; omega

/-- Dropping the leading zeros of zeros followed by a nonzero byte leaves that byte first. -/
private theorem dropWhile_replicate_append (k : Nat) {b : UInt8} (rest : List UInt8)
    (hb : b ≠ 0) : (List.replicate k 0 ++ b :: rest).dropWhile (· == 0) = b :: rest := by
  induction k with
  | zero => simp [hb]
  | succ k ih => simpa [List.replicate_succ, List.dropWhile_cons] using ih

/-- A number with exactly `i + 1` significant bytes keeps those bytes once its leading zeros go. -/
private theorem dropWhile_natToBytes {n i : Nat} (hi : i < 32) (low : 256 ^ i ≤ n)
    (high : n < 256 ^ (i + 1)) :
    (natToBytes 32 n).dropWhile (· == 0) = natToBytes (i + 1) n := by
  have hsplit := natToBytes_add (31 - i) (i + 1) n
  rw [show 31 - i + (i + 1) = 32 by omega, Nat.div_eq_of_lt high, natToBytes_zero_right]
    at hsplit
  have hpos : 0 < 256 ^ i := Nat.pow_pos (by decide)
  have hlow : 1 ≤ n / 256 ^ i := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
  have hhigh : n / 256 ^ i < 256 :=
    (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.pow_succ] at high; omega)
  rw [hsplit, natToBytes_succ_eq_cons]
  apply dropWhile_replicate_append
  intro h
  have := congrArg UInt8.toNat h
  rw [toNat_ofNat_of_lt hhigh] at this
  simp at this
  omega

/-- The DER INTEGER of a number below `2 ^ 256`, BIP 62.

Its content is the number on `k` big-endian bytes, the fewest bytes whose top bit stays clear.

So the number is below `2 ^ (8 * k - 1)`, and, for `k` above 1, at least `2 ^ (8 * (k - 1) - 1)`.

The first content byte is then below `0x80`, and it is `0x00` only before a byte of `0x80` or more.

Zero is one content byte, `0x00`. -/
theorem derInteger_eq {n k : Nat} (hn : n < 2 ^ 256) (high : n < 2 ^ (8 * k - 1))
    (low : k = 1 ∨ 2 ^ (8 * (k - 1) - 1) ≤ n) :
    derInteger n = [0x02, UInt8.ofNat k] ++ natToBytes k n := by
  obtain _ | j := k
  · simp at high low; omega
  have hhigh : n < 128 * 256 ^ j := by
    rw [show 8 * (j + 1) - 1 = 7 + 8 * j by omega, Nat.pow_add, Nat.pow_mul] at high
    simpa using high
  have h256 : n < 256 ^ 32 := by simpa using hn
  by_cases hj : 256 ^ j ≤ n
  · have hj32 : j < 32 := (Nat.pow_lt_pow_iff_right (a := 256) (by decide)).mp (by omega)
    have hdiv : n / 256 ^ j < 128 :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr (by omega)
    have hdrop := dropWhile_natToBytes hj32 hj (by rw [Nat.pow_succ]; omega)
    rw [natToBytes_succ_eq_cons j n] at hdrop ⊢
    have : ¬ (UInt8.ofNat (n / 256 ^ j)).toNat ≥ 128 := by
      rw [toNat_ofNat_of_lt (by omega)]; omega
    simp only [derInteger, hdrop]
    rw [ite_eq_right this]
    simp [natToBytes_length]
  · obtain _ | i := j
    · have hzero : n = 0 := by simp at hj; omega
      subst hzero
      decide
    · have hlow : 128 * 256 ^ i ≤ n := by
        rcases low with h | h
        · omega
        · rw [show 8 * (i + 1 + 1 - 1) - 1 = 7 + 8 * i by omega, Nat.pow_add, Nat.pow_mul] at h
          simpa using h
      have hi32 : i < 32 := (Nat.pow_lt_pow_iff_right (a := 256) (by decide)).mp (by omega)
      have hdrop := dropWhile_natToBytes (n := n) hi32 (by omega) (by omega)
      have hdiv : 128 ≤ n / 256 ^ i :=
        (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr (by omega)
      have hdiv256 : n / 256 ^ i < 256 :=
        (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
          (by rw [Nat.pow_succ] at hj; omega)
      rw [natToBytes_succ_eq_cons i n] at hdrop
      rw [natToBytes_succ_eq_cons (i + 1) n, Nat.div_eq_of_lt (by omega),
        natToBytes_succ_eq_cons i n]
      have : (UInt8.ofNat (n / 256 ^ i)).toNat ≥ 128 := by
        rw [toNat_ofNat_of_lt hdiv256]; omega
      simp only [derInteger, hdrop]
      rw [ite_eq_left this]
      simp [natToBytes_length]

-- The bound for 33 bytes is `2 ^ 263`, above the default threshold for evaluating a power.
set_option exponentiation.threshold 263 in
/-- Every number below `2 ^ 256` has a byte count of at most 33 that meets the bounds. -/
private theorem exists_byteCount {n : Nat} (hn : n < 2 ^ 256) :
    ∃ k, 1 ≤ k ∧ k ≤ 33 ∧ n < 2 ^ (8 * k - 1) ∧
      (k = 1 ∨ 2 ^ (8 * (k - 1) - 1) ≤ n) := by
  suffices h : ∀ k, 1 ≤ k → k ≤ 33 → n < 2 ^ (8 * k - 1) →
      ∃ k, 1 ≤ k ∧ k ≤ 33 ∧ n < 2 ^ (8 * k - 1) ∧
        (k = 1 ∨ 2 ^ (8 * (k - 1) - 1) ≤ n) from
    h 33 (by decide) (by decide) (Nat.lt_trans hn (by decide))
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro h1 h33 high
    by_cases hk : k = 0
    · exact ⟨k + 1, h1, h33, high, .inl (by omega)⟩
    by_cases hlow : 2 ^ (8 * (k + 1 - 1) - 1) ≤ n
    · exact ⟨k + 1, h1, h33, high, .inr hlow⟩
    · exact ih (by omega) (by omega)
        (by rw [show 8 * k - 1 = 8 * (k + 1 - 1) - 1 by omega]; omega)

/-- Every number below `2 ^ 256` has its DER INTEGER on at most 33 content bytes. -/
private theorem exists_derInteger_eq {n : Nat} (hn : n < 2 ^ 256) :
    ∃ k, 1 ≤ k ∧ k ≤ 33 ∧ n < 256 ^ k ∧
      derInteger n = [0x02, UInt8.ofNat k] ++ natToBytes k n := by
  obtain ⟨k, h1, h33, high, low⟩ := exists_byteCount hn
  refine ⟨k, h1, h33, ?_, derInteger_eq hn high low⟩
  have : 2 ^ (8 * k - 1) ≤ 256 ^ k := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The decoder accepts exactly the encodings of r in [1, n) and s in [1, n/2], BIP 62.

It returns those r and s.

So no other bytes decode to the same r and s, and a signature has one accepted form. -/
theorem decodeSignature_eq_ok_iff {signature : ByteArray} {r s : Nat} :
    decodeSignature signature = .ok (r, s) ↔
      0 < r ∧ r < Fn.modulus ∧ 0 < s ∧ s ≤ Fn.modulus / 2 ∧
        encodeSignature r s = signature := by
  constructor
  · intro h
    unfold decodeSignature at h
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · split at h
            · rename_i hc
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hc
            · simp at h
        · simp at h
    · simp at h
  · rintro ⟨hr, hrn, hs, hsn, rfl⟩
    have hN : Fn.modulus < 2 ^ 256 := by decide
    obtain ⟨kr, hkr1, hkr, hrk, hder_r⟩ := exists_derInteger_eq (n := r) (by omega)
    obtain ⟨ks, hks1, hks, hsk, hder_s⟩ := exists_derInteger_eq (n := s) (by omega)
    have hdata : (encodeSignature r s).data.toList =
        0x30 :: UInt8.ofNat (kr + ks + 4) :: 0x02 :: UInt8.ofNat kr ::
          (natToBytes kr r ++ 0x02 :: UInt8.ofNat ks :: natToBytes ks s) := by
      simp [encodeSignature, hder_r, hder_s, natToBytes_length]
      apply UInt8.toNat_inj.mp
      simp
      omega
    have hsize : (encodeSignature r s).size = kr + ks + 6 := by
      rw [ByteArray.size, ← Array.length_toList, hdata]
      simp [natToBytes_length]
      omega
    have hkr8 : (UInt8.ofNat kr).toNat = kr := toNat_ofNat_of_lt (by omega)
    have hks8 : (UInt8.ofNat ks).toNat = ks := toNat_ofNat_of_lt (by omega)
    have htotal : (UInt8.ofNat (kr + ks + 4)).toNat = kr + ks + 4 := toNat_ofNat_of_lt (by omega)
    have hcond : 0 < r ∧ r < Fn.modulus ∧ 0 < s ∧ s ≤ Fn.modulus / 2 ∧
        encodeSignature r s = encodeSignature r s := ⟨hr, hrn, hs, hsn, rfl⟩
    unfold decodeSignature
    rw [hdata]
    simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      hsize, htotal, hkr8, hks8, List.take_left' (natToBytes_length kr r),
      List.drop_left' (natToBytes_length kr r), natToBytes_length,
      bytesToNat_natToBytes_of_lt hrk, bytesToNat_natToBytes_of_lt hsk]
    simp [hcond]


end EthLib.Networking.Proofs.Libp2p.PeerId
