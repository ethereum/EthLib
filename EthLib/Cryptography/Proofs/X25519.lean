module

public import EthLib.Cryptography.X25519
public import EthLib.Base.Proofs.LittleEndian

/-!
# Proofs: the X25519 clamp and coordinate encoding

The clamp of [RFC 7748 §5][rfc] clears the three low bits and bit 255 of a scalar.

It sets bit 254.

It keeps bits 3 to 253 of the key as they are.

The decoding of a coordinate clears bit 255 and reduces the rest modulo the field prime.

So a noncanonical coordinate is accepted, and the encoding of a reduced coordinate decodes to it.

The ladder ignores every scalar bit above bit 254, and bit 0 of a clamped scalar leaves no swap.

These are statements about the definitions alone.

The files under `Proofs/X25519/` prove that the ladder computes a scalar multiple on the curve.

[rfc]: https://www.rfc-editor.org/rfc/rfc7748#section-5
-/

@[expose] public section

namespace EthLib.Cryptography.X25519

open EthLib.Base

/-! ## The bytes at the two ends

The clamp and the mask change only the first and the last byte, so the proofs split them off.
-/

/-- A number read from `k + 1` bytes is the number of the first `k`, plus the last at `256 ^ k`. -/
private theorem bytesToUint_ofFn_castSucc : ∀ {k : Nat} (f : Fin (k + 1) → UInt8),
    bytesToUint (Vector.ofFn f)
      = bytesToUint (Vector.ofFn fun i : Fin k => f i.castSucc)
        + (f (Fin.last k)).toNat * 256 ^ k := by
  intro k
  induction k with
  | zero => intro f; simp [bytesToUint_eq_foldr, Vector.toList_ofFn]
  | succ k ih =>
    intro f
    rw [bytesToUint_ofFn_succ, bytesToUint_ofFn_succ (fun i : Fin (k + 1) => f i.castSucc),
      ih (fun i => f i.succ)]
    simp only [Fin.succ_last, Fin.castSucc_zero, Nat.pow_succ]
    rw [show (fun i : Fin k => f i.castSucc.succ) = fun i => f i.succ.castSucc from rfl]
    simp only [Nat.mul_add, Nat.add_assoc]
    congr 1
    rw [Nat.mul_left_comm, Nat.mul_comm (256 ^ k) 256]

/-- A number read from 32 bytes splits into its first byte, the 30 middle ones and its last. -/
private theorem bytesToUint_ofFn_32 (f : Fin 32 → UInt8) :
    bytesToUint (Vector.ofFn f) = (f 0).toNat
      + 256 * bytesToUint (Vector.ofFn fun i : Fin 30 => f i.succ.castSucc)
      + (f 31).toNat * 256 ^ 31 := by
  rw [bytesToUint_ofFn_castSucc, bytesToUint_ofFn_succ]
  rfl

/-- The bytes of a key split in the same way. -/
private theorem bytesToUint_key (key : Key) :
    bytesToUint key = key[0].toNat
      + 256 * bytesToUint (Vector.ofFn fun i : Fin 30 => key[i.succ.castSucc])
      + key[31].toNat * 256 ^ 31 := by
  have h := bytesToUint_ofFn_32 fun i => key[i]
  rwa [show (Vector.ofFn fun i : Fin 32 => key[i]) = key from
    Vector.ext fun i hi => by simp] at h

/-! ## The bits that the clamp and the mask fix -/

/-- Clearing the three low bits of a byte rounds it down to a multiple of eight. -/
private theorem toNat_and_248 (b : UInt8) : (b &&& 248).toNat = b.toNat / 8 * 8 := by
  rw [UInt8.toNat_and, show (248 : UInt8).toNat = (2 ^ 5 - 1) * 2 ^ 3 from rfl,
    show (8 : Nat) = 2 ^ 3 from rfl]
  have hb := b.toNat_lt
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h3 : 3 ≤ i
  · rw [Nat.sub_add_cancel h3]
    by_cases h8 : i - 3 < 5
    · simp [h3, h8]
    · -- A byte has no bit from bit 8 up.
      have : b.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb
          (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [h3, h8, this]
  · simp [h3]

/-- Clearing bit 7 of a byte keeps its remainder by 128. -/
private theorem toNat_and_127 (b : UInt8) : (b &&& 127).toNat = b.toNat % 128 := by
  rw [UInt8.toNat_and, show (127 : UInt8).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]

/-- Clearing bit 7 of a byte and setting bit 6 gives 64 plus its remainder by 64. -/
private theorem toNat_clamp_high (b : UInt8) :
    ((b &&& 127) ||| 64).toNat = 64 + b.toNat % 64 := by
  rw [UInt8.toNat_or, toNat_and_127, show (64 : UInt8).toNat = 2 ^ 6 from rfl,
    show (128 : Nat) = 2 ^ 7 from rfl, show (64 : Nat) = 2 ^ 6 from rfl, Nat.add_comm,
    ← Nat.or_two_pow_eq_add_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 6))]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_two_pow]
  by_cases h : i = 6
  · subst h; simp
  · by_cases h6 : i < 6
    · simp [h6, show i < 7 by omega]
    · simp [h6, show ¬i < 7 by omega, Ne.symm h]

/-- The clamped bytes, read back, are the key with its low bits and high bits replaced. -/
private theorem clamp_arith {a m c : Nat} (ha : a < 256) (hm : m < 256 ^ 30) :
    a / 8 * 8 + 256 * m + (64 + c % 64) * 256 ^ 31
      = 2 ^ 254 + (a + 256 * m + c * 256 ^ 31) % 2 ^ 254 / 8 * 8 := by
  simp only [Nat.reducePow] at hm ⊢
  omega

/-- The masked bytes, read back, are the number below bit 255. -/
private theorem mask_arith {l c : Nat} (hl : l < 256 ^ 31) :
    l + c % 128 * 256 ^ 31 = (l + c * 256 ^ 31) % 2 ^ 255 := by
  simp only [Nat.reducePow] at hl ⊢
  omega

/-! ## The scalar that the ladder reads -/

/-- The clamp sets bit 254, clears bits 0 to 2 and bit 255, and keeps bits 3 to 253, RFC 7748 §5.

Bits above bit 255 do not occur, since the key has 32 bytes. -/
theorem decodeScalar_eq (key : Key) :
    decodeScalar key = 2 ^ 254 + bytesToUint key % 2 ^ 254 / 8 * 8 := by
  have hmid : (Vector.ofFn fun i : Fin 30 =>
      (fun i : Fin 32 => if i.val = 0 then key[i] &&& 248
        else if i.val = 31 then (key[i] &&& 127) ||| 64 else key[i]) i.succ.castSucc)
      = Vector.ofFn fun i : Fin 30 => key[i.succ.castSucc] := by
    apply Vector.ext
    intro i hi
    simp [show i ≠ 30 by omega]
  have hd : decodeScalar key = (key[0] &&& 248).toNat
      + 256 * bytesToUint (Vector.ofFn fun i : Fin 30 => key[i.succ.castSucc])
      + ((key[31] &&& 127) ||| 64).toNat * 256 ^ 31 := by
    rw [decodeScalar, bytesToUint_ofFn_32, hmid]
    rfl
  rw [hd, bytesToUint_key, toNat_and_248 key[0], toNat_clamp_high key[31]]
  exact clamp_arith key[0].toNat_lt (bytesToUint_lt _)

/-- A clamped scalar is a multiple of eight, the cofactor of Curve25519, RFC 7748 §5. -/
theorem decodeScalar_mod_eight (key : Key) : decodeScalar key % 8 = 0 := by
  rw [decodeScalar_eq]
  omega

/-- A clamped scalar is below `2 ^ 255`, RFC 7748 §5.

So bit 255 of the scalar is clear. -/
theorem decodeScalar_lt (key : Key) : decodeScalar key < 2 ^ 255 := by
  have := Nat.mod_lt (bytesToUint key) (Nat.two_pow_pos 254)
  rw [decodeScalar_eq]
  omega

/-- A clamped scalar is at least `2 ^ 254`, RFC 7748 §5.

With the upper bound, bit 254 of the scalar is set. -/
theorem le_decodeScalar (key : Key) : 2 ^ 254 ≤ decodeScalar key := by
  rw [decodeScalar_eq]
  omega

/-! ## The coordinate that the bytes carry -/

/-- Decoding clears bit 255 and reduces modulo the field prime, RFC 7748 §5.

So a noncanonical value, from the prime up to `2 ^ 255`, is accepted and reduced. -/
theorem val_decodeUCoordinate (u : Key) :
    (decodeUCoordinate u).val = bytesToUint u % 2 ^ 255 % modulus := by
  have hlow : (Vector.ofFn fun i : Fin 31 =>
      (fun i : Fin 32 => if i.val = 31 then u[i] &&& 127 else u[i]) i.castSucc)
      = Vector.ofFn fun i : Fin 31 => u[i.castSucc] := by
    apply Vector.ext
    intro i hi
    simp [show i ≠ 31 by omega]
  have hd : bytesToUint (Vector.ofFn fun i : Fin 32 =>
        if i.val = 31 then u[i] &&& 127 else u[i])
      = bytesToUint (Vector.ofFn fun i : Fin 31 => u[i.castSucc])
        + (u[31] &&& 127).toNat * 256 ^ 31 := by
    rw [bytesToUint_ofFn_castSucc, hlow]
    rfl
  have hu : bytesToUint u
      = bytesToUint (Vector.ofFn fun i : Fin 31 => u[i.castSucc]) + u[31].toNat * 256 ^ 31 := by
    have h := bytesToUint_ofFn_castSucc fun i : Fin 32 => u[i]
    rwa [show (Vector.ofFn fun i : Fin 32 => u[i]) = u from
      Vector.ext fun i hi => by simp] at h
  rw [decodeUCoordinate, Fin.val_ofNat, hd, hu, toNat_and_127 u[31],
    mask_arith (bytesToUint_lt _)]

/-- Decoding the bytes of a reduced coordinate returns that coordinate, RFC 7748 §5. -/
@[simp] theorem decodeUCoordinate_encodeUCoordinate (u : Fp) :
    decodeUCoordinate (encodeUCoordinate u) = u := by
  have hmod : modulus < 2 ^ 255 := Nat.sub_lt (Nat.two_pow_pos 255) (by decide)
  have h32 : u.val < 256 ^ 32 := by
    rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]
    omega
  apply Fin.ext
  rw [val_decodeUCoordinate, encodeUCoordinate, bytesToUint_uintToBytes, Nat.mod_eq_of_lt h32,
    Nat.mod_eq_of_lt (show u.val < 2 ^ 255 by omega), Nat.mod_eq_of_lt u.isLt]

/-! ## The bits that the ladder reads -/

/-- The ladder reads bit 0 last, so bit 0 of the scalar is the swap that it leaves pending. -/
private theorem swap_ladder (scalar : Nat) (u : Fp) :
    (ladder scalar u).swap = scalar.testBit 0 := by
  rw [ladder, show (255 : Nat) = 254 + 1 from rfl, List.range_succ, List.foldl_append]
  simp [ladderStep]

/-- A clamped scalar leaves no swap pending at the end of the ladder.

Bit 0 of a clamped scalar is clear, RFC 7748 §5. -/
theorem swap_ladder_decodeScalar (key : Key) (u : Fp) :
    (ladder (decodeScalar key) u).swap = false := by
  have := decodeScalar_mod_eight key
  rw [swap_ladder, Nat.testBit_zero]
  simp only [decide_eq_false_iff_not]
  omega

/-- Two scalars that agree on the bits the steps read run the ladder to the same state. -/
private theorem foldl_ladderStep_congr {a b : Nat} (u : Fp) (l : List Nat)
    (h : ∀ i ∈ l, a.testBit (254 - i) = b.testBit (254 - i)) (s : LadderState) :
    l.foldl (fun s i => ladderStep u (a.testBit (254 - i)) s) s
      = l.foldl (fun s i => ladderStep u (b.testBit (254 - i)) s) s := by
  induction l generalizing s with
  | nil => rfl
  | cons i t ih =>
    rw [List.foldl_cons, List.foldl_cons, h i (by simp)]
    exact ih (fun j hj => h j (by simp [hj])) _

/-- The ladder reads bits 254 down to 0, so the bits above bit 254 do not change its result.

A scalar runs the ladder exactly as the same scalar with bit 255 cleared does.

So the ladder cannot observe bit 255.

Only the clamp theorems record that the clamp clears it. -/
theorem ladder_mod_two_pow (scalar : Nat) (u : Fp) :
    ladder (scalar % 2 ^ 255) u = ladder scalar u := by
  unfold ladder
  refine foldl_ladderStep_congr u _ (fun i _ => ?_) _
  rw [Nat.testBit_mod_two_pow]
  have h : 254 - i < 255 := by omega
  simp [h]

end EthLib.Cryptography.X25519
