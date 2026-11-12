module

public import EthLib.Cryptography.X25519
public import EthLib.Base.Proofs.LittleEndian

/-!
# Proofs: `X25519`

The clamp of RFC 7748 §5 fixes the range of the scalar that the ladder reads.

A clamped scalar is a multiple of eight, it is at least `2 ^ 254`, and it is below `2 ^ 255`.

The ladder reads bits 254 down to 0, so the cleared bit 255 is a bit it never reads.

The coordinate encoding of §5 is undone by its decoding, so a reduced coordinate survives its bytes.

These are statements about the definitions alone.

No theorem here says that the ladder computes a scalar multiple of a curve point.
-/

@[expose] public section

namespace EthLib.Cryptography.X25519

open EthLib.Base

/-! ## The byte that bounds a scalar

The clamp fixes the first and the last byte of the scalar, so each bound comes from one end.
-/

/-- A number read from `k + 1` bytes is below the bound that its last byte gives. -/
private theorem bytesToUint_lt_of_last : ∀ {k m : Nat} (f : Fin (k + 1) → UInt8),
    (f (Fin.last k)).toNat < m → bytesToUint (Vector.ofFn f) < m * 256 ^ k := by
  intro k
  induction k with
  | zero =>
    intro m f h
    simpa [bytesToUint_eq_foldr, Vector.toList_ofFn] using h
  | succ k ih =>
    intro m f h
    rw [bytesToUint_ofFn_succ, show m * 256 ^ (k + 1) = 256 * (m * 256 ^ k) from by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]]
    have hb := (f 0).toNat_lt
    have hrest := ih (fun i => f i.succ) (by simpa using h)
    omega

/-- A number read from `k + 1` bytes is at least the bound that its last byte gives. -/
private theorem le_bytesToUint_of_last : ∀ {k m : Nat} (f : Fin (k + 1) → UInt8),
    m ≤ (f (Fin.last k)).toNat → m * 256 ^ k ≤ bytesToUint (Vector.ofFn f) := by
  intro k
  induction k with
  | zero =>
    intro m f h
    simpa [bytesToUint_eq_foldr, Vector.toList_ofFn] using h
  | succ k ih =>
    intro m f h
    rw [bytesToUint_ofFn_succ, show m * 256 ^ (k + 1) = 256 * (m * 256 ^ k) from by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]]
    have hrest := ih (fun i => f i.succ) (by simpa using h)
    omega

/-- The 31 bytes below the last one carry 248 bits. -/
private theorem pow_256_31 : (256 : Nat) ^ 31 = 2 ^ 248 := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-- A last byte of 64 carries bit 254, and one of 128 would carry bit 255. -/
private theorem pow_256_31_mul : (256 : Nat) ^ 31 * 128 = 2 ^ 255 := by
  rw [pow_256_31, show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add]

/-! ## The bits that the clamp fixes -/

/-- Clearing the three low bits of a byte leaves a multiple of eight. -/
private theorem toNat_and_248 (b : UInt8) : (b &&& 248).toNat % 8 = 0 := by
  rw [UInt8.toNat_and, show (248 : UInt8).toNat = 248 from rfl,
    show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.and_two_pow_sub_one_eq_mod, Nat.and_assoc,
    show (248 : Nat) &&& (2 ^ 3 - 1) = 0 from by decide, Nat.and_zero]

/-- Clearing bit 7 of a byte and setting bit 6 leaves it at least 64 and below 128. -/
private theorem toNat_clamped_high (b : UInt8) :
    64 ≤ ((b &&& 127) ||| 64).toNat ∧ ((b &&& 127) ||| 64).toNat < 128 := by
  rw [UInt8.toNat_or, UInt8.toNat_and, show (127 : UInt8).toNat = 2 ^ 7 - 1 from rfl,
    show (64 : UInt8).toNat = 64 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  refine ⟨Nat.right_le_or, Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) (by decide)⟩

/-- A byte below 128 keeps its value when bit 7 is cleared. -/
private theorem and_127_of_lt {b : UInt8} (h : b.toNat < 128) : b &&& 127 = b := by
  apply UInt8.toNat.inj
  rw [UInt8.toNat_and, show (127 : UInt8).toNat = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

/-! ## The scalar that the ladder reads -/

/-- A clamped scalar is a multiple of eight, RFC 7748 §5. -/
theorem decodeScalar_mod_eight (key : Key) : decodeScalar key % 8 = 0 := by
  rw [decodeScalar, bytesToUint_ofFn_succ]
  simp only [Fin.val_zero, ↓reduceIte]
  have := toNat_and_248 key[(0 : Fin 32)]
  omega

/-- A clamped scalar is below `2 ^ 255`, RFC 7748 §5.

So bit 255 of the scalar is clear, and the ladder reads bits 254 down to 0 only. -/
theorem decodeScalar_lt (key : Key) : decodeScalar key < 2 ^ 255 := by
  have h := bytesToUint_lt_of_last (k := 31) (m := 128)
    (fun i : Fin 32 => if i.val = 0 then key[i] &&& 248
      else if i.val = 31 then (key[i] &&& 127) ||| 64 else key[i])
    (by simp only [Fin.val_last, ↓reduceIte]; exact (toNat_clamped_high _).2)
  simpa [decodeScalar, (Nat.mul_comm 128 (256 ^ 31)).trans pow_256_31_mul] using h

/-- A clamped scalar is at least `2 ^ 254`, RFC 7748 §5.

So bit 254 of the scalar is set, and the ladder reads a fixed number of bits. -/
theorem le_decodeScalar (key : Key) : 2 ^ 254 ≤ decodeScalar key := by
  have h := le_bytesToUint_of_last (k := 31) (m := 64)
    (fun i : Fin 32 => if i.val = 0 then key[i] &&& 248
      else if i.val = 31 then (key[i] &&& 127) ||| 64 else key[i])
    (by simp only [Fin.val_last, ↓reduceIte]; exact (toNat_clamped_high _).1)
  simpa [decodeScalar, show (64 : Nat) * 256 ^ 31 = 2 ^ 254 from by
    rw [pow_256_31, show (64 : Nat) = 2 ^ 6 from rfl]] using h

/-! ## The coordinate that the bytes carry -/

/-- Clearing bit 7 of a last byte already below 128 leaves the bytes of a coordinate. -/
private theorem mask_high_eq (v : Key) (h : v[31].toNat < 128) :
    (Vector.ofFn fun i : Fin 32 => if i.val = 31 then v[i] &&& 127 else v[i]) = v := by
  ext i hi
  simp only [Vector.getElem_ofFn]
  split
  · rename_i hv
    subst hv
    exact and_127_of_lt h
  · rfl

/-- Decoding the bytes of a reduced coordinate returns that coordinate, RFC 7748 §5. -/
@[simp] theorem decodeUCoordinate_encodeUCoordinate (u : Fp) :
    decodeUCoordinate (encodeUCoordinate u) = u := by
  have hmod : modulus < 2 ^ 255 := Nat.sub_lt (Nat.two_pow_pos 255) (by decide)
  have hlt : u.val < 256 ^ 31 * 128 := by rw [pow_256_31_mul]; omega
  have h32 : u.val < 256 ^ 32 := by
    rw [show (256 : Nat) ^ 32 = 2 ^ 256 from by
      rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]]
    omega
  -- A coordinate below `2 ^ 255` has a last byte below 128, so clearing bit 7 keeps it.
  have hbyte : (encodeUCoordinate u)[31].toNat < 128 := by
    rw [show (encodeUCoordinate u)[31] = UInt8.ofNat (u.val / 256 ^ 31) from by
      simp [encodeUCoordinate, uintToBytes], UInt8.toNat_ofNat']
    exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.div_lt_of_lt_mul hlt)
  rw [decodeUCoordinate, mask_high_eq _ hbyte, encodeUCoordinate, bytesToUint_uintToBytes,
    Nat.mod_eq_of_lt h32]
  exact Fin.ext (by rw [Fin.val_ofNat, Nat.mod_eq_of_lt u.isLt])

/-! ## The swap that the ladder leaves pending -/

/-- A swap by `false` is no swap, RFC 7748 §5. -/
@[simp] theorem conditionalSwap_false (s : LadderState) : conditionalSwap false s = s := by
  simp [conditionalSwap]

/-- A swap exchanges the two points and keeps the pending bit, so swapping twice is no swap. -/
theorem conditionalSwap_conditionalSwap (s : LadderState) :
    conditionalSwap true (conditionalSwap true s) = s := by
  simp [conditionalSwap]

/-- A step leaves the bit that it read pending, RFC 7748 §5. -/
@[simp] theorem swap_ladderStep (u : Fp) (bit : Bool) (s : LadderState) :
    (ladderStep u bit s).swap = bit := by
  simp [ladderStep]

/-- The ladder reads bit 0 last, so bit 0 of the scalar is the swap that it leaves pending. -/
theorem swap_ladder (scalar : Nat) (u : Fp) :
    (ladder scalar u).swap = scalar.testBit 0 := by
  rw [ladder, show (255 : Nat) = 254 + 1 from rfl, List.range_succ, List.foldl_append]
  simp

/-! ## The bits that the ladder never reads -/

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

/-- The ladder reads bits 254 down to 0, so a bit above bit 254 leaves its state unchanged.

A scalar that keeps bit 255 therefore runs the ladder exactly as the clamped one does.

Only the range of the clamped scalar records that bit 255 is cleared. -/
theorem ladder_mod_two_pow (scalar : Nat) (u : Fp) :
    ladder (scalar % 2 ^ 255) u = ladder scalar u := by
  unfold ladder
  refine foldl_ladderStep_congr u _ (fun i _ => ?_) _
  rw [Nat.testBit_mod_two_pow]
  have h : 254 - i < 255 := by omega
  simp [h]

end EthLib.Cryptography.X25519
