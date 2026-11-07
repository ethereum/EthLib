module

public import EthLib.Cryptography.Hash.Ripemd160
public import Mathlib.Logic.Function.Defs

/-!
# Proofs: `Hash.Ripemd160`

What is proved about RIPEMD-160:

- The added constants are the ones the authors derive from square and cube roots.
- Each group of sixteen steps of `r` and `r'` lists sixteen indices that include every message word, so it reads each once.
- Rotating a word left by `n` bits with `0 < n < 32` has left rotation by `32 - n` as its inverse.
- Each step with a rotation of 1 to 31 bits, and both eighty-step lines, permutes the five-word
  state.
- Padding fills whole blocks, with the least zeros that do, and keeps the message and the `0x80` byte in place.
- Every digest is 20 bytes.

This does not prove that the hash equals a second, independent model of the algorithm.

The Python tests of the bindings check the hash against the published test vectors.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Ripemd160

/-! ## The constants -/

/-- The largest number below 4 whose square is at most the given one. -/
def wholeSquareRoot (value : Nat) : Nat :=
  (List.range 4).foldl (fun best candidate => if candidate * candidate ≤ value then candidate else best) 0

/-- The largest number below 3 whose cube is at most the given one. -/
def wholeCubeRoot (value : Nat) : Nat :=
  (List.range 3).foldl (fun best candidate => if candidate ^ 3 ≤ value then candidate else best) 0

/--
Whether a word is `int(2^30 * sqrt(prime))`.

It is exactly when `word^2 ≤ prime * 2^60 < (word + 1)^2`.
-/
def isSquareRootTimes2Pow30 (prime word : Nat) : Bool :=
  word ^ 2 ≤ prime * 2 ^ 60 && prime * 2 ^ 60 < (word + 1) ^ 2

/--
Whether a word is `int(2^30 * cbrt(prime))`.

It is exactly when `word^3 ≤ prime * 2^90 < (word + 1)^3`.
-/
def isCubeRootTimes2Pow30 (prime word : Nat) : Bool :=
  word ^ 3 ≤ prime * 2 ^ 90 && prime * 2 ^ 90 < (word + 1) ^ 3

/-- The constants of the left line are `int(2^30 * sqrt(p))` for p = 2, 3, 5, 7, as in `rmd160.txt`. -/
theorem K_from_square_roots :
    ([2, 3, 5, 7].zip ((K.toList.drop 1).map UInt32.toNat)).all
      (fun pair => isSquareRootTimes2Pow30 pair.1 pair.2) = true ∧
    K[0] = 0 := by
  decide +kernel

/-- The constants of the right line are `int(2^30 * cbrt(p))` for p = 2, 3, 5, 7, as in `rmd160.txt`. -/
theorem K'_from_cube_roots :
    ([2, 3, 5, 7].zip ((K'.toList.take 4).map UInt32.toNat)).all
      (fun pair => isCubeRootTimes2Pow30 pair.1 pair.2) = true ∧
    K'[4] = 0 := by
  decide +kernel

/-! ## The word order

Each group of sixteen steps reads every message word exactly once, in both lines.
-/

/-- The sixteen indices of one group of an index table. -/
def group (table : Vector (Fin 16) 80) (g : Nat) : List Nat :=
  (List.range 16).map fun i => (table[16 * g + i]!).val

/-- Every group of `r` is a permutation of the sixteen words. -/
theorem r_groups_permute :
    (List.range 5).all (fun g => (group r g).length == 16 && (List.range 16).all (group r g).contains) = true := by
  decide +kernel

/-- Every group of `r'` is a permutation of the sixteen words. -/
theorem r'_groups_permute :
    (List.range 5).all (fun g => (group r' g).length == 16 && (List.range 16).all (group r' g).contains) = true := by
  decide +kernel

/-! ## The rotation -/

/--
The rotation is the left rotation of the 32-bit word by `n` bits, for `0 < n < 32`.

The pseudo-code writes the rotation as a shift left by `n` and a shift right by `32 - n`.
-/
theorem rol_toBitVec (x n : UInt32) (h0 : 0 < n.toNat) (h32 : n.toNat < 32) :
    (rol x n).toBitVec = x.toBitVec.rotateLeft n.toNat := by
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  unfold rol
  -- The right shift wraps modulo `2^32`, so its distance is `32 - n` bits.
  simp [hi, Nat.mod_eq_of_lt h32,
    show (4294967296 - n.toNat) % 32 = 32 - n.toNat by omega]
  by_cases hlt : i < n.toNat
  · simp [hlt, BitVec.getLsbD_eq_getElem, (by omega : 32 - n.toNat + i < 32)]
  · simp [hlt, BitVec.getLsbD_of_ge _ _ (by omega : 32 ≤ 32 - n.toNat + i)]

/-- Subtracting a positive distance below 32 from 32 twice returns that distance. -/
private theorem thirtyTwo_sub_cancel {n : UInt32} (h0 : 0 < n.toNat) (h32 : n.toNat < 32) :
    (32 - n).toNat = 32 - n.toNat ∧ 32 - (32 - n) = n := by
  have hsub : (32 - n).toNat = 32 - n.toNat := by
    rw [UInt32.toNat_sub_of_le]
    · simp
    · exact UInt32.le_iff_toNat_le.mpr (Nat.le_of_lt h32)
  refine ⟨hsub, UInt32.toBitVec_inj.mp (BitVec.eq_of_toNat_eq ?_)⟩
  simp
  omega

/-- Rotating left by `n` and then by `32 - n` returns the word, for `0 < n < 32`. -/
theorem rol_rol (x n : UInt32) (h0 : 0 < n.toNat) (h32 : n.toNat < 32) :
    rol (rol x n) (32 - n) = x := by
  have hsub := (thirtyTwo_sub_cancel h0 h32).1
  apply UInt32.toBitVec_inj.mp
  rw [rol_toBitVec _ _ (by omega) (by omega), rol_toBitVec _ _ h0 h32, hsub]
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  simp only [BitVec.getLsbD_rotateLeft, Nat.mod_eq_of_lt (by omega : 32 - n.toNat < 32),
    Nat.mod_eq_of_lt h32, hi, decide_true, Bool.true_and]
  rw [show 32 - (32 - n.toNat) = n.toNat by omega]
  by_cases hlt : i < 32 - n.toNat
  · have hlt2 : n.toNat + i < 32 := by omega
    have hge2 : ¬ (n.toNat + i < n.toNat) := by omega
    simp [hlt, hlt2, hge2, show n.toNat + i - n.toNat = i by omega]
  · have hlt3 : i - (32 - n.toNat) < n.toNat := by omega
    simp [hlt, hlt3, show 32 - n.toNat + (i - (32 - n.toNat)) = i by omega]

/-- Left rotation by a fixed `n` with `0 < n < 32` permutes the 32-bit words. -/
theorem rol_left_bijective {n : UInt32} (h0 : 0 < n.toNat) (h32 : n.toNat < 32) :
    Function.Bijective (rol · n) := by
  obtain ⟨hsub, hcancel⟩ := thirtyTwo_sub_cancel h0 h32
  refine ⟨Function.LeftInverse.injective (g := (rol · (32 - n))) fun x => rol_rol x n h0 h32,
    Function.RightInverse.surjective (g := (rol · (32 - n))) fun x => ?_⟩
  simpa only [hcancel] using rol_rol x (32 - n) (by omega) (by omega)

/-- Every rotation amount of the left line is between 1 and 31. -/
theorem s_bounds (j : Fin 80) : 0 < s[j].toNat ∧ s[j].toNat < 32 := by
  revert j
  decide +kernel

/-- Every rotation amount of the right line is between 1 and 31. -/
theorem s'_bounds (j : Fin 80) : 0 < s'[j].toNat ∧ s'[j].toNat < 32 := by
  revert j
  decide +kernel

/-! ## One step and the two lines -/

/--
The inverse of one step for a rotation of 1 to 31 bits.

From `#v[E, T, B, rol_10(C), D]`, left rotation by 22 recovers `C`.

Left rotation of `T - E` by `32 - amount`, then subtraction, recovers `A`.
-/
private def unstep (g : Fin 5) (state : Vector UInt32 5) (word constant amount : UInt32) :
    Vector UInt32 5 :=
  let c := rol state[3] 22
  let a := rol (state[1] - state[0]) (32 - amount) - constant - word - f g state[2] c state[4]
  #v[a, state[2], c, state[4], state[0]]

/-- One step with a rotation of 1 to 31 bits permutes the five-word state. -/
theorem step_bijective (g : Fin 5) (word constant amount : UInt32)
    (h0 : 0 < amount.toNat) (h32 : amount.toNat < 32) :
    Function.Bijective (step g · word constant amount) := by
  obtain ⟨hsub, hcancel⟩ := thirtyTwo_sub_cancel h0 h32
  have hc1 : ∀ x : UInt32, rol (rol x 10) 22 = x := fun x =>
    rol_rol x 10 (by decide) (by decide)
  have hc2 : ∀ x : UInt32, rol (rol x 22) 10 = x := fun x =>
    rol_rol x 22 (by decide) (by decide)
  refine ⟨Function.LeftInverse.injective (g := (unstep g · word constant amount)) fun v => ?_,
    Function.RightInverse.surjective (g := (unstep g · word constant amount)) fun v => ?_⟩
  · ext k hk
    match k, hk with
    | 0, _ => simp [step, unstep, UInt32.add_sub_cancel, rol_rol _ _ h0 h32, hc1]
    | 1, _ => simp [step, unstep]
    | 2, _ => simp [step, unstep, hc1]
    | 3, _ => simp [step, unstep]
    | 4, _ => simp [step, unstep]
  · ext k hk
    match k, hk with
    | 0, _ => simp [step, unstep]
    | 1, _ =>
      have hrot : ∀ u : UInt32, rol (rol u (32 - amount)) amount = u := fun u => by
        simpa only [hcancel] using rol_rol u (32 - amount) (by omega) (by omega)
      simp [step, unstep, UInt32.sub_add_cancel, hrot]
    | 2, _ => simp [step, unstep]
    | 3, _ => simp [step, unstep, hc2]
    | 4, _ => simp [step, unstep]

/-- Folding a list of bijective updates permutes the state. -/
private theorem foldl_bijective {α β : Type} (stepFn : β → α → β) :
    ∀ (xs : List α), (∀ j ∈ xs, Function.Bijective (stepFn · j)) →
      Function.Bijective (fun start => xs.foldl stepFn start)
  | [], _ => Function.bijective_id
  | j :: js, hbij => by
    have hj := hbij j List.mem_cons_self
    have hjs := foldl_bijective stepFn js fun k hk => hbij k (List.mem_cons_of_mem j hk)
    simpa only [List.foldl_cons, Function.comp_def] using hjs.comp hj

/-- An eighty-step line permutes the five-word state when every rotation is 1 to 31 bits. -/
theorem line_bijective (X : Vector UInt32 16) (constants : Vector UInt32 5)
    (index : Vector (Fin 16) 80) (rotation : Vector UInt32 80) (reversed : Bool)
    (hrot : ∀ j : Fin 80, 0 < rotation[j].toNat ∧ rotation[j].toNat < 32) :
    Function.Bijective (line X · constants index rotation reversed) := by
  unfold line
  exact foldl_bijective _ (List.finRange 80) fun j _ =>
    step_bijective _ _ _ _ (hrot j).1 (hrot j).2

/-- The left line permutes the five-word state, for every message block. -/
theorem line_left_bijective (X : Vector UInt32 16) :
    Function.Bijective (line X · K r s false) :=
  line_bijective X K r s false s_bounds

/-- The right line permutes the five-word state, for every message block. -/
theorem line_right_bijective (X : Vector UInt32 16) :
    Function.Bijective (line X · K' r' s' true) :=
  line_bijective X K' r' s' true s'_bounds

/-! ## Padding -/

/-- The length takes eight bytes. -/
@[simp] theorem lengthBytes_size (size : Nat) : (lengthBytes size).size = 8 := by
  simp only [lengthBytes, ByteArray.size, Array.size_ofFn]

/-- Padding adds the `0x80` byte, the zeros, and the eight length bytes. -/
theorem pad_size (message : ByteArray) :
    (pad message).size = message.size + 1 + paddingZeros message.size + 8 := by
  simp only [pad, ByteArray.size_append, ByteArray.size_push, lengthBytes_size]
  simp only [ByteArray.size, Array.size_replicate]

/-- Padding adds fewer than a block of zeros. -/
theorem paddingZeros_lt (size : Nat) : paddingZeros size < 64 := Nat.mod_lt _ (by decide)

/-- A padded message is whole blocks. -/
theorem pad_size_mod (message : ByteArray) : (pad message).size % 64 = 0 := by
  rw [pad_size]
  unfold paddingZeros
  omega

/-- No fewer zeros would fill whole blocks. -/
theorem paddingZeros_minimal (size zeros : Nat) (complete : (size + 1 + zeros + 8) % 64 = 0) :
    paddingZeros size ≤ zeros := by
  unfold paddingZeros
  omega

/-- Padding keeps every byte of the message where it was. -/
theorem pad_prefix (message : ByteArray) (i : Nat) (within : i < message.size) :
    (pad message)[i]'(by rw [pad_size]; omega) = message[i] := by
  -- Name the bound, so it unfolds together with the padded message.
  have bound : i < (pad message).size := by rw [pad_size]; omega
  change (pad message)[i]'bound = message[i]
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp; omega)]
  exact Array.getElem_push_lt within

/-- The byte after the message is `0x80`. -/
theorem pad_delimiter (message : ByteArray) :
    (pad message)[message.size]'(by rw [pad_size]; omega) = 0x80 := by
  -- Name the bound, so it unfolds together with the padded message.
  have bound : message.size < (pad message).size := by rw [pad_size]; omega
  change (pad message)[message.size]'bound = 0x80
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp; omega), ByteArray.getElem_append_left (by simp)]
  exact Array.getElem_push_eq

/-- Every byte between `0x80` and the length is zero. -/
theorem pad_zero (message : ByteArray) (i : Nat) (within : i < paddingZeros message.size) :
    (pad message)[message.size + 1 + i]'(by rw [pad_size]; omega) = 0 := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  -- Name the bound, so it unfolds together with the padded message.
  have bound : message.size + 1 + i < (pad message).size := by rw [pad_size]; omega
  change (pad message)[message.size + 1 + i]'bound = 0
  unfold pad at bound ⊢
  rw [ByteArray.getElem_append_left (by simp only [ByteArray.size_append, ByteArray.size_push, zeroSize]; omega)]
  rw [ByteArray.getElem_append_right (by simp)]
  exact Array.getElem_replicate _

/-- The last eight bytes are the length. -/
theorem pad_length_suffix (message : ByteArray) :
    (pad message).extract ((pad message).size - 8) (pad message).size = lengthBytes message.size := by
  have zeroSize : (ByteArray.mk (Array.replicate (paddingZeros message.size) 0)).size =
      paddingZeros message.size := Array.size_replicate
  rw [pad_size]
  unfold pad
  apply ByteArray.extract_append_eq_right
  · simp only [ByteArray.size_append, ByteArray.size_push, zeroSize]
    omega
  · simp only [ByteArray.size_append, ByteArray.size_push, lengthBytes_size, zeroSize]

/-! ## The hash -/

/-- Every digest is 20 bytes long, whatever the message. -/
@[simp] theorem hash_size (message : ByteArray) : (hash message).size = 20 := by
  simp only [hash, digest, ByteArray.size, Array.size_ofFn]

end EthLib.Cryptography.Hash.Ripemd160
