module

public import EthLib.Cryptography.Hash.Ripemd160
public import Mathlib.Logic.Function.Defs

/-!
# Proofs: `Hash.Ripemd160`

What is proved about RIPEMD-160:

- The added constants are the ones the authors derive from square and cube roots.
- Each group of sixteen steps of `r` and `r'` lists sixteen indices that include every message word, so it reads each once.
- Rotating a word left by `n` bits with `0 < n < 32` has left rotation by `32 - n` as its inverse.
- Each step with a rotation of 1 to 31 bits permutes the five-word state, and so do both lines.
- Padding fills whole blocks, with the least zeros that do, and keeps the message and the `0x80` byte in place.
- Every digest is 20 bytes.
- One block's compression, read as 32-bit vectors, is the compression of a model of the pseudo-code.
- The hash of every message is the hash of the model, with no bound on the length of the message.

The model follows the authors' pseudo-code over 32-bit vectors.

It runs both lines in one loop, as the pseudo-code does, and rotates bit vectors.

It reads each message word with its least significant byte first, as MD4 does (RFC 1320 §2).

It shares only the constants `K` and `K'`, the word orders and the rotation amounts with the code.

The model pads the message as MD4 does (RFC 1320 §3.1 and §3.2).

It runs the blocks from its own initial value.

Its digest puts the least significant byte of each word first.

The Python tests of the bindings check the hash against the published test vectors.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Ripemd160

/-! ## The model -/

namespace Spec

/-- A word of RIPEMD-160, whose addition `[+]` is modulo `2^32`. -/
abbrev Word := BitVec 32

/-- The five variables `A` to `E` of one line of the pseudo-code. -/
structure Vars where
  /-- The variable `A`. -/
  A : Word
  /-- The variable `B`. -/
  B : Word
  /-- The variable `C`. -/
  C : Word
  /-- The variable `D`. -/
  D : Word
  /-- The variable `E`. -/
  E : Word

/-- The variables at the start of a block: `A` to `E` take `h0` to `h4`. -/
def Vars.ofChain (h : Vector Word 5) : Vars := ⟨h[0], h[1], h[2], h[3], h[4]⟩

/-- The nonlinear function `f(j, x, y, z)` of step `j`, chosen by the range of `j`. -/
def f (j : Nat) (x y z : Word) : Word :=
  if j ≤ 15 then x ^^^ y ^^^ z
  else if j ≤ 31 then (x &&& y) ||| (~~~x &&& z)
  else if j ≤ 47 then (x ||| ~~~y) ^^^ z
  else if j ≤ 63 then (x &&& z) ||| (y &&& ~~~z)
  else x ^^^ (y ||| ~~~z)

/-- Step `j` of the left line: `f(j)`, the word `X[r(j)]`, `K(j)` and the rotation `s(j)`.

Then `A := E`, `E := D`, `D := rol_10(C)`, `C := B` and `B := T`. -/
def stepLeft (X : Vector Word 16) (v : Vars) (j : Fin 80) : Vars :=
  let T := (v.A + f j v.B v.C v.D + X[r[j]] + (K[j.val / 16]'(by omega)).toBitVec).rotateLeft
    s[j].toNat + v.E
  ⟨v.E, T, v.B, v.C.rotateLeft 10, v.D⟩

/-- Step `j` of the right line: `f(79 - j)`, the word `X[r'(j)]`, `K'(j)` and the rotation `s'(j)`.

Then `A' := E'`, `E' := D'`, `D' := rol_10(C')`, `C' := B'` and `B' := T`. -/
def stepRight (X : Vector Word 16) (v : Vars) (j : Fin 80) : Vars :=
  let T :=
    (v.A + f (79 - j.val) v.B v.C v.D + X[r'[j]] + (K'[j.val / 16]'(by omega)).toBitVec).rotateLeft
      s'[j].toNat + v.E
  ⟨v.E, T, v.B, v.C.rotateLeft 10, v.D⟩

/-- The loop `for j := 0 to 79`: step `j` of the left line, then step `j` of the right line. -/
def lines (X : Vector Word 16) (h : Vector Word 5) : Vars × Vars :=
  (List.finRange 80).foldl (fun lr j => (stepLeft X lr.1 j, stepRight X lr.2 j))
    (Vars.ofChain h, Vars.ofChain h)

/-- The chaining variable after one block of the pseudo-code.

- `T := h1 [+] C [+] D'`, `h1 := h2 [+] D [+] E'` and `h2 := h3 [+] E [+] A'`.
- `h3 := h4 [+] A [+] B'`, `h4 := h0 [+] B [+] C'` and `h0 := T`. -/
def compression (X : Vector Word 16) (h : Vector Word 5) : Vector Word 5 :=
  let left := (lines X h).1
  let right := (lines X h).2
  #v[h[1] + left.C + right.D, h[2] + left.D + right.E, h[3] + left.E + right.A,
    h[4] + left.A + right.B, h[0] + left.B + right.C]

/-- The sixteen words `X[i][0..15]` of the block at a byte offset.

Each word is four bytes, the least significant first (RFC 1320 §2). -/
def inputWords (block : ByteArray) (start : Nat) (whole : start + 64 ≤ block.size) :
    Vector Word 16 :=
  Vector.ofFn fun i =>
    block[start + 4 * i.val + 3].toBitVec ++ block[start + 4 * i.val + 2].toBitVec ++
      block[start + 4 * i.val + 1].toBitVec ++ block[start + 4 * i.val].toBitVec

/-- The initial value `h0` to `h4` of the pseudo-code. -/
def initial : Vector Word 5 := #v[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-- The least number of zero bytes after the `0x80` byte that leaves the length 56 modulo 64.

RFC 1320 §3.1 appends a set bit, then zero bits up to a length of 448 modulo 512.

The message is whole bytes, so the set bit and the seven zero bits after it are the byte `0x80`. -/
def zeroCount (size : Nat) : Nat := (119 - size % 64) % 64

/-- The padded message of RFC 1320 §3.1 and §3.2.

It is the message, `0x80`, zeros, and the low 64 bits of the bit length.

The length bytes put the least significant byte first, as RFC 1320 §2 and §3.2 do. -/
def padded (message : ByteArray) : ByteArray :=
  ⟨message.data ++ #[0x80] ++ Array.replicate (zeroCount message.size) 0 ++
    Array.ofFn fun i : Fin 8 => UInt8.ofNat (message.size * 8 % 2 ^ 64 / 2 ^ (8 * i.val) % 256)⟩

/-- The chaining variable after the first `count` blocks of a message, from a chaining variable.

This is the outer loop `for i := 0 to t-1` of the pseudo-code. -/
def blocks (message : ByteArray) (h : Vector Word 5) :
    (count : Nat) → 64 * count ≤ message.size → Vector Word 5
  | 0, _ => h
  | count + 1, within =>
    compression (inputWords message (64 * count) (by omega)) (blocks message h count (by omega))

/-- The hash result as twenty bytes: `h0` to `h4`, each word least significant byte first.

The paper takes the last chaining variable as the hash result.

The byte order is the one of MD4 (RFC 1320 §3.5), which the test values of the paper pin. -/
def digest (h : Vector Word 5) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 20 =>
    UInt8.ofNat ((h[i.val / 4]'(by omega)).toNat / 2 ^ (8 * (i.val % 4)) % 256)⟩

/-- RIPEMD-160 of a message: pad it, run every block from the initial value, and read the digest. -/
def hash (message : ByteArray) : ByteArray :=
  let input := padded message
  digest (blocks input initial (input.size / 64) (Nat.mul_div_le input.size 64))

end Spec

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

/-! ## Agreement with the model -/

/-- A five-word state read as the variables of the model. -/
def toVars (v : Vector UInt32 5) : Spec.Vars :=
  ⟨v[0].toBitVec, v[1].toBitVec, v[2].toBitVec, v[3].toBitVec, v[4].toBitVec⟩

/-- The function of group `g` is `f(j)` of the model for every step `j` in that group. -/
private theorem f_toBitVec_of_div (g : Fin 5) (j : Nat) (hg : j / 16 = g.val) (x y z : UInt32) :
    (f g x y z).toBitVec = Spec.f j x.toBitVec y.toBitVec z.toBitVec := by
  match g with
  | 0 =>
    have : j / 16 = 0 := hg
    rw [Spec.f, ite_eq_left (by omega)]
    simp [f]
  | 1 =>
    have : j / 16 = 1 := hg
    rw [Spec.f, ite_eq_right (by omega), ite_eq_left (by omega)]
    simp [f]
  | 2 =>
    have : j / 16 = 2 := hg
    rw [Spec.f, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    simp [f]
  | 3 =>
    have : j / 16 = 3 := hg
    rw [Spec.f, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_left (by omega)]
    simp [f]
  | 4 =>
    have : j / 16 = 4 := hg
    rw [Spec.f, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    simp [f]

/-- The group of step `j` gives `f(j)` of the model, and the reversed group gives `f(79 - j)`. -/
theorem f_toBitVec (j : Fin 80) (x y z : UInt32) :
    (f ⟨j.val / 16, by omega⟩ x y z).toBitVec = Spec.f j x.toBitVec y.toBitVec z.toBitVec ∧
      (f ⟨4 - j.val / 16, by omega⟩ x y z).toBitVec =
        Spec.f (79 - j.val) x.toBitVec y.toBitVec z.toBitVec :=
  ⟨f_toBitVec_of_div _ j rfl x y z, f_toBitVec_of_div _ (79 - j.val) (by simp; omega) x y z⟩

/-- Folding two independent updates over a pair is folding each over its own component. -/
private theorem foldl_pair {α β γ : Type} (F : α → γ → α) (G : β → γ → β) :
    ∀ (xs : List γ) (a : α) (b : β),
      xs.foldl (fun p j => (F p.1 j, G p.2 j)) (a, b) = (xs.foldl F a, xs.foldl G b)
  | [], _, _ => rfl
  | j :: js, a, b => foldl_pair F G js (F a j) (G b j)

/-- A map that turns each update into another carries a fold to the other fold. -/
private theorem foldl_hom {α β γ : Type} (φ : α → β) (F : α → γ → α) (G : β → γ → β)
    (hφ : ∀ a j, φ (F a j) = G (φ a) j) :
    ∀ (xs : List γ) (a : α), φ (xs.foldl F a) = xs.foldl G (φ a)
  | [], _ => rfl
  | j :: js, a => by rw [List.foldl_cons, List.foldl_cons, foldl_hom φ F G hφ js, hφ]

/-- Step `j` of the left line is step `j` of the left line of the model. -/
theorem step_left_toVars (X : Vector UInt32 16) (v : Vector UInt32 5) (j : Fin 80) :
    toVars (step ⟨j.val / 16, by omega⟩ v X[r[j]] K[(⟨j.val / 16, by omega⟩ : Fin 5)] s[j]) =
      Spec.stepLeft (X.map UInt32.toBitVec) (toVars v) j := by
  have hf (x y z : UInt32) := (f_toBitVec j x y z).1
  have hs (x : UInt32) : (rol x s[j.val]).toBitVec = x.toBitVec.rotateLeft s[j.val].toNat :=
    rol_toBitVec x s[j] (s_bounds j).1 (s_bounds j).2
  have h10 (x : UInt32) : (rol x 10).toBitVec = x.toBitVec.rotateLeft 10 :=
    rol_toBitVec x 10 (by decide) (by decide)
  simp [step, toVars, Spec.stepLeft, hf, hs, h10]

/-- Step `j` of the right line is step `j` of the right line of the model. -/
theorem step_right_toVars (X : Vector UInt32 16) (v : Vector UInt32 5) (j : Fin 80) :
    toVars (step ⟨4 - j.val / 16, by omega⟩ v X[r'[j]] K'[(⟨j.val / 16, by omega⟩ : Fin 5)] s'[j]) =
      Spec.stepRight (X.map UInt32.toBitVec) (toVars v) j := by
  have hf (x y z : UInt32) := (f_toBitVec j x y z).2
  have hs (x : UInt32) : (rol x s'[j.val]).toBitVec = x.toBitVec.rotateLeft s'[j.val].toNat :=
    rol_toBitVec x s'[j] (s'_bounds j).1 (s'_bounds j).2
  have h10 (x : UInt32) : (rol x 10).toBitVec = x.toBitVec.rotateLeft 10 :=
    rol_toBitVec x 10 (by decide) (by decide)
  simp [step, toVars, Spec.stepRight, hf, hs, h10]

/-- The loop of the model runs the left line and the right line of the code side by side. -/
theorem lines_toVars (X : Vector UInt32 16) (h : Vector UInt32 5) :
    Spec.lines (X.map UInt32.toBitVec) (h.map UInt32.toBitVec) =
      (toVars (line X h K r s false), toVars (line X h K' r' s' true)) := by
  have hstart : Spec.Vars.ofChain (h.map UInt32.toBitVec) = toVars h := by
    simp [Spec.Vars.ofChain, toVars]
  unfold Spec.lines line
  rw [foldl_pair, hstart]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [foldl_hom toVars _ _ (step_left_toVars X), foldl_hom toVars _ _ (step_right_toVars X)]

/-- Four bytes read least significant first are the four bytes concatenated, the last highest. -/
theorem little32_toBitVec (block : ByteArray) (start : Nat) (within : start + 4 ≤ block.size) :
    (little32 block start within).toBitVec =
      block[start + 3].toBitVec ++ block[start + 2].toBitVec ++ block[start + 1].toBitVec ++
        block[start].toBitVec := by
  refine BitVec.eq_of_getLsbD_eq fun i hi => ?_
  simp only [little32, UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, BitVec.getLsbD_or]
  simp only [BitVec.getLsbD_append]
  -- Bit `i` comes from byte `i / 8`, and every other byte is zero there.
  by_cases h8 : i < 8
  · simp [hi, h8, (by omega : i < 16), (by omega : i < 24)]
  by_cases h16 : i < 16
  · simp [hi, h8, h16, (by omega : i < 24), (by omega : i - 8 < 8),
      BitVec.getLsbD_of_ge _ i (by omega : 8 ≤ i)]
  by_cases h24 : i < 24
  · simp [hi, h8, h16, h24, decide_eq_false (by omega : ¬i - 8 < 8), (by omega : 8 ≤ i - 8),
      (by omega : i - 8 - 8 = i - 16),
      (by omega : i - 16 < 8), BitVec.getLsbD_of_ge _ i (by omega : 8 ≤ i)]
  · simp [hi, h8, h16, h24, decide_eq_false (by omega : ¬i - 8 < 8), (by omega : 8 ≤ i - 8),
      (by omega : i - 8 - 8 = i - 16),
      decide_eq_false (by omega : ¬i - 16 < 8), (by omega : i - 16 - 8 = i - 24),
      BitVec.getLsbD_of_ge _ i (by omega : 8 ≤ i),
      BitVec.getLsbD_of_ge _ (i - 16) (by omega : 8 ≤ i - 16)]

/-- The final mix of the chaining variable with both lines, read as 32-bit vectors. -/
private theorem combine_toBitVec (h left right : Vector UInt32 5) :
    (#v[h[1] + left[2] + right[3], h[2] + left[3] + right[4], h[3] + left[4] + right[0],
        h[4] + left[0] + right[1], h[0] + left[1] + right[2]] : Vector UInt32 5).map
      UInt32.toBitVec =
      #v[(h.map UInt32.toBitVec)[1] + (toVars left).C + (toVars right).D,
        (h.map UInt32.toBitVec)[2] + (toVars left).D + (toVars right).E,
        (h.map UInt32.toBitVec)[3] + (toVars left).E + (toVars right).A,
        (h.map UInt32.toBitVec)[4] + (toVars left).A + (toVars right).B,
        (h.map UInt32.toBitVec)[0] + (toVars left).B + (toVars right).C] := by
  simp [toVars]

/-- The left line of the code, read as the variables of the model, is the left line of the model. -/
private theorem toVars_line_left (X : Vector UInt32 16) (h : Vector UInt32 5) :
    toVars (line X h K r s false) =
      (Spec.lines (X.map UInt32.toBitVec) (h.map UInt32.toBitVec)).1 := by
  rw [lines_toVars]

/-- The right line of the code, read as variables of the model, is the right line of the model. -/
private theorem toVars_line_right (X : Vector UInt32 16) (h : Vector UInt32 5) :
    toVars (line X h K' r' s' true) =
      (Spec.lines (X.map UInt32.toBitVec) (h.map UInt32.toBitVec)).2 := by
  rw [lines_toVars]

/-- The sixteen words the code reads from a block are the words of the model. -/
private theorem words_toBitVec (block : ByteArray) (start : Nat) (whole : start + 64 ≤ block.size)
    (within : ∀ j : Fin 16, start + 4 * j.val + 4 ≤ block.size) :
    (Vector.ofFn fun j : Fin 16 => little32 block (start + 4 * j.val) (within j)).map
      UInt32.toBitVec =
      Spec.inputWords block start whole := by
  ext i hi
  simp [Spec.inputWords, little32_toBitVec]

/-- The compression of one block, read as 32-bit vectors, is the compression of the model.

The model reads the sixteen words of the block least significant byte first.

This holds for every chaining variable and every block. -/
theorem compress_toBitVec (h : Vector UInt32 5) (block : ByteArray) (start : Nat)
    (whole : start + 64 ≤ block.size) :
    (compress h block start whole).map UInt32.toBitVec =
      Spec.compression (Spec.inputWords block start whole) (h.map UInt32.toBitVec) := by
  simp only [compress]
  -- Turn each line of the code into the line of the model, then read the words as the model does.
  rw [combine_toBitVec, toVars_line_left, toVars_line_right, words_toBitVec block start whole,
    Spec.compression]

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

/-- Byte `i` of the length is digit `i` in base 256 of the low 64 bits of the bit length. -/
theorem lengthBytes_digit (size : Nat) (i : Fin 8) :
    ((lengthBytes size)[i.val]'(by simp)).toNat = size * 8 % 2 ^ 64 / 2 ^ (8 * i.val) % 256 := by
  have offset : (8 * UInt64.ofNat i.val).toNat = 8 * i.val := by
    simp [UInt64.toNat_mul, UInt64.toNat_ofNat]
    omega
  simp only [lengthBytes, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn,
    UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, offset]
  -- The conversion and the multiplication both reduce modulo `2^64`.
  have bits : (UInt64.ofNat size * 8).toNat = size * 8 % 2 ^ 64 := by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.toNat_ofNat, ← Nat.mul_mod]
  rw [bits, Nat.mod_eq_of_lt (show 8 * i.val < 64 by omega), Nat.shiftRight_eq_div_pow]

/-- The padding is the one of RFC 1320 §3.1 and §3.2, for every message. -/
theorem pad_eq_spec (message : ByteArray) : pad message = Spec.padded message := by
  have zeros : paddingZeros message.size = Spec.zeroCount message.size := by
    unfold paddingZeros Spec.zeroCount
    omega
  have length : (lengthBytes message.size).data =
      Array.ofFn fun i : Fin 8 =>
        UInt8.ofNat (message.size * 8 % 2 ^ 64 / 2 ^ (8 * i.val) % 256) := by
    apply Array.ext
    · exact (lengthBytes_size message.size).trans Array.size_ofFn.symm
    · intro p left right
      apply UInt8.toNat_inj.mp
      simpa [ByteArray.getElem_eq_getElem_data] using
        lengthBytes_digit message.size ⟨p, by simpa using left⟩
  -- The message, the `0x80` byte, the zeros and the length agree region by region.
  apply ByteArray.ext
  simp [pad, Spec.padded, zeros, length, ByteArray.data_append, ByteArray.push]

/-- The initial value of the code is the one of the model. -/
theorem IV_toBitVec : IV.map UInt32.toBitVec = Spec.initial := by
  decide +kernel

/-- The compression of the first `count` blocks, in order, is the chain of blocks of the model. -/
theorem foldl_compress_toBitVec (bytes : ByteArray) (h : Vector UInt32 5) (count : Nat)
    (whole : 64 * count ≤ bytes.size) :
    (Fin.foldl count (fun state i => compress state bytes (64 * i.val) (by omega)) h).map
        UInt32.toBitVec =
      Spec.blocks bytes (h.map UInt32.toBitVec) count whole := by
  induction count with
  | zero => simp [Spec.blocks]
  | succ count ih =>
    -- The last block runs on the chaining variable of the blocks before it.
    rw [Fin.foldl_succ_last, compress_toBitVec, Spec.blocks, ← ih (by omega)]
    rfl

/-- The digest is the model's digest. -/
theorem digest_eq_spec (state : Vector UInt32 5) :
    digest state = Spec.digest (state.map UInt32.toBitVec) := by
  apply ByteArray.ext
  apply Array.ext
  · simp [digest, Spec.digest]
  · intro i _ _
    apply UInt8.toNat_inj.mp
    -- Each byte is one base-256 digit of its word.
    simp [digest, Spec.digest, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
      UInt32.toNat_mul, UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show 8 * (i % 4) < 32 by omega)]

/--
RIPEMD-160 is the hash of the authors' pseudo-code with the padding of MD4, for every message.

The code and the model both take the low 64 bits of the bit length, as RFC 1320 §3.2 does.

So the statement bounds no message length.
-/
theorem hash_eq_spec (message : ByteArray) : hash message = Spec.hash message := by
  -- The padded bytes are the model's, and the chain of blocks then runs over them.
  have padded : ∀ bytes, bytes = Spec.padded message →
      ∀ within : ∀ i : Fin (bytes.size / 64), 64 * i.val + 64 ≤ bytes.size,
        digest (Fin.foldl (bytes.size / 64)
          (fun state i => compress state bytes (64 * i.val) (within i)) IV) =
          Spec.hash message := by
    intro bytes same within
    subst same
    rw [digest_eq_spec, foldl_compress_toBitVec _ _ _ (Nat.mul_div_le _ 64), IV_toBitVec,
      Spec.hash]
  exact padded (pad message) (pad_eq_spec message) _

end EthLib.Cryptography.Hash.Ripemd160
