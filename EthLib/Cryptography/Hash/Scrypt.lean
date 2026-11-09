module

public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Pbkdf2

/-!
# scrypt

[RFC 7914 §§3 to 6][scrypt] defines Salsa20/8, BlockMix, ROMix and scrypt.

The bounds on the parameters come from [RFC 7914 §2][params].

The ROMix table stores byte arrays, so its payload is `128 * r * N` bytes.

Passwords are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

ROMix reads its table at indices that depend on the password.

Parameters within the bounds can still ask for more memory than the machine has.

[scrypt]: https://www.rfc-editor.org/rfc/rfc7914#section-3
[params]: https://www.rfc-editor.org/rfc/rfc7914#section-2
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Scrypt

/-- The input and output size of Salsa20/8, RFC 7914 §3, in bytes. -/
def SALSA_BLOCK_SIZE : Nat := 64

/-- The byte count per unit of `r`, RFC 7914 §4. -/
def BLOCK_SIZE : Nat := 128

/-- Every way scrypt or one of its steps can reject its input, RFC 7914 §2. -/
inductive ScryptError where
  /-- The cost `N` was not a power of two above 1 and below `2^(16 * r)`. -/
  | invalidCost (n : Nat)
  /-- The block size `r` was zero. -/
  | invalidBlockSize (r : Nat)
  /-- The parallelization `p` was zero, or `p * 128 * r` exceeded `(2^32 - 1) * 32`. -/
  | invalidParallelization (p : Nat)
  /-- The requested length was zero. -/
  | emptyOutput
  /-- The requested length exceeded `(2^32 - 1) * 32` bytes. -/
  | outputTooLong (length : Nat)
  /-- A step received a block of the wrong size. -/
  | invalidInputSize (expected actual : Nat)
  /-- PBKDF2 rejected the password or the salt. -/
  | pbkdf2 (error : Pbkdf2.Pbkdf2Error)
deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def ScryptError.code : ScryptError → UInt32
  | .invalidCost _ => 1
  | .invalidBlockSize _ => 2
  | .invalidParallelization _ => 3
  | .emptyOutput => 4
  | .outputTooLong _ => 5
  | .invalidInputSize _ _ => 6
  | .pbkdf2 _ => 7

/-- A value `B` or `X` of BlockMix and ROMix, with its `128 * r` bytes in the type. -/
abbrev MixBlock (r : Nat) := { bytes : ByteArray // bytes.size = 128 * r }

/-- The sixteen words of the Salsa20/8 state, each read little-endian from 4 bytes, RFC 7914 §3. -/
structure State where
  (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt32)

/-- A left rotation in a 32-bit word, RFC 7914 §3. -/
@[inline] def rotl (x shift : UInt32) : UInt32 :=
  (x <<< shift) ||| (x >>> (32 - shift))

/-- Four bytes read as a little-endian word, RFC 7914 §3. -/
@[inline] def little32 (a b c d : UInt8) : UInt32 :=
  a.toUInt32 ||| b.toUInt32 <<< 8 ||| c.toUInt32 <<< 16 ||| d.toUInt32 <<< 24

/-- Read the sixteen words of a whole 64-byte block. -/
def State.ofBytes (bytes : ByteArray) (start : Nat) (whole : start + 64 ≤ bytes.size) :
    State :=
  let word (i : Nat) (within : i < 16) : UInt32 :=
    little32 (bytes[start + 4 * i]'(by omega)) (bytes[start + 4 * i + 1]'(by omega))
      (bytes[start + 4 * i + 2]'(by omega)) (bytes[start + 4 * i + 3]'(by omega))
  ⟨word 0 (by decide), word 1 (by decide), word 2 (by decide), word 3 (by decide),
    word 4 (by decide), word 5 (by decide), word 6 (by decide), word 7 (by decide),
    word 8 (by decide), word 9 (by decide), word 10 (by decide), word 11 (by decide),
    word 12 (by decide), word 13 (by decide), word 14 (by decide), word 15 (by decide)⟩

/-- The byte selected by a shift of a word. -/
@[inline] def byteAt (word shift : UInt32) : UInt8 := (word >>> shift).toUInt8

/-- The words of a state as 64 little-endian bytes, RFC 7914 §3. -/
def State.bytes (s : State) : ByteArray :=
  ⟨#[
    byteAt s.x0 0, byteAt s.x0 8, byteAt s.x0 16, byteAt s.x0 24,
    byteAt s.x1 0, byteAt s.x1 8, byteAt s.x1 16, byteAt s.x1 24,
    byteAt s.x2 0, byteAt s.x2 8, byteAt s.x2 16, byteAt s.x2 24,
    byteAt s.x3 0, byteAt s.x3 8, byteAt s.x3 16, byteAt s.x3 24,
    byteAt s.x4 0, byteAt s.x4 8, byteAt s.x4 16, byteAt s.x4 24,
    byteAt s.x5 0, byteAt s.x5 8, byteAt s.x5 16, byteAt s.x5 24,
    byteAt s.x6 0, byteAt s.x6 8, byteAt s.x6 16, byteAt s.x6 24,
    byteAt s.x7 0, byteAt s.x7 8, byteAt s.x7 16, byteAt s.x7 24,
    byteAt s.x8 0, byteAt s.x8 8, byteAt s.x8 16, byteAt s.x8 24,
    byteAt s.x9 0, byteAt s.x9 8, byteAt s.x9 16, byteAt s.x9 24,
    byteAt s.x10 0, byteAt s.x10 8, byteAt s.x10 16, byteAt s.x10 24,
    byteAt s.x11 0, byteAt s.x11 8, byteAt s.x11 16, byteAt s.x11 24,
    byteAt s.x12 0, byteAt s.x12 8, byteAt s.x12 16, byteAt s.x12 24,
    byteAt s.x13 0, byteAt s.x13 8, byteAt s.x13 16, byteAt s.x13 24,
    byteAt s.x14 0, byteAt s.x14 8, byteAt s.x14 16, byteAt s.x14 24,
    byteAt s.x15 0, byteAt s.x15 8, byteAt s.x15 16, byteAt s.x15 24]⟩

/-- Every encoded state has the 64 bytes required by BlockMix. -/
theorem State.bytes_size (s : State) : s.bytes.size = 64 := rfl

/-- A double round: one round on the columns, then one round on the rows, RFC 7914 §3.

Each round applies four quarter-rounds, one per column or row. -/
@[inline] def doubleRound (s : State) : State :=
  let x0 := s.x0
  let x1 := s.x1
  let x2 := s.x2
  let x3 := s.x3
  let x4 := s.x4
  let x5 := s.x5
  let x6 := s.x6
  let x7 := s.x7
  let x8 := s.x8
  let x9 := s.x9
  let x10 := s.x10
  let x11 := s.x11
  let x12 := s.x12
  let x13 := s.x13
  let x14 := s.x14
  let x15 := s.x15
  let x4 := x4 ^^^ rotl (x0 + x12) 7
  let x8 := x8 ^^^ rotl (x4 + x0) 9
  let x12 := x12 ^^^ rotl (x8 + x4) 13
  let x0 := x0 ^^^ rotl (x12 + x8) 18
  let x9 := x9 ^^^ rotl (x5 + x1) 7
  let x13 := x13 ^^^ rotl (x9 + x5) 9
  let x1 := x1 ^^^ rotl (x13 + x9) 13
  let x5 := x5 ^^^ rotl (x1 + x13) 18
  let x14 := x14 ^^^ rotl (x10 + x6) 7
  let x2 := x2 ^^^ rotl (x14 + x10) 9
  let x6 := x6 ^^^ rotl (x2 + x14) 13
  let x10 := x10 ^^^ rotl (x6 + x2) 18
  let x3 := x3 ^^^ rotl (x15 + x11) 7
  let x7 := x7 ^^^ rotl (x3 + x15) 9
  let x11 := x11 ^^^ rotl (x7 + x3) 13
  let x15 := x15 ^^^ rotl (x11 + x7) 18
  let x1 := x1 ^^^ rotl (x0 + x3) 7
  let x2 := x2 ^^^ rotl (x1 + x0) 9
  let x3 := x3 ^^^ rotl (x2 + x1) 13
  let x0 := x0 ^^^ rotl (x3 + x2) 18
  let x6 := x6 ^^^ rotl (x5 + x4) 7
  let x7 := x7 ^^^ rotl (x6 + x5) 9
  let x4 := x4 ^^^ rotl (x7 + x6) 13
  let x5 := x5 ^^^ rotl (x4 + x7) 18
  let x11 := x11 ^^^ rotl (x10 + x9) 7
  let x8 := x8 ^^^ rotl (x11 + x10) 9
  let x9 := x9 ^^^ rotl (x8 + x11) 13
  let x10 := x10 ^^^ rotl (x9 + x8) 18
  let x12 := x12 ^^^ rotl (x15 + x14) 7
  let x13 := x13 ^^^ rotl (x12 + x15) 9
  let x14 := x14 ^^^ rotl (x13 + x12) 13
  let x15 := x15 ^^^ rotl (x14 + x13) 18
  ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15⟩

/-- Four double rounds give the eight rounds of Salsa20/8, RFC 7914 §3. -/
def rounds : Nat → State → State
  | 0, s => s
  | count + 1, s => rounds count (doubleRound s)

/-- XOR the corresponding words of two states. -/
@[inline] def State.xor (a b : State) : State :=
  ⟨a.x0 ^^^ b.x0, a.x1 ^^^ b.x1, a.x2 ^^^ b.x2,
    a.x3 ^^^ b.x3, a.x4 ^^^ b.x4, a.x5 ^^^ b.x5,
    a.x6 ^^^ b.x6, a.x7 ^^^ b.x7, a.x8 ^^^ b.x8,
    a.x9 ^^^ b.x9, a.x10 ^^^ b.x10, a.x11 ^^^ b.x11,
    a.x12 ^^^ b.x12, a.x13 ^^^ b.x13, a.x14 ^^^ b.x14,
    a.x15 ^^^ b.x15⟩

/-- Add the input words after the eight rounds, RFC 7914 §3. -/
def salsa208Core (input : State) : State :=
  let output := rounds 4 input
  ⟨output.x0 + input.x0, output.x1 + input.x1, output.x2 + input.x2,
    output.x3 + input.x3, output.x4 + input.x4, output.x5 + input.x5,
    output.x6 + input.x6, output.x7 + input.x7, output.x8 + input.x8,
    output.x9 + input.x9, output.x10 + input.x10, output.x11 + input.x11,
    output.x12 + input.x12, output.x13 + input.x13, output.x14 + input.x14,
    output.x15 + input.x15⟩

/-- Salsa20/8 on exactly 64 bytes, RFC 7914 §3. -/
def salsa208 (input : ByteArray) : Except ScryptError ByteArray :=
  if whole : input.size = 64 then
    .ok ((salsa208Core (State.ofBytes input 0 (by omega))).bytes)
  else .error (.invalidInputSize SALSA_BLOCK_SIZE input.size)

/-- The successive `Y[i]` blocks, with even and odd indices collected separately. -/
def blockMixLoop (input : ByteArray) : (count i : Nat) →
    64 * i + 64 * count ≤ input.size → State → ByteArray → ByteArray → ByteArray
  | 0, _, _, _, even, odd => even ++ odd
  | count + 1, i, whole, previous, even, odd =>
    let next := salsa208Core (previous.xor (State.ofBytes input (64 * i) (by omega)))
    if i % 2 = 0 then
      blockMixLoop input count (i + 1) (by omega) next (even ++ next.bytes) odd
    else
      blockMixLoop input count (i + 1) (by omega) next even (odd ++ next.bytes)

/-- Each BlockMix step adds one whole 64-byte block. -/
theorem blockMixLoop_size (input : ByteArray) (count i : Nat)
    (whole : 64 * i + 64 * count ≤ input.size) (previous : State) (even odd : ByteArray) :
    (blockMixLoop input count i whole previous even odd).size =
      even.size + odd.size + 64 * count := by
  induction count generalizing i previous even odd with
  | zero => simp [blockMixLoop]
  | succ count ih =>
    simp only [blockMixLoop]
    split <;> rw [ih] <;> simp only [ByteArray.size_append, State.bytes_size] <;> omega

/-- BlockMix with its `128 * r` byte length preserved, RFC 7914 §4. -/
def blockMixCore (r : Nat) (positive : 0 < r) (input : MixBlock r) : MixBlock r :=
  let previous := State.ofBytes input.val (128 * r - 64) (by have := input.property; omega)
  let whole : 64 * 0 + 64 * (2 * r) ≤ input.val.size := by have := input.property; omega
  ⟨blockMixLoop input.val (2 * r) 0 whole previous ByteArray.empty ByteArray.empty,
    by rw [blockMixLoop_size]; simp; omega⟩

/-- BlockMix on `2 * r` consecutive 64-byte blocks, RFC 7914 §4. -/
def blockMix (input : ByteArray) (r : Nat) : Except ScryptError ByteArray :=
  if positive : 0 < r then
    if whole : input.size = 128 * r then .ok (blockMixCore r positive ⟨input, whole⟩).val
    else .error (.invalidInputSize (BLOCK_SIZE * r) input.size)
  else .error (.invalidBlockSize r)

/-- `Integerify`: the last 64 bytes of a ROMix value as a little-endian integer, RFC 7914 §5. -/
def integerify (r : Nat) (x : MixBlock r) : Nat :=
  (x.val.extract (128 * r - 64) (128 * r)).data.foldr (fun byte acc => 256 * acc + byte.toNat) 0

/-- Store each `X` before its BlockMix step, RFC 7914 §5, step 2. -/
def romixFill (r : Nat) (positive : 0 < r) {n : Nat} : (count i : Nat) → i + count = n →
    Vector (MixBlock r) n → MixBlock r → Vector (MixBlock r) n × MixBlock r
  | 0, _, _, table, x => (table, x)
  | count + 1, i, whole, table, x =>
    let table := table.set i x (by omega)
    romixFill r positive count (i + 1) (by omega) table (blockMixCore r positive x)

/-- Select from the stored table before each BlockMix, RFC 7914 §5, step 3. -/
def romixRead (r : Nat) (positive : 0 < r) (n : Nat) (nonzero : 0 < n)
    (table : Vector (MixBlock r) n) : Nat → MixBlock r → MixBlock r
  | 0, x => x
  | count + 1, x =>
    let index := integerify r x % n
    let mixed : MixBlock r := ⟨Base.xorByteArray x.val (table[index]'(Nat.mod_lt _ nonzero)).val,
      by rw [Base.xorByteArray_size]; exact x.property⟩
    romixRead r positive n nonzero table count (blockMixCore r positive mixed)

/-- ROMix with its input size in the type, RFC 7914 §5. -/
def romixCore (r : Nat) (positive : 0 < r) (n : Nat) (nonzero : 0 < n)
    (input : MixBlock r) : MixBlock r :=
  let (table, x) := romixFill r positive n 0 (by omega) (Vector.replicate n input) input
  romixRead r positive n nonzero table n x

/-- The cost bound of RFC 7914 §§2 and 5, without constructing `2^(16 * r)`. -/
def validCost (n r : Nat) : Bool :=
  1 < n && n &&& (n - 1) == 0 && n.log2 < 16 * r

/-- ROMix on `128 * r` bytes with a valid power-of-two cost, RFC 7914 §5. -/
def romix (input : ByteArray) (n r : Nat) : Except ScryptError ByteArray :=
  if positive : 0 < r then
    if cost : validCost n r then
      if whole : input.size = 128 * r then
        have nonzero : 0 < n := by simp [validCost, Bool.and_eq_true] at cost; omega
        .ok (romixCore r positive n nonzero ⟨input, whole⟩).val
      else .error (.invalidInputSize (BLOCK_SIZE * r) input.size)
    else .error (.invalidCost n)
  else .error (.invalidBlockSize r)

/-- Mix the `p` independent blocks in order, RFC 7914 §6, step 2. -/
def mixBlocks (input : ByteArray) (n r : Nat) :
    Nat → Nat → ByteArray → Except ScryptError ByteArray
  | 0, _, out => .ok out
  | count + 1, offset, out => do
    let mixed ← romix (input.extract offset (offset + 128 * r)) n r
    mixBlocks input n r count (offset + 128 * r) (out ++ mixed)

/-- Expand, mix and compress the password, RFC 7914 §6, with the output length in bytes. -/
def scrypt (password salt : ByteArray) (n r p length : Nat) : Except ScryptError ByteArray := do
  if r = 0 then throw (.invalidBlockSize r)
  if !validCost n r then throw (.invalidCost n)
  if p = 0 ∨ Pbkdf2.MAX_LENGTH < p * 128 * r then throw (.invalidParallelization p)
  if length = 0 then throw .emptyOutput
  if Pbkdf2.MAX_LENGTH < length then throw (.outputTooLong length)
  let expanded ← (Pbkdf2.pbkdf2 password salt 1 (p * 128 * r)).mapError ScryptError.pbkdf2
  let mixed ← mixBlocks expanded n r p 0 ByteArray.empty
  (Pbkdf2.pbkdf2 password mixed 1 length).mapError ScryptError.pbkdf2

end EthLib.Cryptography.Hash.Scrypt
