module

/-!
# SHA-256

SHA-256, as FIPS 180-4 defines it, for messages of whole bytes.

Each step of the standard is one definition, from the padding of §5.1.1 to the hash of §6.2.

BLS hash-to-curve, the Fiat-Shamir challenges of KZG and SSZ merkleization use it.

None of them needs constant time.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Sha256

/-! ## Words -/

/-- The size `w` of a word, in bits, FIPS 180-4 §1 and §2.2.1. -/
def WORD_BITS : UInt32 := 32

/-- Rotation right by `n` bits, ROTR of FIPS 180-4 §3.2. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  -- The word moved down by `n` bits, which drops its low `n` bits.
  (x >>> n) |||
  -- Those low `n` bits, moved up to the top of the word.
  (x <<< (WORD_BITS - n))

/-- Shift right by `n` bits, SHR of FIPS 180-4 §3.2. -/
@[inline] def shr (x : UInt32) (n : UInt32) : UInt32 := x >>> n

/-- Ch of FIPS 180-4 §4.1.2 (4.2): each bit of `y` where `x` is set, and of `z` where it is not. -/
@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- Maj of FIPS 180-4 §4.1.2 (4.3): each bit that at least two of the three words share. -/
@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ_0^{256} of FIPS 180-4 §4.1.2 (4.4). -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ_1^{256} of FIPS 180-4 §4.1.2 (4.5). -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ_0^{256} of FIPS 180-4 §4.1.2 (4.6). -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ shr x 3

/-- σ_1^{256} of FIPS 180-4 §4.1.2 (4.7). -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

/-! ## Constants -/

/--
The round constants K_0^{256} to K_63^{256}, FIPS 180-4 §4.2.2.

Each is the first 32 bits of the fractional part of the cube root of one of the first 64 primes.
-/
def K : Vector UInt32 64 := #v[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/--
The initial hash value H^(0), FIPS 180-4 §5.3.3.

Each is the first 32 bits of the fractional part of the square root of one of the first 8 primes.
-/
def IV : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-! ## Padding -/

/-- The size `m` of a message block, 512 bits, in bytes, FIPS 180-4 §1 and §2.2.1. -/
def BLOCK_SIZE_BYTES : Nat := 64

/-- The size of the block that holds the message length, 64 bits, in bytes, FIPS 180-4 §5.1.1. -/
def LENGTH_SIZE_BYTES : Nat := 8

/--
The zero bytes between the `0b10000000` byte and the length, so that the blocks are whole.

They are the fewest that bring the message, that byte, them and the length to whole blocks.
-/
def paddingZeros (size : Nat) : Nat :=
  (BLOCK_SIZE_BYTES - (size + 1 + LENGTH_SIZE_BYTES) % BLOCK_SIZE_BYTES) % BLOCK_SIZE_BYTES

/--
The length of a message in bits, as eight big-endian bytes.

FIPS 180-4 §5.1.1 admits fewer than 2^64 bits, so the length of an admitted message fits.
-/
def lengthBytes (size : Nat) : ByteArray :=
  let bits : UInt64 := UInt64.ofNat size * 8
  ⟨Array.ofFn fun i : Fin 8 => (bits >>> (56 - 8 * UInt64.ofNat i.val)).toUInt8⟩

/--
The padded message, FIPS 180-4 §5.1.1.

It has four parts, in order:

- The message itself, of `l` bits.
- The byte `0b10000000`: the bit 1, then seven zero bits, since `l` is a multiple of 8.
- The fewest zero bits that bring the size to 448 modulo 512.
- The 64-bit block that holds `l`, big-endian, which completes the last 512-bit block.
-/
def pad (message : ByteArray) : ByteArray :=
  message ++ ⟨#[0b10000000]⟩ ++ ⟨Array.replicate (paddingZeros message.size) 0⟩ ++
    lengthBytes message.size

/-! ## Words of four bytes -/

/--
Four bytes read as one big-endian word, FIPS 180-4 §3.1.

The first byte is the most significant.
-/
@[inline] def big32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  -- The first byte fills bits 31 to 24.
  b0.toUInt32 <<< 24 |||
  -- The second byte fills bits 23 to 16.
  b1.toUInt32 <<< 16 |||
  -- The third byte fills bits 15 to 8.
  b2.toUInt32 <<< 8 |||
  -- The last byte fills bits 7 to 0.
  b3.toUInt32

/-! ## One block

The words of the state and of the schedule are record fields. -/

/-- The eight words `a` to `h` of the working variables, or of a hash value. -/
structure State where
  (a b c d e f g h : UInt32)

/-- The initial hash value as a state. -/
def initial : State := ⟨IV[0], IV[1], IV[2], IV[3], IV[4], IV[5], IV[6], IV[7]⟩

/-- Sixteen consecutive words `W_t` to `W_(t+15)` of the message schedule. -/
structure Window where
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32)

/--
The first sixteen words of the schedule are those of the block, FIPS 180-4 §6.2.2, step 1.

The block is the `m / 8` bytes of `bytes` from `start`.

Word `j` of the block is its four bytes from `4j` on, read big-endian.
-/
def Window.ofBlock (bytes : ByteArray) (start : Nat)
    (whole : start + BLOCK_SIZE_BYTES ≤ bytes.size) :
    Window :=
  -- Word `j` is the bytes at `4j` to `4j + 3` of the block, the first one most significant.
  let word (j : Fin 16) : UInt32 :=
    -- Since `j` is at most 15, every index is below `start + 64`, so inside the array.
    big32 (bytes[start + 4 * j]'(by unfold BLOCK_SIZE_BYTES at whole; omega))
      (bytes[start + 4 * j + 1]'(by unfold BLOCK_SIZE_BYTES at whole; omega))
      (bytes[start + 4 * j + 2]'(by unfold BLOCK_SIZE_BYTES at whole; omega))
      (bytes[start + 4 * j + 3]'(by unfold BLOCK_SIZE_BYTES at whole; omega))
  -- The words `W_0` to `W_15`, in order.
  ⟨word 0, word 1, word 2, word 3, word 4, word 5, word 6, word 7,
    word 8, word 9, word 10, word 11, word 12, word 13, word 14, word 15⟩

/--
The schedule sixteen words later, FIPS 180-4 §6.2.2, step 1.

From the words `W_t` to `W_(t+15)`, it gives the words `W_(t+16)` to `W_(t+31)`.

The rounds use one window for sixteen rounds.
-/
def Window.next (w : Window) : Window :=
  -- Each new word is `W_u = W_(u-16) + σ_0^{256}(W_(u-15)) + W_(u-7) + σ_1^{256}(W_(u-2))`.
  --
  -- The later new words read the earlier new words, so they are computed in order.
  --
  -- `n_i` is `W_(t+16+i)`; an operand past `W_(t+15)` is an earlier `n`.
  let n0 := w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14
  let n1 := w.w1 + smallSigma0 w.w2 + w.w10 + smallSigma1 w.w15
  let n2 := w.w2 + smallSigma0 w.w3 + w.w11 + smallSigma1 n0
  let n3 := w.w3 + smallSigma0 w.w4 + w.w12 + smallSigma1 n1
  let n4 := w.w4 + smallSigma0 w.w5 + w.w13 + smallSigma1 n2
  let n5 := w.w5 + smallSigma0 w.w6 + w.w14 + smallSigma1 n3
  let n6 := w.w6 + smallSigma0 w.w7 + w.w15 + smallSigma1 n4
  let n7 := w.w7 + smallSigma0 w.w8 + n0 + smallSigma1 n5
  let n8 := w.w8 + smallSigma0 w.w9 + n1 + smallSigma1 n6
  let n9 := w.w9 + smallSigma0 w.w10 + n2 + smallSigma1 n7
  let n10 := w.w10 + smallSigma0 w.w11 + n3 + smallSigma1 n8
  let n11 := w.w11 + smallSigma0 w.w12 + n4 + smallSigma1 n9
  let n12 := w.w12 + smallSigma0 w.w13 + n5 + smallSigma1 n10
  let n13 := w.w13 + smallSigma0 w.w14 + n6 + smallSigma1 n11
  let n14 := w.w14 + smallSigma0 w.w15 + n7 + smallSigma1 n12
  let n15 := w.w15 + smallSigma0 n0 + n8 + smallSigma1 n13
  ⟨n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15⟩

/--
Round `t` on the working variables a to h, FIPS 180-4 §6.2.2, step 3.

It takes the constant `K_t^{256}` and the schedule word `W_t`, and adds modulo 2^32.
-/
@[inline] def round (s : State) (K_t W_t : UInt32) : State :=
  -- `T1 = h + Σ_1^{256}(e) + Ch(e, f, g) + K_t^{256} + W_t`.
  let T1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + K_t + W_t
  -- `T2 = Σ_0^{256}(a) + Maj(a, b, c)`.
  let T2 := bigSigma0 s.a + maj s.a s.b s.c
  -- `h = g`, `g = f`, `f = e`, `e = d + T1`, then `d = c`, `c = b`, `b = a`, `a = T1 + T2`.
  { h := s.g, g := s.f, f := s.e, e := s.d + T1, d := s.c, c := s.b, b := s.a, a := T1 + T2 }

/--
Rounds `t` to `t + 15` of FIPS 180-4 §6.2.2, step 3.

The window holds `W_t` to `W_(t+15)`, and round `t + j` takes `K_(t+j)^{256}` and `W_(t+j)`.
-/
@[inline] def rounds (s : State) (w : Window) (t : Nat) (inside : t + 16 ≤ 64) : State :=
  let s := round s (K[t + 0]'(by omega)) w.w0
  let s := round s (K[t + 1]'(by omega)) w.w1
  let s := round s (K[t + 2]'(by omega)) w.w2
  let s := round s (K[t + 3]'(by omega)) w.w3
  let s := round s (K[t + 4]'(by omega)) w.w4
  let s := round s (K[t + 5]'(by omega)) w.w5
  let s := round s (K[t + 6]'(by omega)) w.w6
  let s := round s (K[t + 7]'(by omega)) w.w7
  let s := round s (K[t + 8]'(by omega)) w.w8
  let s := round s (K[t + 9]'(by omega)) w.w9
  let s := round s (K[t + 10]'(by omega)) w.w10
  let s := round s (K[t + 11]'(by omega)) w.w11
  let s := round s (K[t + 12]'(by omega)) w.w12
  let s := round s (K[t + 13]'(by omega)) w.w13
  let s := round s (K[t + 14]'(by omega)) w.w14
  let s := round s (K[t + 15]'(by omega)) w.w15
  s

/--
The hash value `H^(i)` after the block `M^(i)`, FIPS 180-4 §6.2.2, steps 1 to 4.

The block is the `m / 8` bytes of `bytes` from `start`, and `H` is `H^(i-1)`.
-/
def compress (H : State) (bytes : ByteArray) (start : Nat)
    (whole : start + BLOCK_SIZE_BYTES ≤ bytes.size) :
    State :=
  -- Step 1: the schedule starts with the sixteen words of the block.
  --
  -- It is computed sixteen words at a time.
  let w0 := Window.ofBlock bytes start whole
  let w1 := w0.next
  let w2 := w1.next
  let w3 := w2.next
  -- Step 2: the working variables a to h are set to `H_0^(i-1)` to `H_7^(i-1)`.
  --
  -- Step 3: the 64 rounds run on them, sixteen on each window.
  let r := rounds (rounds (rounds (rounds H w0 0 (by omega)) w1 16 (by omega)) w2 32 (by omega))
    w3 48 (by omega)
  -- Step 4: `H_0^(i) = a + H_0^(i-1)`, and so on to `H_7^(i) = h + H_7^(i-1)`, modulo 2^32.
  --
  -- Each word of `H^(i)` is a working variable plus the same word of `H^(i-1)`.
  { a := r.a + H.a, b := r.b + H.b, c := r.c + H.c, d := r.d + H.d,
    e := r.e + H.e, f := r.f + H.f, g := r.g + H.g, h := r.h + H.h }

/--
The loop over the blocks of FIPS 180-4 §6.2.2: for `i` from 1 to `N`, `H^(i)` from `H^(i-1)`.

The blocks are the `count` blocks of `m / 8` bytes of `bytes` from `start`.

The step is the compression, which computes `H^(i)` from `H^(i-1)` and the block `M^(i)`.

It is an argument because, with the compression inside, the kernel overflows on the equations.
-/
def chain
    (step : State → (bytes : ByteArray) → (start : Nat) →
      start + BLOCK_SIZE_BYTES ≤ bytes.size → State)
    (bytes : ByteArray) :
    (count start : Nat) → start + BLOCK_SIZE_BYTES * count ≤ bytes.size → State → State
  -- No block is left, so the hash value is the last one computed.
  | 0, _, _, H => H
  | count + 1, start, whole, H =>
    -- The rest of the blocks start one block later, from `H^(i)`.
    chain step bytes count (start + BLOCK_SIZE_BYTES) (by rw [Nat.mul_succ] at whole; omega)
      -- The block `M^(i)` starts at `start`, and the compression gives `H^(i)` from `H^(i-1)`.
      (step H bytes start (by rw [Nat.mul_succ] at whole; omega))

/-! ## The hash -/

/-- The byte of a word that a right shift brings to the low eight bits. -/
@[inline] def byteAt (w : UInt32) (shift : UInt32) : UInt8 := (w >>> shift).toUInt8

/-- The size of a message digest, 256 bits, in bytes, FIPS 180-4 §1. -/
def DIGEST_SIZE_BYTES : Nat := 32

/--
The message digest `H_0^(N) ‖ H_1^(N) ‖ ... ‖ H_7^(N)`, FIPS 180-4 §6.2.2, as 32 bytes.

Each word is written big-endian, as FIPS 180-4 §3.1 does.
-/
def digest (H : State) : ByteArray :=
  -- One word per line, `H_0^(N)` to `H_7^(N)`, each most significant byte first.
  ⟨#[byteAt H.a 24, byteAt H.a 16, byteAt H.a 8, byteAt H.a 0,
    byteAt H.b 24, byteAt H.b 16, byteAt H.b 8, byteAt H.b 0,
    byteAt H.c 24, byteAt H.c 16, byteAt H.c 8, byteAt H.c 0,
    byteAt H.d 24, byteAt H.d 16, byteAt H.d 8, byteAt H.d 0,
    byteAt H.e 24, byteAt H.e 16, byteAt H.e 8, byteAt H.e 0,
    byteAt H.f 24, byteAt H.f 16, byteAt H.f 8, byteAt H.f 0,
    byteAt H.g 24, byteAt H.g 16, byteAt H.g 8, byteAt H.g 0,
    byteAt H.h 24, byteAt H.h 16, byteAt H.h 8, byteAt H.h 0]⟩

/--
SHA-256 of a message, FIPS 180-4 §6.2.
-/
def hash (message : ByteArray) : ByteArray :=
  -- §6.2.1: the message is padded (§5.1.1) and parsed into `N` blocks of `m / 8` bytes (§5.2.1).
  --
  -- The padded message is whole blocks.
  --
  -- It is a byte array, and each block is read at its offset, with no copy.
  let padded := pad message
  -- §6.2.1: the hash value starts as `H^(0)` (§5.3.3).
  --
  -- §6.2.2: for `i` from 1 to `N`, the compression of the block `M^(i)` gives `H^(i)`.
  --
  -- §6.2.2: the message digest is `H^(N)`, as bytes.
  --
  -- All `N` blocks from `H^(0)`, then the digest of `H^(N)`.
  digest (chain compress padded (padded.size / BLOCK_SIZE_BYTES) 0
    (by have := Nat.mul_div_le padded.size BLOCK_SIZE_BYTES; omega) initial)

/-- SHA-256 of a message, as its 32 bytes. -/
def hash32 (message : ByteArray) : Vector UInt8 32 :=
  ⟨(hash message).data, by simp [hash, digest]⟩

end EthLib.Cryptography.Hash.Sha256

namespace EthLib.Cryptography.Hash

/--
SHA-256 of a byte string shorter than 2^61 bytes, the bound of FIPS 180-4 §1.

A longer input wraps its bit length modulo 2^64, and the result is not SHA-256.
-/
@[inline] def sha256 (data : ByteArray) : ByteArray := Sha256.hash data

end EthLib.Cryptography.Hash
