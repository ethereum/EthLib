module

/-!
# SHA-256

SHA-256, as FIPS 180-4 defines it, for messages of whole bytes.

Each step of the standard is one definition, from the padding of §5.1.1 to the hash of §6.2.

The words of the state and of the schedule are record fields, and the message is a list.

So the kernel evaluates the hash in time linear in the message.

BLS hash-to-curve, the Fiat-Shamir challenges of KZG and SSZ merkleization use it.

None of them needs constant time.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Sha256

/-! ## Words -/

/-- Rotation right by `n` bits, ROTR of FIPS 180-4 §3.2. -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Shift right by `n` bits, SHR of FIPS 180-4 §3.2. -/
@[inline] def shr (x : UInt32) (n : UInt32) : UInt32 := x >>> n

/-- Ch of FIPS 180-4 §4.1.2 (4.2): each bit of `y` where `x` is set, and of `z` where it is not. -/
@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)

/-- Maj of FIPS 180-4 §4.1.2 (4.3): each bit that at least two of the three words share. -/
@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- Σ0 of FIPS 180-4 §4.1.2 (4.4). -/
@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22

/-- Σ1 of FIPS 180-4 §4.1.2 (4.5). -/
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25

/-- σ0 of FIPS 180-4 §4.1.2 (4.6). -/
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ shr x 3

/-- σ1 of FIPS 180-4 §4.1.2 (4.7). -/
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ shr x 10

/-! ## Constants -/

/--
The round constants K₀ to K₆₃, FIPS 180-4 §4.2.2.

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
The initial hash value H⁽⁰⁾, FIPS 180-4 §5.3.3.

Each is the first 32 bits of the fractional part of the square root of one of the first 8 primes.
-/
def IV : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-! ## Padding -/

/-- The zero bytes between the `0x80` byte and the length, so that the blocks are whole. -/
def paddingZeros (size : Nat) : Nat := (64 - (size + 9) % 64) % 64

/--
The length of a message in bits, as eight big-endian bytes.

FIPS 180-4 §5.1.1 admits fewer than 2⁶⁴ bits, so the length of an admitted message fits.
-/
def lengthBytes (size : Nat) : ByteArray :=
  let bits : UInt64 := UInt64.ofNat size * 8
  ⟨Array.ofFn fun i : Fin 8 => (bits >>> (56 - 8 * UInt64.ofNat i.val)).toUInt8⟩

/--
The padded message, FIPS 180-4 §5.1.1: the message, a set bit, zeros, then its length in bits.

The message is whole bytes, so the set bit and the seven zero bits after it are the byte `0x80`.
-/
def pad (message : ByteArray) : List UInt8 :=
  message.data.toList ++ 0x80 :: List.replicate (paddingZeros message.size) 0 ++
    (lengthBytes message.size).data.toList

/-! ## Parsing -/

/-- Four bytes read as one big-endian word, FIPS 180-4 §3.1. -/
@[inline] def big32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 <<< 24 ||| b1.toUInt32 <<< 16 ||| b2.toUInt32 <<< 8 ||| b3.toUInt32

/-- Bytes as 32-bit words, four bytes each, FIPS 180-4 §5.2.1. -/
def words : List UInt8 → List UInt32
  | b0 :: b1 :: b2 :: b3 :: rest => big32 b0 b1 b2 b3 :: words rest
  | _ => []

/-! ## One block -/

/-- The eight words `a` to `h` of the working variables, or of a hash value. -/
structure State where
  (a b c d e f g h : UInt32)

/-- The initial hash value as a state. -/
def initial : State := ⟨IV[0], IV[1], IV[2], IV[3], IV[4], IV[5], IV[6], IV[7]⟩

/-- Sixteen consecutive words `W_t` to `W_(t+15)` of the message schedule. -/
structure Window where
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : UInt32)

/-- The first sixteen words of the schedule are the block's, FIPS 180-4 §6.2.2, step 1. -/
def Window.ofWords (block : List UInt32) : Window :=
  ⟨block[0]!, block[1]!, block[2]!, block[3]!, block[4]!, block[5]!, block[6]!, block[7]!,
    block[8]!, block[9]!, block[10]!, block[11]!, block[12]!, block[13]!, block[14]!, block[15]!⟩

/--
The schedule one word later, FIPS 180-4 §6.2.2, step 1.

The new last word is `W_(t+16) = W_t + σ0(W_(t+1)) + W_(t+9) + σ1(W_(t+14))`.
-/
def Window.next (w : Window) : Window :=
  ⟨w.w1, w.w2, w.w3, w.w4, w.w5, w.w6, w.w7, w.w8, w.w9, w.w10, w.w11, w.w12, w.w13, w.w14, w.w15,
    w.w0 + smallSigma0 w.w1 + w.w9 + smallSigma1 w.w14⟩

/-- One round on the working variables a to h, FIPS 180-4 §6.2.2, step 3. -/
@[inline] def round (s : State) (constant word : UInt32) : State :=
  let t1 := s.h + bigSigma1 s.e + ch s.e s.f s.g + constant + word
  let t2 := bigSigma0 s.a + maj s.a s.b s.c
  ⟨t1 + t2, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

/-- One round per constant, each with the first word of the schedule, which then moves on. -/
def rounds : List UInt32 → Window → State → State
  | [], _, s => s
  | constant :: rest, w, s => rounds rest w.next (round s constant w.w0)

/--
The hash value after one more block, FIPS 180-4 §6.2.2, steps 2 to 4.

The working variables start as the hash value, go through the rounds, and are added back to it.
-/
def compress (s : State) (block : List UInt8) : State :=
  let r := rounds K.toList (Window.ofWords (words (block.take 64))) s
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

/--
The hash value after the first blocks of 64 bytes, each absorbed by one step.

The step is an argument: with the compression inside, the kernel overflows on the equations.
-/
def chain (step : State → List UInt8 → State) : (count : Nat) → List UInt8 → State → State
  | 0, _, s => s
  | count + 1, block, s => chain step count (block.drop 64) (step s block)

/-! ## The hash -/

/-- One word as four big-endian bytes, FIPS 180-4 §3.1. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- The final hash value as thirty-two bytes, each word big-endian, FIPS 180-4 §6.2.2. -/
def digest (s : State) : ByteArray :=
  ⟨(wordBytes s.a ++ wordBytes s.b ++ wordBytes s.c ++ wordBytes s.d ++
    wordBytes s.e ++ wordBytes s.f ++ wordBytes s.g ++ wordBytes s.h).toArray⟩

/-- SHA-256 of a message, FIPS 180-4 §6.2: every block of the padded message, in order. -/
def hash (message : ByteArray) : ByteArray :=
  let padded := pad message
  digest (chain compress (padded.length / 64) padded initial)

end EthLib.Cryptography.Hash.Sha256

namespace EthLib.Cryptography.Hash

/-- SHA-256 of a byte string of any length. -/
@[inline] def sha256 (data : ByteArray) : ByteArray := Sha256.hash data

end EthLib.Cryptography.Hash
