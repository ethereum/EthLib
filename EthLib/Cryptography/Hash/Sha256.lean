/-!
# `Sha256`

SHA-256, as FIPS 180-4 defines it, for messages of whole bytes.

Each step of the standard is one definition here:

```text
pad        §5.1.1   the message, a set bit, zeros, and the length in bits
schedule   §6.2.2   step 1: the sixty-four words of one block
round      §6.2.2   step 3: one of the sixty-four rounds
compress   §6.2.2   steps 2 to 4: one block absorbed into the hash value
digest     §6.2.2   the final hash value as thirty-two bytes
hash       §6.2     every block of the padded message, in order
```

Used by BLS hash-to-curve (`expand_message_xmd`), KZG's Fiat-Shamir challenges, and SSZ Merkleization.
None of them needs constant time, so this is written for clarity.
-/

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

Each is the first 32 bits of the fractional part of the cube root of one of the first sixty-four primes.
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

Each word is the first 32 bits of the fractional part of the square root of one of the first eight primes.
-/
def IV : Vector UInt32 8 := #v[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-! ## Padding -/

/-- The zero bytes between the `0x80` byte and the length, so that the padded message fills whole blocks. -/
def paddingZeros (size : Nat) : Nat := (64 - (size + 9) % 64) % 64

/--
The length of a message in bits, as eight big-endian bytes.

FIPS 180-4 §5.1.1 admits fewer than 2⁶⁴ bits, so the length of an admitted message fits in 64 bits.
-/
def lengthBytes (size : Nat) : ByteArray :=
  let bits : UInt64 := UInt64.ofNat size * 8
  ⟨Array.ofFn fun i : Fin 8 => (bits >>> (56 - 8 * UInt64.ofNat i.val)).toUInt8⟩

/--
The padded message, FIPS 180-4 §5.1.1: the message, a set bit, zeros, then its length in bits.

The message is whole bytes, so the set bit and the seven zero bits after it are the byte `0x80`.
-/
def pad (message : ByteArray) : ByteArray :=
  message.push 0x80 ++ ⟨Array.replicate (paddingZeros message.size) 0⟩ ++ lengthBytes message.size

/-! ## One block -/

/-- Four bytes from `start`, read as one big-endian word, FIPS 180-4 §3.1 and §5.2.1. -/
@[inline] def big32 (block : ByteArray) (start : Nat) : UInt32 :=
  block[start]!.toUInt32 <<< 24 ||| block[start + 1]!.toUInt32 <<< 16 |||
    block[start + 2]!.toUInt32 <<< 8 ||| block[start + 3]!.toUInt32

/-- The first `count` words of the message schedule, each computed from the ones before it. -/
def schedulePrefix (block : ByteArray) (start : Nat) : (count : Nat) → Vector UInt32 count
  | 0 => .emptyWithCapacity 64
  | t + 1 =>
    let W := schedulePrefix block start t
    let next := if early : t < 16 then big32 block (start + 4 * t)
      else W[t - 16]'(by omega) + smallSigma0 (W[t - 15]'(by omega)) + W[t - 7]'(by omega) +
        smallSigma1 (W[t - 2]'(by omega))
    W.push next

/--
The message schedule W₀ to W₆₃ of the block starting at byte `start`, FIPS 180-4 §6.2.2, step 1.

The first sixteen words are the block's, and each later word mixes four earlier ones.
-/
def schedule (block : ByteArray) (start : Nat) : Vector UInt32 64 := schedulePrefix block start 64

/-- One round on the working variables a to h, FIPS 180-4 §6.2.2, step 3. -/
@[inline] def round (state : Vector UInt32 8) (constant word : UInt32) : Vector UInt32 8 :=
  let a := state[0]
  let b := state[1]
  let c := state[2]
  let d := state[3]
  let e := state[4]
  let f := state[5]
  let g := state[6]
  let h := state[7]
  let t1 := h + bigSigma1 e + ch e f g + constant + word
  let t2 := bigSigma0 a + maj a b c
  #v[t1 + t2, a, b, c, d + t1, e, f, g]

/--
The hash value after one more block, FIPS 180-4 §6.2.2, steps 2 to 4.

The working variables start as the hash value, go through sixty-four rounds, and are added back to it.
-/
def compress (state : Vector UInt32 8) (block : ByteArray) (start : Nat) : Vector UInt32 8 :=
  let W := schedule block start
  let working := (List.finRange 64).foldl (fun current t => round current K[t] W[t]) state
  state.zipWith (· + ·) working

/-! ## The hash -/

/-- The final hash value as thirty-two bytes, each word big-endian, FIPS 180-4 §6.2.2. -/
def digest (state : Vector UInt32 8) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 32 => (state[i.val / 4]'(by omega) >>> (24 - 8 * UInt32.ofNat (i.val % 4))).toUInt8⟩

/-- SHA-256 of a message, FIPS 180-4 §6.2: every block of the padded message, in order, from the initial value. -/
def hash (message : ByteArray) : ByteArray :=
  let padded := pad message
  digest ((List.range (padded.size / 64)).foldl (fun state i => compress state padded (64 * i)) IV)

end EthLib.Cryptography.Hash.Sha256

namespace EthLib.Cryptography.Hash

/-- SHA-256 of an arbitrary-length `ByteArray`. -/
@[inline] def sha256 (data : ByteArray) : ByteArray := Sha256.hash data

end EthLib.Cryptography.Hash
