/-!
# `Ripemd160`

RIPEMD-160, as Dobbertin, Bosselaers and Preneel define it in "RIPEMD-160: A strengthened version of RIPEMD" (FSE 1996), for messages of whole bytes.

The names below follow the authors' pseudo-code, `rmd160.txt` on Bosselaers' RIPEMD-160 page.
Its sections are named `definitions` and `pseudo-code`.

```text
pad        padding is identical to that of MD4 (RFC 1320 §3.1 and §3.2)
f          definitions: the five nonlinear functions
K, K'      definitions: the added constants of the left and the right line
r, r'      definitions: the message word each step reads
s, s'      definitions: the amount each step rotates by
IV         definitions: the initial value
line       pseudo-code: the eighty steps of one line
compress   pseudo-code: one block absorbed into the chaining variable
digest     the final chaining variable as twenty bytes
hash       every block of the padded message, in order
```

Words are little-endian, unlike SHA-256: the message words, the length and the digest all put the least significant byte first.

Used by the precompile at address `0x03`, which returns the digest left-padded to 32 bytes.
This specification makes no constant-time guarantee.
-/

namespace EthLib.Cryptography.Hash.Ripemd160

/-! ## Words -/

/-- Rotate left by `n` bits, `rol_n` of the pseudo-code. `n` is between 1 and 31. -/
@[inline] def rol (x : UInt32) (n : UInt32) : UInt32 :=
  (x <<< n) ||| (x >>> (32 - n))

/--
The nonlinear function `f(j, x, y, z)` of the group of sixteen steps `group = j / 16`.

```text
    group   f(j, x, y, z)
      0     x XOR y XOR z
      1     (x AND y) OR (NOT(x) AND z)
      2     (x OR NOT(y)) XOR z
      3     (x AND z) OR (y AND NOT(z))
      4     x XOR (y OR NOT(z))
```
-/
@[inline] def f (group : Fin 5) (x y z : UInt32) : UInt32 :=
  match group with
  | 0 => x ^^^ y ^^^ z
  | 1 => (x &&& y) ||| ((~~~x) &&& z)
  | 2 => (x ||| ~~~y) ^^^ z
  | 3 => (x &&& z) ||| (y &&& ~~~z)
  | 4 => x ^^^ (y ||| ~~~z)

/-! ## Constants -/

/--
The added constants `K(j)` of the left line, one per group of sixteen steps.

For the last four groups, each is `int(2^30 * sqrt(p))` for p = 2, 3, 5, 7.
-/
def K : Vector UInt32 5 := #v[0x00000000, 0x5A827999, 0x6ED9EBA1, 0x8F1BBCDC, 0xA953FD4E]

/--
The added constants `K'(j)` of the right line, one per group of sixteen steps.

For the first four groups, each is `int(2^30 * cbrt(p))` for p = 2, 3, 5, 7.
-/
def K' : Vector UInt32 5 := #v[0x50A28BE6, 0x5C4DD124, 0x6D703EF3, 0x7A6D76E9, 0x00000000]

/-- The index of the message word the left line reads at each of its eighty steps, `r(j)`. -/
def r : Vector (Fin 16) 80 := #v[
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
  7, 4, 13, 1, 10, 6, 15, 3, 12, 0, 9, 5, 2, 14, 11, 8,
  3, 10, 14, 4, 9, 15, 8, 1, 2, 7, 0, 6, 13, 11, 5, 12,
  1, 9, 11, 10, 0, 8, 12, 4, 13, 3, 7, 15, 14, 5, 6, 2,
  4, 0, 5, 9, 7, 12, 2, 10, 14, 1, 3, 8, 11, 6, 15, 13 ]

/-- The index of the message word the right line reads at each of its eighty steps, `r'(j)`. -/
def r' : Vector (Fin 16) 80 := #v[
  5, 14, 7, 0, 9, 2, 11, 4, 13, 6, 15, 8, 1, 10, 3, 12,
  6, 11, 3, 7, 0, 13, 5, 10, 14, 15, 8, 12, 4, 9, 1, 2,
  15, 5, 1, 3, 7, 14, 6, 9, 11, 8, 12, 2, 10, 0, 4, 13,
  8, 6, 4, 1, 3, 11, 15, 0, 5, 12, 2, 13, 9, 7, 10, 14,
  12, 15, 10, 4, 1, 5, 8, 7, 6, 2, 13, 14, 0, 3, 9, 11 ]

/-- The number of bits the left line rotates by at each of its eighty steps, `s(j)`. -/
def s : Vector UInt32 80 := #v[
  11, 14, 15, 12, 5, 8, 7, 9, 11, 13, 14, 15, 6, 7, 9, 8,
  7, 6, 8, 13, 11, 9, 7, 15, 7, 12, 15, 9, 11, 7, 13, 12,
  11, 13, 6, 7, 14, 9, 13, 15, 14, 8, 13, 6, 5, 12, 7, 5,
  11, 12, 14, 15, 14, 15, 9, 8, 9, 14, 5, 6, 8, 6, 5, 12,
  9, 15, 5, 11, 6, 8, 13, 12, 5, 12, 13, 14, 11, 8, 5, 6 ]

/-- The number of bits the right line rotates by at each of its eighty steps, `s'(j)`. -/
def s' : Vector UInt32 80 := #v[
  8, 9, 9, 11, 13, 15, 15, 5, 7, 7, 8, 11, 14, 14, 12, 6,
  9, 13, 15, 7, 12, 8, 9, 11, 7, 7, 12, 7, 6, 15, 13, 11,
  9, 7, 15, 11, 8, 6, 6, 14, 12, 13, 5, 14, 13, 13, 7, 5,
  15, 5, 8, 11, 14, 14, 6, 14, 6, 9, 12, 9, 12, 5, 15, 8,
  8, 5, 12, 9, 12, 5, 14, 6, 8, 13, 6, 5, 15, 13, 11, 11 ]

/-- The initial value h0 to h4 of the chaining variable. -/
def IV : Vector UInt32 5 := #v[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0]

/-! ## Padding -/

/-- The zero bytes between the `0x80` byte and the length, so that the padded message fills whole blocks. -/
def paddingZeros (size : Nat) : Nat := (64 - (size + 9) % 64) % 64

/--
The length of a message in bits, as eight little-endian bytes.

RFC 1320 section 3.2 appends the low 64 bits of the bit length.
The conversion and multiplication below implement that reduction modulo 2^64.
-/
def lengthBytes (size : Nat) : ByteArray :=
  let bits : UInt64 := UInt64.ofNat size * 8
  ⟨Array.ofFn fun i : Fin 8 => (bits >>> (8 * UInt64.ofNat i.val)).toUInt8⟩

/--
The padded message: the message, a set bit, zeros, then its length in bits.

The message is whole bytes, so the set bit and the seven zero bits after it are the byte `0x80`.
-/
def pad (message : ByteArray) : ByteArray :=
  message.push 0x80 ++ ⟨Array.replicate (paddingZeros message.size) 0⟩ ++ lengthBytes message.size

/-! ## One block -/

/-- Four bytes from `start`, read as one little-endian word, `X[i][j]` of the pseudo-code. -/
@[inline] def little32 (block : ByteArray) (start : Nat) : UInt32 :=
  block[start]!.toUInt32 ||| block[start + 1]!.toUInt32 <<< 8 |||
    block[start + 2]!.toUInt32 <<< 16 ||| block[start + 3]!.toUInt32 <<< 24

/--
One step of a line on the variables (A, B, C, D, E).

```text
    T := rol_s(A + f(B, C, D) + X + K) + E
    (A, B, C, D, E) := (E, T, B, rol_10(C), D)
```
-/
@[inline] def step (group : Fin 5) (state : Vector UInt32 5) (word constant amount : UInt32) :
    Vector UInt32 5 :=
  let T := rol (state[0] + f group state[1] state[2] state[3] + word + constant) amount + state[4]
  #v[state[4], T, state[1], rol state[2] 10, state[3]]

/-- One line of eighty steps. `index` and `rotation` are the line's `r` and `s`, `constants` its `K`, and `reversed` says whether `f` runs backwards. -/
def line (X : Vector UInt32 16) (start : Vector UInt32 5) (constants : Vector UInt32 5)
    (index : Vector (Fin 16) 80) (rotation : Vector UInt32 80) (reversed : Bool) : Vector UInt32 5 :=
  (List.finRange 80).foldl
    (fun state j =>
      -- The left line uses f(j), the right line f(79 - j); the constant changes every sixteen steps.
      let group : Fin 5 := if reversed then ⟨4 - j.val / 16, by omega⟩ else ⟨j.val / 16, by omega⟩
      step group state X[index[j]] constants[(⟨j.val / 16, by omega⟩ : Fin 5)] rotation[j])
    start

/--
The chaining variable after one more block.

Both lines start from the chaining variable.
Their results are mixed with it in a rotated order:

```text
    T := h1 + C + D';  h1 := h2 + D + E';  h2 := h3 + E + A';
    h3 := h4 + A + B';  h4 := h0 + B + C';  h0 := T
```
-/
def compress (h : Vector UInt32 5) (block : ByteArray) (start : Nat) : Vector UInt32 5 :=
  let X : Vector UInt32 16 := Vector.ofFn fun j => little32 block (start + 4 * j.val)
  let left := line X h K r s false
  let right := line X h K' r' s' true
  #v[h[1] + left[2] + right[3], h[2] + left[3] + right[4], h[3] + left[4] + right[0],
    h[4] + left[0] + right[1], h[0] + left[1] + right[2]]

/-! ## The hash -/

/-- The final chaining variable as twenty bytes, each word little-endian. -/
def digest (state : Vector UInt32 5) : ByteArray :=
  ⟨Array.ofFn fun i : Fin 20 => (state[i.val / 4]'(by omega) >>> (8 * UInt32.ofNat (i.val % 4))).toUInt8⟩

/-- RIPEMD-160 of a message: every block of the padded message, in order, from the initial value. -/
def hash (message : ByteArray) : ByteArray :=
  let padded := pad message
  digest ((List.range (padded.size / 64)).foldl (fun state i => compress state padded (64 * i)) IV)

end EthLib.Cryptography.Hash.Ripemd160

namespace EthLib.Cryptography.Hash

/-- RIPEMD-160 of an arbitrary-length `ByteArray`. -/
@[inline] def ripemd160 (data : ByteArray) : ByteArray := Ripemd160.hash data

end EthLib.Cryptography.Hash
