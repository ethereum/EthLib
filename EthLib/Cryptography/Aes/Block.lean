module

/-!
# `Aes.Block`

The AES block cipher of [FIPS 197-upd1](https://doi.org/10.6028/NIST.FIPS.197-upd1).

It covers AES-128 and AES-256, and each step of the standard is one definition.

The key is secret, and nothing here is constant-time: the S-box lookup reads secret bytes.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-! ## The finite field GF(2^8)

FIPS 197 §4 reads a byte `{b7 ... b0}` as the polynomial `b7 x^7 + ... + b0` over GF(2).

Addition is XOR (§4.1).

Multiplication reduces the product modulo `m(x) = x^8 + x^4 + x^3 + x + 1` (§4.2). -/

/-- XTIMES of FIPS 197 §4.2 (4.5): the product of a byte with `{02}`, that is with `x`.

The left shift multiplies by `x`.

When `b7` is set, the shift drops `x^8`.

Adding `{1b}` puts back its remainder `x^4 + x^3 + x + 1`. -/
def xtimes (b : UInt8) : UInt8 :=
  if b &&& 0x80 = 0 then b <<< 1 else (b <<< 1) ^^^ 0x1b

/-- The sum of `b • x^i` over the bits `i` of `c` below `n`, from bit 0 up.

The argument `b` holds `b • x^i` at step `i`, as the table of FIPS 197 §4.2 (4.6) builds it. -/
def mulAux : Nat → UInt8 → UInt8 → UInt8
  | 0, _, _ => 0
  | n + 1, b, c => (if c &&& 1 = 0 then 0 else b) ^^^ mulAux n (xtimes b) (c >>> 1)

/-- The product `b • c` in GF(2^8), as FIPS 197 §4.2 (4.7) computes it.

The byte `c` is a sum of powers `x^i`, one per set bit.

So `b • c` is the sum of the matching `b • x^i`. -/
def mul (b c : UInt8) : UInt8 :=
  mulAux 8 b c

/-! ## The S-box

FIPS 197 §5.1.1 defines the S-box by an algorithm and prints its values in Table 4.

The cipher reads the table.

A theorem proves each entry equal to the algorithm, so no entry is taken on trust. -/

namespace Internal

/-- The multiplicative inverse `b^-1 = b^254` of FIPS 197 §4.4 (4.11), for `b ≠ {00}`.

Square-and-multiply runs over the bits of 254, which is `11111110` in binary.

Each step squares, then multiplies by `b` when the next bit is set. -/
def inv (b : UInt8) : UInt8 :=
  [true, true, true, true, true, true, true, false].foldl
    (fun acc bit => if bit then mul (mul acc acc) b else mul acc acc) 1

/-- Bit `i mod 8` of a byte, as the byte `0` or `1`. -/
def bit (b : UInt8) (i : Nat) : UInt8 :=
  (b >>> (i % 8).toUInt8) &&& 1

/-- The affine transformation of FIPS 197 §5.1.1 (5.3), with `c = {63}`:

```text
    b'_i = b_i ^ b_(i+4) ^ b_(i+5) ^ b_(i+6) ^ b_(i+7) ^ c_i     indices mod 8
```
-/
def affine (b : UInt8) : UInt8 :=
  (List.range 8).foldl
    (fun acc i =>
      acc ||| ((bit b i ^^^ bit b (i + 4) ^^^ bit b (i + 5) ^^^ bit b (i + 6) ^^^ bit b (i + 7) ^^^
        bit 0x63 i) <<< i.toUInt8))
    0

/-- SBOX of FIPS 197 §5.1.1: the inverse of (5.2), `{00}` to `{00}`, then the affine map. -/
def sbox (b : UInt8) : UInt8 :=
  affine (if b = 0 then 0 else inv b)

end Internal

-- A literal of 256 entries nests deeper than the default limit.
set_option maxRecDepth 2048 in
/-- Table 4 of FIPS 197, with the S-box of byte `b` at index `b`.

A theorem proves each entry equal to the algorithm of §5.1.1. -/
def SBOX : Vector UInt8 256 := #v[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16]

set_option maxRecDepth 2048 in
/-- Table 6 of FIPS 197, with the inverse S-box of byte `b` at index `b`.

§5.3.2 derives it from Table 4 by swapping inputs and outputs.

A theorem proves that the two tables invert each other. -/
def INV_SBOX : Vector UInt8 256 := #v[
  0x52, 0x09, 0x6a, 0xd5, 0x30, 0x36, 0xa5, 0x38, 0xbf, 0x40, 0xa3, 0x9e, 0x81, 0xf3, 0xd7, 0xfb,
  0x7c, 0xe3, 0x39, 0x82, 0x9b, 0x2f, 0xff, 0x87, 0x34, 0x8e, 0x43, 0x44, 0xc4, 0xde, 0xe9, 0xcb,
  0x54, 0x7b, 0x94, 0x32, 0xa6, 0xc2, 0x23, 0x3d, 0xee, 0x4c, 0x95, 0x0b, 0x42, 0xfa, 0xc3, 0x4e,
  0x08, 0x2e, 0xa1, 0x66, 0x28, 0xd9, 0x24, 0xb2, 0x76, 0x5b, 0xa2, 0x49, 0x6d, 0x8b, 0xd1, 0x25,
  0x72, 0xf8, 0xf6, 0x64, 0x86, 0x68, 0x98, 0x16, 0xd4, 0xa4, 0x5c, 0xcc, 0x5d, 0x65, 0xb6, 0x92,
  0x6c, 0x70, 0x48, 0x50, 0xfd, 0xed, 0xb9, 0xda, 0x5e, 0x15, 0x46, 0x57, 0xa7, 0x8d, 0x9d, 0x84,
  0x90, 0xd8, 0xab, 0x00, 0x8c, 0xbc, 0xd3, 0x0a, 0xf7, 0xe4, 0x58, 0x05, 0xb8, 0xb3, 0x45, 0x06,
  0xd0, 0x2c, 0x1e, 0x8f, 0xca, 0x3f, 0x0f, 0x02, 0xc1, 0xaf, 0xbd, 0x03, 0x01, 0x13, 0x8a, 0x6b,
  0x3a, 0x91, 0x11, 0x41, 0x4f, 0x67, 0xdc, 0xea, 0x97, 0xf2, 0xcf, 0xce, 0xf0, 0xb4, 0xe6, 0x73,
  0x96, 0xac, 0x74, 0x22, 0xe7, 0xad, 0x35, 0x85, 0xe2, 0xf9, 0x37, 0xe8, 0x1c, 0x75, 0xdf, 0x6e,
  0x47, 0xf1, 0x1a, 0x71, 0x1d, 0x29, 0xc5, 0x89, 0x6f, 0xb7, 0x62, 0x0e, 0xaa, 0x18, 0xbe, 0x1b,
  0xfc, 0x56, 0x3e, 0x4b, 0xc6, 0xd2, 0x79, 0x20, 0x9a, 0xdb, 0xc0, 0xfe, 0x78, 0xcd, 0x5a, 0xf4,
  0x1f, 0xdd, 0xa8, 0x33, 0x88, 0x07, 0xc7, 0x31, 0xb1, 0x12, 0x10, 0x59, 0x27, 0x80, 0xec, 0x5f,
  0x60, 0x51, 0x7f, 0xa9, 0x19, 0xb5, 0x4a, 0x0d, 0x2d, 0xe5, 0x7a, 0x9f, 0x93, 0xc9, 0x9c, 0xef,
  0xa0, 0xe0, 0x3b, 0x4d, 0xae, 0x2a, 0xf5, 0xb0, 0xc8, 0xeb, 0xbb, 0x3c, 0x83, 0x53, 0x99, 0x61,
  0x17, 0x2b, 0x04, 0x7e, 0xba, 0x77, 0xd6, 0x26, 0xe1, 0x69, 0x14, 0x63, 0x55, 0x21, 0x0c, 0x7d]

/-- SBOX of FIPS 197 §5.1.1, read from Table 4. -/
@[inline] def sbox (b : UInt8) : UInt8 :=
  SBOX[b.toNat]'b.toNat_lt

/-- INVSBOX of FIPS 197 §5.3.2, read from Table 6. -/
@[inline] def invSbox (b : UInt8) : UInt8 :=
  INV_SBOX[b.toNat]'b.toNat_lt

/-! ## The state

A block is 16 bytes `in_0 ... in_15`, and a word is 4 bytes (FIPS 197 §3.1 and §3.5).

The state is a 4 x 4 array of bytes, with `s[r, c] = in[r + 4c]` (§3.4, (3.6)).

So the state is the block itself, with byte `s[r, c]` at index `r + 4c`.

Column `c` is then bytes `4c` to `4c + 3`. -/

/-- A block of 128 bits, as 16 bytes. -/
abbrev Block := Vector UInt8 16

/-- A word of 32 bits, as 4 bytes. -/
abbrev Word := Vector UInt8 4

/-! ## The transformations of the cipher -/

/-- SUBBYTES of FIPS 197 §5.1.1: the S-box on each byte of the state. -/
def subBytes (s : Block) : Block :=
  s.map sbox

/-- SHIFTROWS of FIPS 197 §5.1.2 (5.5): `s'[r, c] = s[r, (c + r) mod 4]`. -/
def shiftRows (s : Block) : Block :=
  -- Index `i` holds `s'[r, c]` with `r = i mod 4` and `c = i / 4`.
  Vector.ofFn fun i => s[i.val % 4 + 4 * ((i.val / 4 + i.val % 4) % 4)]'(by omega)

/-- Multiplication of a word by the fixed matrix of `[a0, a1, a2, a3]`, FIPS 197 §4.3 (4.8). -/
def mulWord (a b : Word) : Word := #v[
  mul a[0] b[0] ^^^ mul a[3] b[1] ^^^ mul a[2] b[2] ^^^ mul a[1] b[3],
  mul a[1] b[0] ^^^ mul a[0] b[1] ^^^ mul a[3] b[2] ^^^ mul a[2] b[3],
  mul a[2] b[0] ^^^ mul a[1] b[1] ^^^ mul a[0] b[2] ^^^ mul a[3] b[3],
  mul a[3] b[0] ^^^ mul a[2] b[1] ^^^ mul a[1] b[2] ^^^ mul a[0] b[3]]

/-- Column `c` of the state, the word `[s[0, c], s[1, c], s[2, c], s[3, c]]` of FIPS 197 (3.8). -/
def column (s : Block) (c : Fin 4) : Word :=
  Vector.ofFn fun r => s[r.val + 4 * c.val]'(by omega)

/-- Each column of the state multiplied by the fixed matrix of `a`. -/
def mixColumnsWith (a : Word) (s : Block) : Block :=
  -- The matrix acts on each column alone, so the four rows of a column share one product.
  let columns : Vector Word 4 := Vector.ofFn fun c => mulWord a (column s c)
  -- Byte `s'[r, c]` at index `i` is row `r = i mod 4` of the product of column `c = i / 4`.
  Vector.ofFn fun i => (columns[i.val / 4]'(by omega))[i.val % 4]'(by omega)

/-- MIXCOLUMNS of FIPS 197 §5.1.3, with the word `[{02}, {01}, {01}, {03}]` of (5.6). -/
def mixColumns (s : Block) : Block :=
  mixColumnsWith #v[0x02, 0x01, 0x01, 0x03] s

/-- ADDROUNDKEY of FIPS 197 §5.1.4 (5.9): the state XOR the round key.

The round key is the words `w[4 round .. 4 round + 3]`, laid out as the state. -/
def addRoundKey (s roundKey : Block) : Block :=
  Vector.zipWith (· ^^^ ·) s roundKey

/-! ## The transformations of the inverse cipher -/

/-- INVSHIFTROWS of FIPS 197 §5.3.1 (5.12): `s'[r, c] = s[r, (c - r) mod 4]`.

Since `r < 4`, `(c - r) mod 4` is `(c + 4 - r) mod 4` in natural numbers. -/
def invShiftRows (s : Block) : Block :=
  Vector.ofFn fun i => s[i.val % 4 + 4 * ((i.val / 4 + 4 - i.val % 4) % 4)]'(by omega)

/-- INVSUBBYTES of FIPS 197 §5.3.2: the inverse S-box on each byte of the state. -/
def invSubBytes (s : Block) : Block :=
  s.map invSbox

/-- INVMIXCOLUMNS of FIPS 197 §5.3.3, with the word `[{0e}, {09}, {0d}, {0b}]` of (5.13). -/
def invMixColumns (s : Block) : Block :=
  mixColumnsWith #v[0x0e, 0x09, 0x0d, 0x0b] s

/-! ## The key expansion -/

/-- The word XOR of FIPS 197 §5.1.4, byte by byte. -/
def xorWord (a b : Word) : Word :=
  Vector.zipWith (· ^^^ ·) a b

/-- ROTWORD of FIPS 197 §5.2 (5.10): `[a0, a1, a2, a3]` to `[a1, a2, a3, a0]`. -/
def rotWord (a : Word) : Word :=
  #v[a[1], a[2], a[3], a[0]]

/-- SUBWORD of FIPS 197 §5.2 (5.11): the S-box on each byte of a word. -/
def subWord (a : Word) : Word :=
  a.map sbox

/-- The round constant `Rcon[j] = [x^(j-1), {00}, {00}, {00}]` of FIPS 197 §5.2.

Its first byte is XTIMES applied `j - 1` times to `{01}`, as §5.2 notes below Table 5.

A theorem checks the ten values of Table 5. -/
def rcon (j : Nat) : Word :=
  #v[Nat.repeat xtimes (j - 1) 1, 0, 0, 0]

/-- Word `w[i]` of the key schedule from `w[i - 1]` and `w[i - Nk]`.

It is lines 8 to 14 of FIPS 197 §5.2, Algorithm 2. -/
def nextWord (Nk i : Nat) (prev back : Word) : Word :=
  let temp :=
    if i % Nk = 0 then xorWord (subWord (rotWord prev)) (rcon (i / Nk))
    else if Nk > 6 ∧ i % Nk = 4 then subWord prev
    else prev
  xorWord back temp

/-- KEYEXPANSION of FIPS 197 §5.2, Algorithm 2: the key schedule `w[0 .. 4 Nr + 3]`.

The first `Nk` words are the key itself.

Each later word comes from the word before it and the word `Nk` places before it. -/
def keyExpansion (Nk Nr : Nat) (key : Vector UInt8 (4 * Nk)) : Vector Word (4 * (Nr + 1)) :=
  -- Lines 2 to 6: word `i` of the key is bytes `4i` to `4i + 3`.
  let init : Array Word :=
    Array.ofFn fun i : Fin Nk => Vector.ofFn fun j : Fin 4 => key[4 * i.val + j.val]'(by omega)
  -- Lines 7 to 16: word `i` is computed from an array that holds `w[0 .. i - 1]`.
  -- So both reads are in bounds, and the default is never read.
  let w := (List.range' Nk (4 * (Nr + 1) - Nk)).foldl
    (fun w i => w.push (nextWord Nk i (w.getD (i - 1) default) (w.getD (i - Nk) default))) init
  -- The array has `4 (Nr + 1)` words when `Nk ≤ 4 (Nr + 1)`, as for both key sizes.
  Vector.ofFn fun i => w.getD i.val default

/-- The round key of round `round`: the words `w[4 round .. 4 round + 3]`, laid out as the state. -/
def roundKey {Nr : Nat} (w : Vector Word (4 * (Nr + 1))) (round : Nat) (h : round ≤ Nr) : Block :=
  Vector.ofFn fun i => (w[4 * round + i.val / 4]'(by omega))[i.val % 4]'(by omega)

/-! ## The cipher and its inverse -/

/-- One middle round of CIPHER, lines 5 to 8 of FIPS 197 §5.1, Algorithm 1. -/
def round (s roundKey : Block) : Block :=
  addRoundKey (mixColumns (shiftRows (subBytes s))) roundKey

/-- One middle round of INVCIPHER, lines 5 to 8 of FIPS 197 §5.3, Algorithm 3. -/
def invRound (s roundKey : Block) : Block :=
  invMixColumns (addRoundKey (invSubBytes (invShiftRows s)) roundKey)

/-- The middle rounds `1` to `Nr - 1`, each with a proof that its round key exists. -/
def middleRounds (Nr : Nat) : List { round : Nat // round ≤ Nr } :=
  (List.range' 1 (Nr - 1)).attach.map fun ⟨round, h⟩ =>
    ⟨round, by rw [List.mem_range'_1] at h; omega⟩

/-- CIPHER of FIPS 197 §5.1, Algorithm 1, over `Nr` rounds with key schedule `w`. -/
def cipher (Nr : Nat) (w : Vector Word (4 * (Nr + 1))) (input : Block) : Block :=
  -- Line 3: the initial round key.
  let state := addRoundKey input (roundKey w 0 (Nat.zero_le _))
  -- Lines 4 to 9: rounds 1 to Nr - 1, in increasing order.
  let state := (middleRounds Nr).foldl (fun s r => round s (roundKey w r.val r.property)) state
  -- Lines 10 to 12: the final round has no MIXCOLUMNS.
  addRoundKey (shiftRows (subBytes state)) (roundKey w Nr (Nat.le_refl _))

/-- INVCIPHER of FIPS 197 §5.3, Algorithm 3, over `Nr` rounds with key schedule `w`. -/
def invCipher (Nr : Nat) (w : Vector Word (4 * (Nr + 1))) (input : Block) : Block :=
  -- Line 3: the last round key comes first.
  let state := addRoundKey input (roundKey w Nr (Nat.le_refl _))
  -- Lines 4 to 9: rounds Nr - 1 down to 1.
  let state :=
    (middleRounds Nr).reverse.foldl (fun s r => invRound s (roundKey w r.val r.property)) state
  -- Lines 10 to 12: the last step has no INVMIXCOLUMNS.
  addRoundKey (invSubBytes (invShiftRows state)) (roundKey w 0 (Nat.zero_le _))

/-! ## AES-128 and AES-256 -/

/-- The key sizes of FIPS 197 Table 3 that EthLib supports. -/
inductive KeySize where
  /-- AES-128: `Nk = 4` words of key and `Nr = 10` rounds. -/
  | aes128
  /-- AES-256: `Nk = 8` words of key and `Nr = 14` rounds. -/
  | aes256
  deriving DecidableEq, Repr

/-- The number `Nk` of 32-bit words in the key, FIPS 197 Table 3. -/
def KeySize.Nk : KeySize → Nat
  | .aes128 => 4
  | .aes256 => 8

/-- The number `Nr` of rounds, FIPS 197 Table 3. -/
def KeySize.Nr : KeySize → Nat
  | .aes128 => 10
  | .aes256 => 14

/-- A key of `4 Nk` bytes: 16 bytes for AES-128 and 32 bytes for AES-256. -/
abbrev Key (k : KeySize) := Vector UInt8 (4 * k.Nk)

/-- The forward cipher `CIPH_K` of FIPS 197 §5 (5.1): `CIPHER(in, Nr, KEYEXPANSION(key))`.

It takes a secret key. -/
def ciph (k : KeySize) (key : Key k) (input : Block) : Block :=
  cipher k.Nr (keyExpansion k.Nk k.Nr key) input

/-- The inverse cipher `CIPH_K^-1` of FIPS 197 §5 (5.1): `INVCIPHER(in, Nr, KEYEXPANSION(key))`.

It takes a secret key. -/
def ciphInv (k : KeySize) (key : Key k) (input : Block) : Block :=
  invCipher k.Nr (keyExpansion k.Nk k.Nr key) input

end EthLib.Cryptography.Aes
