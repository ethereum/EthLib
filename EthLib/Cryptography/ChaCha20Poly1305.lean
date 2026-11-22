module

public import EthLib.Base.Bytes
public import EthLib.Base.LittleEndian

/-!
# ChaCha20 and Poly1305

The cipher, authenticator and AEAD construction of [RFC 8439 §§2.1 to 2.8][rfc].

Never reuse a nonce with one AEAD key, or a Poly1305 one-time key.

The keys are secret, and this specification makes no constant-time claim.

RFC 8439 §4 requires a constant-time tag comparison in online protocols.

[rfc]: https://www.rfc-editor.org/rfc/rfc8439#section-2
-/

@[expose] public section

namespace EthLib.Cryptography.ChaCha20Poly1305

open EthLib.Base

/-- A 256-bit ChaCha20 key or Poly1305 one-time key, RFC 8439 §§2.3 and 2.5. -/
abbrev Key := Vector UInt8 32

/-- A 96-bit ChaCha20 nonce, RFC 8439 §2.3. -/
abbrev Nonce := Vector UInt8 12

/-- A 128-bit Poly1305 tag, RFC 8439 §2.5. -/
abbrev Tag := Vector UInt8 16

/-- The sixteen 32-bit words of the ChaCha20 state, RFC 8439 §2.3. -/
abbrev State := Vector UInt32 16

/-- Counter exhaustion, an unencodable length, or failed authentication, RFC 8439 §2.8.

A failed authentication carries nothing, so that it reveals nothing about the expected tag. -/
inductive ChaCha20Poly1305Error where
  /-- A text of `length` bytes, from the block counter `counter`, needs the counter `2^32` or more.

  The AEAD construction starts its text at the counter 1. -/
  | counterExhausted (counter length : Nat)
  /-- The additional data, of `length` bytes, has `2^64` bytes or more. -/
  | aadTooLong (length : Nat)
  /-- The tag does not match. -/
  | authenticationFailed
deriving DecidableEq, Repr

/-- Stable error codes for the bindings. -/
def ChaCha20Poly1305Error.code : ChaCha20Poly1305Error → UInt32
  | .counterExhausted .. => 1
  | .aadTooLong _ => 2
  | .authenticationFailed => 3

/-- Add, XOR and rotate four 32-bit words, RFC 8439 §2.1. -/
def quarterRound (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  -- `a := a + b mod 2^32`, then `d := (d xor a) <<< 16`.
  let a := a + b
  let d := rotl32 (d ^^^ a) 16
  -- `c := c + d mod 2^32`, then `b := (b xor c) <<< 12`.
  let c := c + d
  let b := rotl32 (b ^^^ c) 12
  -- `a := a + b mod 2^32`, then `d := (d xor a) <<< 8`.
  let a := a + b
  let d := rotl32 (d ^^^ a) 8
  -- `c := c + d mod 2^32`, then `b := (b xor c) <<< 7`.
  let c := c + d
  let b := rotl32 (b ^^^ c) 7
  (a, b, c, d)

/-- Apply a quarter round at four positions of the state, RFC 8439 §2.2. -/
def quarterRoundState (s : State) (a b c d : Fin 16) : State :=
  let (w, x, y, z) := quarterRound s[a] s[b] s[c] s[d]
  (((s.set a w).set b x).set c y).set d z

/-- One column round, then one diagonal round, of four quarter rounds each, RFC 8439 §2.3. -/
def doubleRound (s : State) : State :=
  -- §2.3.1, the inner block: the column round, quarter rounds on (0, 4, 8, 12) to (3, 7, 11, 15).
  let s := quarterRoundState s 0 4 8 12
  let s := quarterRoundState s 1 5 9 13
  let s := quarterRoundState s 2 6 10 14
  let s := quarterRoundState s 3 7 11 15
  -- The diagonal round, quarter rounds on (0, 5, 10, 15) to (3, 4, 9, 14).
  let s := quarterRoundState s 0 5 10 15
  let s := quarterRoundState s 1 6 11 12
  let s := quarterRoundState s 2 7 8 13
  quarterRoundState s 3 4 9 14

/-- Constants, key, counter and nonce form the initial state, RFC 8439 §2.3. -/
def initialState (key : Key) (counter : UInt32) (nonce : Nonce) : State :=
  let k (i : Fin 8) : UInt32 :=
    uint32OfBytes key[4 * i.val] key[4 * i.val + 1] key[4 * i.val + 2] key[4 * i.val + 3]
  let n (i : Fin 3) : UInt32 :=
    uint32OfBytes nonce[4 * i.val] nonce[4 * i.val + 1] nonce[4 * i.val + 2]
      nonce[4 * i.val + 3]
  -- §2.3.1: `state = constants | key | counter | nonce`.
  --
  -- §2.3: words 0 to 3 are the constants, 4 to 11 the key, 12 the counter, 13 to 15 the nonce.
  --
  -- The key and the nonce are read as little-endian 32-bit words.
  #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    k 0, k 1, k 2, k 3, k 4, k 5, k 6, k 7, counter, n 0, n 1, n 2]

/-- Read a state as sixteen little-endian words, RFC 8439 §2.3. -/
def stateOfBytes (bytes : Vector UInt8 64) : State :=
  Vector.ofFn fun i : Fin 16 =>
    uint32OfBytes bytes[4 * i.val] bytes[4 * i.val + 1] bytes[4 * i.val + 2]
      bytes[4 * i.val + 3]

/-- Serialize sixteen words as 64 little-endian bytes, RFC 8439 §2.3. -/
def serializeState (words : State) : Vector UInt8 64 :=
  Vector.ofFn fun i : Fin 64 => uint32Byte (words[i.val / 4]'(by omega)) (i.val % 4)

/-- Twenty rounds and feed-forward, serialized little-endian, RFC 8439 §2.3. -/
def block (key : Key) (counter : UInt32) (nonce : Nonce) : Vector UInt8 64 :=
  -- §2.3.1: `state = constants | key | counter | nonce`, and the initial state is a copy of it.
  let initial := initialState key counter nonce
  -- Ten double rounds, each the inner block of §2.3.1.
  let final := (List.range 10).foldl (fun s _ => doubleRound s) initial
  -- The initial state is added to the state, word by word modulo `2^32`.
  let words := Vector.zipWith (· + ·) final initial
  -- The block is the state serialized as 64 bytes, each word little-endian.
  serializeState words

/-- Successive blocks after the caller checks their counter bound, RFC 8439 §2.4. -/
def keyStream (key : Key) (counter : UInt32) (nonce : Nonce) (blocks : Nat) : ByteArray :=
  -- §2.4.1: key stream block `j` is the ChaCha20 block of the key, `counter + j` and the nonce.
  (List.range blocks).foldl (fun bytes i =>
    bytes ++ packBytes (block key (counter + UInt32.ofNat i) nonce)) .empty

/-- Encrypt or decrypt, rejecting counter wrap, RFC 8439 §§2.4 and 2.8. -/
def crypt (key : Key) (counter : UInt32) (nonce : Nonce) (input : ByteArray) :
    Except ChaCha20Poly1305Error ByteArray :=
  -- §2.3 limits one nonce to `2^32` blocks, so a run past the counter `2^32 - 1` is rejected.
  if counter.toNat + (input.size + 63) / 64 > 2 ^ 32 then
    .error (.counterExhausted counter.toNat input.size)
  else
    -- §2.4.1: the output is the input XOR the key stream, one block per started 64 bytes.
    --
    -- The XOR stops at the end of the input, so the last block is truncated as in §2.4.1.
    .ok (xorByteArray input (keyStream key counter nonce ((input.size + 63) / 64)))

/-- Clamp the low half of a Poly1305 key, RFC 8439 §2.5. -/
def clampR (key : Key) : Nat :=
  -- §2.5.1: `r` is bytes 0 to 15 of the key, read as a little-endian number.
  --
  -- The clamp keeps the bits of `r` set in `0x0ffffffc0ffffffc0ffffffc0fffffff`.
  bytesToUint (Vector.ofFn fun i : Fin 16 => key[i.val]'(by omega)) &&&
    0x0ffffffc0ffffffc0ffffffc0fffffff

/-- Accumulate 16-byte blocks with their appended one bit, RFC 8439 §2.5. -/
def poly1305Accumulator (r : Nat) (message : ByteArray) : Nat :=
  -- §2.5.1: from `a = 0`, with `p = 2^130 - 5`, one step per started 16 bytes of the message.
  (List.range ((message.size + 15) / 16)).foldl (fun acc i =>
    let chunk := message.extract (16 * i) (16 * i + 16)
    -- `n` is chunk `i` of up to 16 bytes, then the byte `0x01`, read as a little-endian number.
    --
    -- For a chunk of `k` bytes, the byte `0x01` adds `256^k`.
    let n := bytesToUint (⟨chunk.data, rfl⟩ : Vector UInt8 chunk.size) + 256 ^ chunk.size
    -- `a := (r * (a + n)) mod p`.
    ((acc + n) * r) % (2 ^ 130 - 5)) 0

/-- The low 128 bits of the accumulator plus the key's high half, RFC 8439 §2.5. -/
def poly1305 (key : Key) (message : ByteArray) : Tag :=
  -- §2.5.1: `s` is bytes 16 to 31 of the key, read as a little-endian number.
  let s := bytesToUint (Vector.ofFn fun i : Fin 16 => key[16 + i.val]'(by omega))
  -- The tag is `(a + s) mod 2^128`, as 16 little-endian bytes.
  uintToBytes 16 (poly1305Accumulator (clampR key) message + s)

/-- The first 32 bytes of ChaCha20 block zero, RFC 8439 §2.6. -/
def poly1305Key (key : Key) (nonce : Nonce) : Key :=
  -- §2.6.1: the ChaCha20 block of the key and the nonce, under the counter 0.
  let bytes := block key 0 nonce
  -- The one-time key is its first 32 bytes.
  Vector.ofFn fun i : Fin 32 => bytes[i.val]'(by omega)

/-- Up to 15 zero bytes complete a multiple of 16, RFC 8439 §2.8.1. -/
def pad16 (bytes : ByteArray) : ByteArray :=
  -- For an input of `L` bytes, the padding is empty if 16 divides `L`.
  --
  -- Otherwise it is `16 - (L mod 16)` zero bytes.
  --
  -- The outer reduction modulo 16 gives the empty string in the first case.
  ⟨Array.replicate ((16 - bytes.size % 16) % 16) 0⟩

/-- Pad the AAD and ciphertext, then append their 64-bit lengths, RFC 8439 §2.8. -/
def macData (aad ciphertext : ByteArray) : ByteArray :=
  -- §2.8.1: the MAC data is the AAD, its padding, the ciphertext and its padding.
  --
  -- Then come the byte lengths of the AAD and of the ciphertext, as 8 little-endian bytes each.
  aad ++ pad16 aad ++ ciphertext ++ pad16 ciphertext ++
    packBytes (uintToBytes 8 aad.size) ++ packBytes (uintToBytes 8 ciphertext.size)

/-- AEAD admits at most `2^32 - 1` blocks and `2^64 - 1` AAD bytes, RFC 8439 §2.8. -/
def checkLengths (aadLength textLength : Nat) : Except ChaCha20Poly1305Error Unit :=
  -- §2.8: `A_MAX` is `2^64 - 1` octets, set by the length field for associated data.
  if aadLength ≥ 2 ^ 64 then .error (.aadTooLong aadLength)
  -- §2.8: `P_MAX` is `2^32 - 1` blocks of 64 bytes, as the text starts at the counter 1.
  else if textLength > (2 ^ 32 - 1) * 64 then .error (.counterExhausted 1 textLength)
  else .ok ()

/-- Encrypt and authenticate, returning the ciphertext and its tag, RFC 8439 §2.8. -/
def encrypt (key : Key) (nonce : Nonce) (aad plaintext : ByteArray) :
    Except ChaCha20Poly1305Error (ByteArray × Tag) := do
  checkLengths aad.size plaintext.size
  -- §2.8.1: the ciphertext is the ChaCha20 encryption of the plaintext from the counter 1.
  let ciphertext ← crypt key 1 nonce plaintext
  -- The tag is Poly1305 of the MAC data, under the one-time key of §2.6 from the key and nonce.
  --
  -- The nonce is the caller's 96 bits: the `constant | iv` split is left to the protocol.
  return (ciphertext, poly1305 (poly1305Key key nonce) (macData aad ciphertext))

/-- Authenticate the ciphertext before returning plaintext, RFC 8439 §2.8.

RFC 8439 §4 requires a constant-time tag comparison in online protocols.

This comparison is not constant-time. -/
def decrypt (key : Key) (nonce : Nonce) (aad ciphertext : ByteArray) (tag : Tag) :
    Except ChaCha20Poly1305Error ByteArray := do
  checkLengths aad.size ciphertext.size
  -- §2.8: Poly1305 still runs on the AAD and the ciphertext, and the two tags are compared.
  if poly1305 (poly1305Key key nonce) (macData aad ciphertext) = tag then
    -- §2.8: ChaCha20 applied to the ciphertext gives the plaintext.
    crypt key 1 nonce ciphertext
  else
    throw .authenticationFailed

end EthLib.Cryptography.ChaCha20Poly1305
