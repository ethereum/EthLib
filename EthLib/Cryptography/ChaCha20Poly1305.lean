module

public import EthLib.Base.Bytes
public import EthLib.Base.LittleEndian

/-!
# ChaCha20 and Poly1305

The cipher, authenticator and AEAD construction of [RFC 8439 §§2.1 to 2.8][rfc].

Never reuse a nonce with one AEAD key, or a Poly1305 one-time key.

The keys are secret, and this specification makes no constant-time claim.

[rfc]: https://www.rfc-editor.org/rfc/rfc8439#section-2
-/

@[expose] public section

namespace EthLib.Cryptography.ChaCha20Poly1305

open EthLib.Base

abbrev Key := Vector UInt8 32
abbrev Nonce := Vector UInt8 12
abbrev Tag := Vector UInt8 16
abbrev State := Vector UInt32 16

/-- Counter exhaustion, an unencodable length, or failed authentication, RFC 8439 §2.8. -/
inductive CipherError where
  | counterExhausted
  | aadTooLong
  | authenticationFailed
deriving DecidableEq, Repr

/-- Stable error codes for the bindings. -/
def CipherError.code : CipherError → UInt32
  | .counterExhausted => 1
  | .aadTooLong => 2
  | .authenticationFailed => 3

/-- Rotate a word left, RFC 8439 §2.1. -/
@[inline] def rotl (x shift : UInt32) : UInt32 :=
  (x <<< shift) ||| (x >>> (32 - shift))

/-- Add, XOR and rotate four 32-bit words, RFC 8439 §2.1. -/
def quarterRound (a b c d : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b
  let d := rotl (d ^^^ a) 16
  let c := c + d
  let b := rotl (b ^^^ c) 12
  let a := a + b
  let d := rotl (d ^^^ a) 8
  let c := c + d
  let b := rotl (b ^^^ c) 7
  (a, b, c, d)

/-- Apply a quarter round at four positions of the state, RFC 8439 §2.2. -/
def quarterRoundState (s : State) (a b c d : Fin 16) : State :=
  let (w, x, y, z) := quarterRound s[a] s[b] s[c] s[d]
  (((s.set a w).set b x).set c y).set d z

/-- Four column rounds, then four diagonal rounds, RFC 8439 §2.3. -/
def doubleRound (s : State) : State :=
  let s := quarterRoundState s 0 4 8 12
  let s := quarterRoundState s 1 5 9 13
  let s := quarterRoundState s 2 6 10 14
  let s := quarterRoundState s 3 7 11 15
  let s := quarterRoundState s 0 5 10 15
  let s := quarterRoundState s 1 6 11 12
  let s := quarterRoundState s 2 7 8 13
  quarterRoundState s 3 4 9 14

/-- Read four bytes as a little-endian word, RFC 8439 §2.3. -/
def little32 {n : Nat} (v : Vector UInt8 n) (i : Nat) (h : i + 4 ≤ n) : UInt32 :=
  (v[i]'(by omega)).toUInt32 ||| (v[i + 1]'(by omega)).toUInt32 <<< 8 |||
    (v[i + 2]'(by omega)).toUInt32 <<< 16 ||| (v[i + 3]'(by omega)).toUInt32 <<< 24

/-- Constants, key, counter and nonce form the initial state, RFC 8439 §2.3. -/
def initialState (key : Key) (counter : UInt32) (nonce : Nonce) : State :=
  #v[0x61707865, 0x3320646e, 0x79622d32, 0x6b206574,
    little32 key 0 (by decide), little32 key 4 (by decide),
    little32 key 8 (by decide), little32 key 12 (by decide),
    little32 key 16 (by decide), little32 key 20 (by decide),
    little32 key 24 (by decide), little32 key 28 (by decide), counter,
    little32 nonce 0 (by decide), little32 nonce 4 (by decide), little32 nonce 8 (by decide)]

/-- Read a state as sixteen little-endian words, RFC 8439 §2.3. -/
def stateOfBytes (bytes : Vector UInt8 64) : State :=
  Vector.ofFn fun i : Fin 16 => little32 bytes (4 * i.val) (by omega)

/-- Serialize sixteen words as 64 little-endian bytes, RFC 8439 §2.3. -/
def serializeState (words : State) : Vector UInt8 64 :=
  Vector.ofFn fun i : Fin 64 =>
    (words[i.val / 4]'(by omega) >>> UInt32.ofNat (8 * (i.val % 4))).toUInt8

/-- Twenty rounds and feed-forward, serialized little-endian, RFC 8439 §2.3. -/
def block (key : Key) (counter : UInt32) (nonce : Nonce) : Vector UInt8 64 :=
  let initial := initialState key counter nonce
  let final := (List.range 10).foldl (fun s _ => doubleRound s) initial
  let words := Vector.zipWith (· + ·) final initial
  serializeState words

/-- Successive blocks after the caller checks their counter bound, RFC 8439 §2.4. -/
def keyStream (key : Key) (counter : UInt32) (nonce : Nonce) (blocks : Nat) : ByteArray :=
  (List.range blocks).foldl (fun bytes i =>
    bytes ++ packBytes (block key (counter + UInt32.ofNat i) nonce)) .empty

/-- Encrypt or decrypt, rejecting counter wrap, RFC 8439 §§2.4 and 2.8. -/
def crypt (key : Key) (counter : UInt32) (nonce : Nonce) (input : ByteArray) :
    Except CipherError ByteArray :=
  if counter.toNat + (input.size + 63) / 64 > 2 ^ 32 then
    .error .counterExhausted
  else
    .ok (xorByteArray input (keyStream key counter nonce ((input.size + 63) / 64)))

/-- Clamp the low half of a Poly1305 key, RFC 8439 §2.5. -/
def clampR (key : Key) : Nat :=
  bytesToUint (Vector.ofFn fun i : Fin 16 => key[i.val]'(by omega)) &&&
    0x0ffffffc0ffffffc0ffffffc0fffffff

/-- Accumulate 16-byte blocks with their appended one bit, RFC 8439 §2.5. -/
def poly1305Accumulator (r : Nat) (message : ByteArray) : Nat :=
  (List.range ((message.size + 15) / 16)).foldl (fun acc i =>
    let chunk := message.extract (16 * i) (16 * i + 16)
    let n := bytesToUint (⟨chunk.data, rfl⟩ : Vector UInt8 chunk.size) + 256 ^ chunk.size
    ((acc + n) * r) % (2 ^ 130 - 5)) 0

/-- The low 128 bits of the accumulator plus the key's high half, RFC 8439 §2.5. -/
def poly1305 (key : Key) (message : ByteArray) : Tag :=
  let s := bytesToUint (Vector.ofFn fun i : Fin 16 => key[16 + i.val]'(by omega))
  uintToBytes 16 (poly1305Accumulator (clampR key) message + s)

/-- The first 32 bytes of ChaCha20 block zero, RFC 8439 §2.6. -/
def poly1305Key (key : Key) (nonce : Nonce) : Key :=
  let bytes := block key 0 nonce
  Vector.ofFn fun i : Fin 32 => bytes[i.val]'(by omega)

/-- Up to 15 zero bytes complete a multiple of 16, RFC 8439 §2.8.1. -/
def pad16 (bytes : ByteArray) : ByteArray :=
  ⟨Array.replicate ((16 - bytes.size % 16) % 16) 0⟩

/-- Pad the AAD and ciphertext, then append their 64-bit lengths, RFC 8439 §2.8. -/
def macData (aad ciphertext : ByteArray) : ByteArray :=
  aad ++ pad16 aad ++ ciphertext ++ pad16 ciphertext ++
    packBytes (uintToBytes 8 aad.size) ++ packBytes (uintToBytes 8 ciphertext.size)

/-- AEAD admits at most `2^32 - 1` blocks and `2^64 - 1` AAD bytes, RFC 8439 §2.8. -/
def checkLengths (aadLength textLength : Nat) : Except CipherError Unit :=
  if aadLength ≥ 2 ^ 64 then .error .aadTooLong
  else if textLength > (2 ^ 32 - 1) * 64 then .error .counterExhausted
  else .ok ()

/-- Encrypt and authenticate, returning the ciphertext and its tag, RFC 8439 §2.8. -/
def encrypt (key : Key) (nonce : Nonce) (aad plaintext : ByteArray) :
    Except CipherError (ByteArray × Tag) := do
  checkLengths aad.size plaintext.size
  let ciphertext ← crypt key 1 nonce plaintext
  return (ciphertext, poly1305 (poly1305Key key nonce) (macData aad ciphertext))

/-- Authenticate the ciphertext before returning plaintext, RFC 8439 §2.8. -/
def decrypt (key : Key) (nonce : Nonce) (aad ciphertext : ByteArray) (tag : Tag) :
    Except CipherError ByteArray := do
  checkLengths aad.size ciphertext.size
  if poly1305 (poly1305Key key nonce) (macData aad ciphertext) = tag then
    crypt key 1 nonce ciphertext
  else
    throw .authenticationFailed

end EthLib.Cryptography.ChaCha20Poly1305
