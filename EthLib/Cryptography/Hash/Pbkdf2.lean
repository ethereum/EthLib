module

public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Base.BigEndian
public import EthLib.Base.Bytes

/-!
# PBKDF2-HMAC-SHA-256

[RFC 8018 §5.2][pbkdf2] defines the blocks and their iterated exclusive-or sums.

Passwords are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).

[pbkdf2]: https://www.rfc-editor.org/rfc/rfc8018#section-5.2
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Pbkdf2

/-- The output size `hLen` of HMAC-SHA-256, in bytes. -/
def HASH_LEN : Nat := 32

/-- The largest output admitted by RFC 8018 §5.2. -/
def MAX_LENGTH : Nat := (2 ^ 32 - 1) * HASH_LEN

/-- Every way PBKDF2-HMAC-SHA-256 can reject its input, RFC 8018 §5.2. -/
inductive Pbkdf2Error where
  /-- The iteration count was zero, but RFC 8018 §5.2 takes a positive integer. -/
  | zeroIterations
  /-- The requested length was zero, but RFC 8018 §5.2 takes a positive integer. -/
  | emptyOutput
  /-- The output was longer than `(2^32 - 1) * hLen` bytes, step 1. -/
  | outputTooLong (length : Nat)
  /-- An HMAC input was longer than the `2^64 - 1` bits that SHA-256 admits, FIPS 180-4 §1. -/
  | inputTooLong
deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def Pbkdf2Error.code : Pbkdf2Error → UInt32
  | .zeroIterations => 1
  | .emptyOutput => 2
  | .outputTooLong _ => 3
  | .inputTooLong => 4

/-- The pseudorandom function of RFC 8018 §5.2, HMAC-SHA-256 with its output size in the type. -/
def prf (password message : ByteArray) : Vector UInt8 32 := Hmac.hmac32 password message

/-- The remaining iterates `U_j`, XORed into the accumulator, RFC 8018 §5.2, step 3. -/
def iterate (password : ByteArray) : Nat → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32
  | 0, _, acc => acc
  | count + 1, previous, acc =>
    let next := prf password ⟨previous.toArray⟩
    iterate password count next (Base.xorBytes acc next)

/-- Block `F(P, S, c, i)`, with the four-byte big-endian index of RFC 8018 §5.2, step 3.

A derivation has a positive iteration count, and zero iterations give the block of one. -/
def block (password salt : ByteArray) (iterations : Nat) (index : UInt32) : Vector UInt8 32 :=
  let first := prf password (salt ++ Base.natToBytes4 index.toNat)
  iterate password (iterations - 1) first first

/-- Concatenate the requested blocks, RFC 8018 §5.2, steps 3 and 4. -/
def blocks (password salt : ByteArray) (iterations : Nat) :
    Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | count + 1, index, out =>
    let next := block password salt iterations (UInt32.ofNat index)
    blocks password salt iterations count (index + 1) (out ++ ⟨next.toArray⟩)

/-- PBKDF2-HMAC-SHA-256, RFC 8018 §5.2, with the output length in bytes.

Its time grows with the iteration count times the 32-byte blocks of the output.

The output can reach 128 GiB, so a caller must bound both first (SOUNDNESS.md D1). -/
def pbkdf2 (password salt : ByteArray) (iterations length : Nat) :
    Except Pbkdf2Error ByteArray :=
  if iterations = 0 then .error .zeroIterations
  else if length = 0 then .error .emptyOutput
  else if MAX_LENGTH < length then .error (.outputTooLong length)
  -- SHA-256 admits fewer than `2^64` bits (FIPS 180-4 §1), including HMAC's inner block.
  else if 2 ^ 61 ≤ password.size ∨ 2 ^ 61 ≤ 64 + salt.size + 4 then .error .inputTooLong
  else
    let count := (length + HASH_LEN - 1) / HASH_LEN
    .ok ((blocks password salt iterations count 1 ByteArray.empty).extract 0 length)

end EthLib.Cryptography.Hash.Pbkdf2
