module

public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Cryptography.Hash.ConcatKdf

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

/-- Invalid parameters of PBKDF2-HMAC-SHA-256. -/
inductive Pbkdf2Error where
  | zeroIterations
  | emptyOutput
  | outputTooLong (length : Nat)
  | inputTooLong
deriving DecidableEq, Repr

/-- Stable error codes for the bindings, one per constructor. -/
def Pbkdf2Error.code : Pbkdf2Error → UInt32
  | .zeroIterations => 1
  | .emptyOutput => 2
  | .outputTooLong _ => 3
  | .inputTooLong => 4

/-- The pseudorandom function of RFC 8018 §5.2 with its output size in the type. -/
def prf (password message : ByteArray) : Vector UInt8 32 :=
  ⟨(Hmac.hmac password message).data, by simp [Hmac.hmac, Sha256.hash, Sha256.digest]⟩

/-- The remaining iterates `U_j`, XORed into the accumulator, RFC 8018 §5.2, step 3. -/
def iterate (password : ByteArray) : Nat → Vector UInt8 32 → Vector UInt8 32 → Vector UInt8 32
  | 0, _, acc => acc
  | count + 1, previous, acc =>
    let next := prf password ⟨previous.toArray⟩
    iterate password count next (Vector.zipWith (· ^^^ ·) acc next)

/-- Block `F(P, S, c, i)`, with the four-byte big-endian index of RFC 8018 §5.2, step 3. -/
def block (password salt : ByteArray) (iterations : Nat) (_positive : 0 < iterations)
    (index : UInt32) : Vector UInt8 32 :=
  let first := prf password (salt ++ ConcatKdf.counterBytes index.toNat)
  iterate password (iterations - 1) first first

/-- Concatenate the requested blocks, RFC 8018 §5.2, steps 3 and 4. -/
def blocks (password salt : ByteArray) (iterations : Nat) (positive : 0 < iterations) :
    Nat → Nat → ByteArray → ByteArray
  | 0, _, out => out
  | count + 1, index, out =>
    let next := block password salt iterations positive (UInt32.ofNat index)
    blocks password salt iterations positive count (index + 1) (out ++ ⟨next.toArray⟩)

/-- PBKDF2-HMAC-SHA-256, RFC 8018 §5.2, with the output length in bytes. -/
def pbkdf2 (password salt : ByteArray) (iterations length : Nat) :
    Except Pbkdf2Error ByteArray :=
  if positive : 0 < iterations then
    if length = 0 then .error .emptyOutput
    else if MAX_LENGTH < length then .error (.outputTooLong length)
    -- SHA-256 admits fewer than `2^64` bits, including HMAC's inner block.
    else if 2 ^ 61 ≤ password.size ∨ 2 ^ 61 ≤ 64 + salt.size + 4 then .error .inputTooLong
    else
      let count := (length + HASH_LEN - 1) / HASH_LEN
      .ok ((blocks password salt iterations positive count 1 ByteArray.empty).extract 0 length)
  else .error .zeroIterations

end EthLib.Cryptography.Hash.Pbkdf2
