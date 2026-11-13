module

public import EthLib.Cryptography.Hash.Hmac

/-!
# HKDF-SHA-256

HKDF over HMAC-SHA-256, [RFC 5869 §2](https://www.rfc-editor.org/rfc/rfc5869#section-2).

The input keying material and the pseudorandom key are secret.

EthLib makes no constant-time claim for them (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Hkdf

open EthLib.Cryptography.Hash.Hmac

/-- The output length `HashLen` of HMAC-SHA-256, in bytes. -/
def HASH_LEN : Nat := 32

/-- Every way HKDF-Expand can reject its input, RFC 5869 §2.3. -/
inductive HkdfError where
  /-- The pseudorandom key was shorter than `HashLen` bytes. -/
  | keyTooShort (size : Nat)
  /-- The requested output was longer than `255 * HashLen` bytes. -/
  | outputTooLong (length : Nat)
deriving DecidableEq, Repr

/-- The stable code of an error, one per constructor, for the C exports.

The code ignores the arguments of the constructor, which the message carries.

A new constructor takes a new code, so that each code keeps its meaning. -/
def HkdfError.code : HkdfError → UInt32
  | .keyTooShort _ => 1
  | .outputTooLong _ => 2

/--
HKDF-Extract, RFC 5869 §2.2: the pseudorandom key `HMAC-Hash(salt, IKM)`.

RFC 5869 sets an absent salt to `HashLen` zero bytes.

HMAC pads its key with zero bytes, so an empty salt gives the same key.

The input keying material is secret, and this function makes no constant-time claim.
-/
def extract (salt ikm : ByteArray) : ByteArray := hmac salt ikm

/--
The blocks `T(i)` to `T(i + count - 1)` of RFC 5869 §2.3, concatenated.

Each block is `HMAC-Hash(PRK, T(i - 1) | info | i)`, with the counter `i` as one byte.
-/
def expandBlocks (prk info previous : ByteArray) (i : Nat) : (count : Nat) → ByteArray
  | 0 => ByteArray.empty
  | count + 1 =>
    let t := hmac prk (previous ++ info ++ ⟨#[UInt8.ofNat i]⟩)
    t ++ expandBlocks prk info t (i + 1) count

/--
HKDF-Expand, RFC 5869 §2.3: the first `length` bytes of `T(1) | T(2) | ...`.

It rejects a key shorter than `HashLen` bytes, and an output longer than `255 * HashLen` bytes.

The pseudorandom key is secret, and this function makes no constant-time claim.
-/
def expand (prk info : ByteArray) (length : Nat) : Except HkdfError ByteArray :=
  if prk.size < HASH_LEN then .error (.keyTooShort prk.size)
  else if 255 * HASH_LEN < length then .error (.outputTooLong length)
  else
    -- `N = ceil(L / HashLen)` blocks cover the output.
    let count := (length + HASH_LEN - 1) / HASH_LEN
    .ok ((expandBlocks prk info ByteArray.empty 1 count).extract 0 length)

/-- The blocks of the expansion are 32 bytes each. -/
theorem expandBlocks_size (prk info previous : ByteArray) (i count : Nat) :
    (expandBlocks prk info previous i count).size = HASH_LEN * count := by
  induction count generalizing previous i with
  | zero => rfl
  | succ count ih =>
    have hmac_size (key message : ByteArray) : (hmac key message).size = 32 :=
      (hmac32 key message).size_toArray
    simp only [expandBlocks, ByteArray.size_append, hmac_size, ih, HASH_LEN]
    omega

/-- A successful expansion has exactly the requested length. -/
theorem expand_size {prk info okm : ByteArray} {length : Nat}
    (h : expand prk info length = .ok okm) : okm.size = length := by
  unfold expand at h
  by_cases short : prk.size < HASH_LEN
  · simp [short] at h
  by_cases long : 255 * HASH_LEN < length
  · simp [short, long] at h
  simp only [short, long, ite_false] at h
  -- The blocks cover the output, so the extraction keeps the requested length.
  obtain rfl := Except.ok.inj h
  simp only [ByteArray.size_extract, expandBlocks_size, HASH_LEN]
  omega

/--
HKDF, RFC 5869 §2: extract, then expand.

The input keying material is secret, and this function makes no constant-time claim.
-/
def hkdf (salt ikm info : ByteArray) (length : Nat) : Except HkdfError ByteArray :=
  expand (extract salt ikm) info length

end EthLib.Cryptography.Hash.Hkdf
