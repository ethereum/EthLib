module

public import EthLib.Base.BigEndian
public import EthLib.Base.Bytes
public import EthLib.Cryptography.Hash.Hkdf

/-!
# TLS 1.3 labelled HKDF over SHA-256

[RFC 8446 §7.1][tls] binds each expansion to a label, a context and the requested length.

The label carries the prefix `tls13 `, which separates these uses from other uses of HKDF.

Secrets have 32 bytes, and each expansion carries its output length in its type.

The secrets are secret, and EthLib makes no constant-time claim for them (SOUNDNESS.md A3).

[tls]: https://www.rfc-editor.org/rfc/rfc8446#section-7.1
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Tls13

open EthLib.Base

/-- A SHA-256 secret of `Hash.length = 32` bytes, RFC 8446 §7.1. -/
abbrev Secret := Vector UInt8 32

/-- Malformed `HkdfLabel` fields or an output beyond the HKDF limit. -/
inductive Error where
  /-- The label without its prefix is empty or exceeds 249 bytes. -/
  | labelLength (size : Nat)
  /-- The context exceeds the one-byte length field. -/
  | contextLength (size : Nat)
  /-- The output length exceeds the two-byte length field. -/
  | lengthOverflow (length : Nat)
  /-- HKDF rejected its inputs under RFC 5869 §2.3. -/
  | hkdf (error : Hkdf.HkdfError)
  deriving DecidableEq, Repr

/-- One stable code for each kind of TLS derivation error. -/
def Error.code : Error → UInt32
  | .labelLength _ => 1
  | .contextLength _ => 2
  | .lengthOverflow _ => 3
  | .hkdf _ => 4

/-- HKDF-Extract of RFC 5869 §2.2, as a 32-byte secret.

The input keying material is secret, and this function makes no constant-time claim. -/
def extract (salt ikm : ByteArray) : Secret := Hmac.hmac32 salt ikm

/-- Serialize `HkdfLabel` after checking the field bounds of RFC 8446 §7.1.

The supplied label excludes the `tls13 ` prefix. -/
def hkdfLabel (label context : ByteArray) (length : Nat) : Except Error ByteArray := do
  if label.size = 0 ∨ 249 < label.size then throw (.labelLength label.size)
  if 255 < context.size then throw (.contextLength context.size)
  if 65535 < length then throw (.lengthOverflow length)
  let fullLabel := "tls13 ".toUTF8 ++ label
  return ⟨(natToBytes 2 length).toArray⟩ ++ ⟨#[UInt8.ofNat fullLabel.size]⟩ ++
    fullLabel ++ ⟨#[UInt8.ofNat context.size]⟩ ++ context

/-- `HKDF-Expand-Label` with SHA-256, RFC 8446 §7.1.

RFC 5869 §2.3 limits the output to `255 * 32` bytes.

The secret is secret, and this function makes no constant-time claim. -/
def expandLabel (secret : Secret) (label context : ByteArray) (length : Nat) :
    Except Error (Vector UInt8 length) := do
  let info ← hkdfLabel label context length
  match h : Hkdf.expand (packBytes secret) info length with
  | .error e => throw (.hkdf e)
  | .ok output => return ⟨output.data, Hkdf.expand_size h⟩

end EthLib.Cryptography.Hash.Tls13
