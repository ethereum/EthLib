module

public import EthLib.Cryptography.Aes.Ctr
public import EthLib.Cryptography.Hash.ConcatKdf
public import EthLib.Cryptography.Hash.Hmac
public import EthLib.Cryptography.Secp256k1.Ecdh

/-!
# `Networking.Rlpx.Ecies`

The ECIES encryption of RLPx, from the section "ECIES Encryption" of [`rlpx.md`][rlpx].

[rlpx]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/rlpx.md#ecies-encryption

A ciphertext of the message `m` is `R || iv || c || d`:

```text
    [ R: 65 | iv: 16 | c: len(m) | d: 32 ]
```

The sender picks a random key `r` and a random `iv`.

Here the caller passes both, so encryption is a function of its arguments.

The private keys are secret, and EthLib makes no constant-time claim (SOUNDNESS.md A3).
-/

@[expose] public section

namespace EthLib.Networking.Rlpx.Ecies

open EthLib.Cryptography
open EthLib.Cryptography.Secp256k1

/-- The size of `R`, a public key in the uncompressed form of SEC 1 v2 §2.3.3. -/
def EPHEMERAL_KEY_SIZE : Nat := 65

/-- The size of `iv`, one AES block. -/
def IV_SIZE : Nat := 16

/-- The size of the tag `d`, one HMAC-SHA-256 output. -/
def TAG_SIZE : Nat := 32

/-- The bytes that a ciphertext adds to its message: `R`, `iv` and `d`. -/
def OVERHEAD : Nat := EPHEMERAL_KEY_SIZE + IV_SIZE + TAG_SIZE

/-- Every way ECIES can reject its input. -/
inductive EciesError where
  /-- The ciphertext had `size` bytes, fewer than `R`, `iv` and `d` need. -/
  | tooShort (size : Nat)
  /-- `R` was not a public key in the uncompressed form. -/
  | invalidEphemeralKey (error : Secp256k1Error)
  /-- The key agreement failed, because a key was zero or not on the curve. -/
  | keyAgreement (error : Secp256k1Error)
  /-- The key derivation failed. -/
  | keyDerivation (error : Hash.ConcatKdf.ConcatKdfError)
  /-- The tag `d` did not match the tag of `iv || c`. -/
  | tagMismatch
deriving DecidableEq, Repr

/--
The keys `k_E || k_M = KDF(S, 32)` of the shared secret `S`.

`k_E` is the first 16 bytes, an AES-128 key, and `k_M` is the last 16 bytes.

The KDF of SP 800-56A takes no other input here, so its `FixedInfo` is empty.
-/
def deriveKeys (secret : Vector UInt8 32) : Except EciesError (Aes.Key .aes128 × ByteArray) := do
  let keys ← (Hash.ConcatKdf.concatKdf ⟨secret.toArray⟩ .empty 32).mapError .keyDerivation
  return (Vector.ofFn fun i => keys[i.val]!, keys.extract 16 32)

/--
The encryption `c = AES(k_E, iv, m)`: AES-128 in counter mode, from the counter block `iv`.

The counter is the whole block, so the increment is modulo `2^128`.
-/
def cipher (encKey : Aes.Key .aes128) (iv : Aes.Block) (data : ByteArray) : ByteArray :=
  Aes.ctr (Aes.ciph .aes128 encKey) 128 iv data

/--
The tag `d = MAC(sha256(k_M), iv || c || s)`, with HMAC-SHA-256 as the MAC.

The shared data `s` is the `AUTHDATA` of the section "Notation" of `rlpx.md`.

It is authenticated, but it is not part of the ciphertext.
-/
def tag (macKey : ByteArray) (iv : Aes.Block) (c sharedMac : ByteArray) : ByteArray :=
  Hash.Hmac.hmac (Hash.Sha256.hash macKey) (⟨iv.toArray⟩ ++ c ++ sharedMac)

/--
The ciphertext `R || iv || c || d` of `m` to the public key `recipient`.

The shared secret `S` is the `x` of `r K_B`, and `R = r G`.

A zero `r` gives no shared secret, so it is an error.
-/
def encrypt (recipient : Point) (ephemeral : Fn) (iv : Aes.Block) (sharedMac m : ByteArray) :
    Except EciesError ByteArray := do
  let secret ← (ecdh ephemeral recipient).mapError .keyAgreement
  let (encKey, macKey) ← deriveKeys secret
  let c := cipher encKey iv m
  return (Point.mul ephemeral Point.generator).encodeUncompressed ++ ⟨iv.toArray⟩ ++ c ++
    tag macKey iv c sharedMac

/--
The message of the ciphertext `R || iv || c || d`, under the private key `key`.

The shared secret `S` is the `x` of `k_B R`.

The tag is checked before the message is decrypted.
-/
def decrypt (key : Fn) (sharedMac ciphertext : ByteArray) : Except EciesError ByteArray :=
  let bytes := ciphertext.data.toList
  if h : bytes.length < OVERHEAD then .error (.tooShort ciphertext.size)
  else do
    let ephemeral ← (Point.decode ⟨(bytes.take EPHEMERAL_KEY_SIZE).toArray⟩).mapError
      .invalidEphemeralKey
    let secret ← (ecdh key ephemeral).mapError .keyAgreement
    let (encKey, macKey) ← deriveKeys secret
    let iv : Aes.Block :=
      ⟨((bytes.drop EPHEMERAL_KEY_SIZE).take IV_SIZE).toArray, by
        simp [OVERHEAD, EPHEMERAL_KEY_SIZE, IV_SIZE, TAG_SIZE] at h ⊢; omega⟩
    let c : ByteArray :=
      ⟨((bytes.drop (EPHEMERAL_KEY_SIZE + IV_SIZE)).take (bytes.length - OVERHEAD)).toArray⟩
    if bytes.drop (bytes.length - TAG_SIZE) = (tag macKey iv c sharedMac).data.toList then
      .ok (cipher encKey iv c)
    else .error .tagMismatch

end EthLib.Networking.Rlpx.Ecies
