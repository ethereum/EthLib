module

public import EthLib.Cryptography.Bls.Signatures
public import EthLib.Cryptography.Hash.Hkdf
public import EthLib.Base.BigEndian

/-!
# BLS key generation

Key generation of the IRTF BLS signature draft, version 4, §2.3.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-2.3>

The draft loops until the key is not zero, and this module bounds that loop.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Signatures

open EthLib.Cryptography.Bls
open EthLib.Cryptography.Hash

/-- The first salt of key generation, the 20 ASCII bytes `BLS-SIG-KEYGEN-SALT-`. -/
def KEYGEN_SALT : ByteArray := String.toUTF8 "BLS-SIG-KEYGEN-SALT-"

/-- The output length `L = ceil(3 * ceil(log2(r)) / 16)` of key generation, in bytes.

`r` has 255 bits, so `L = ceil(765 / 16) = 48`. -/
def KEYGEN_L : Nat := 48

/-- The number of salts that key generation tries before it fails.

An attempt fails only when its output is a multiple of `r`. -/
def KEYGEN_ATTEMPTS : Nat := 16

/-- The attempts of key generation that remain, from the previous salt `salt`.

The key material is secret, and this function does not run in constant time. -/
def keyGenLoop (ikm keyInfo : ByteArray) : (salt : ByteArray) → (attempts : Nat) →
    Except BlsError SecretKey
  | _, 0 => .error .keyGenNoKey
  | salt, attempts + 1 => do
    let salt := Sha256.hash salt
    let prk := Hkdf.extract salt (ikm ++ HashToCurve.i2osp 0 1)
    let okm ← (Hkdf.expand prk (keyInfo ++ HashToCurve.i2osp KEYGEN_L 2) KEYGEN_L).mapError
      fun _ => .keyGenHkdf
    -- `OS2IP(OKM) mod r`.
    let sk := Fr.ofNat (Base.bytesToNat okm.data.toList)
    if h : sk = 0 then keyGenLoop ikm keyInfo salt attempts else return ⟨sk, h⟩

/-- Key generation (§2.3): a secret key from at least 32 bytes of input keying material.

It fails on a shorter input, and when every attempt gives a multiple of `r`.

The key material is secret, and this function does not run in constant time. -/
def keyGen (ikm : ByteArray) (keyInfo : ByteArray := ByteArray.empty) :
    Except BlsError SecretKey :=
  if ikm.size < 32 then .error (.keyGenIkmTooShort ikm.size)
  else keyGenLoop ikm keyInfo KEYGEN_SALT KEYGEN_ATTEMPTS

end EthLib.Cryptography.Bls.Signatures
