module

public import EthLib.Cryptography.Secp256k1.Ecdsa

/-!
# `Secp256k1.Recovery`

Public key recovery, from SEC 1 v2 §4.1.6.

An Ethereum transaction carries a signature, not a public key.

The key is rebuilt from the signature and the hash, then hashed into the sender's address.

The recovery ids are those of Appendix F of the [Yellow Paper][yp], Shanghai version (`efc5f9a`).

[yp]: https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

/-- The public key whose signature on `hash` is `(r, s)`, by SEC 1 v2 §4.1.6.

The recovery id gives the parity of the `y` of `R`. -/
def recover (hash : Vector UInt8 32) (r s : Nat) (recoveryId : Fin 2) : Except Secp256k1Error Point :=
  -- Not a step of §4.1.6: `0 < r, s < secp256k1n`, as ECREC in Appendix E asks.
  if hr : 0 < r ∧ r < Fn.modulus then
    if hs : 0 < s ∧ s < Fn.modulus then do
      -- Step 1 runs `j` from 0 to `h = 1`; the ids name only `j = 0`, so a failure is final.
      --
      -- That loses only the rare signatures whose `x_R >= n`.
      --
      -- Steps 1.1 to 1.3: `x = r + 0 n < p`, and `R` from `02 || X`, of even `y`.
      --
      -- Step 1.6.3 turns `R` into `-R`, of odd `y`: the id picks one of the two directly.
      --
      -- So the id picks the signer's point `R`, whose `x` is `r`.
      --
      -- The id `0` names an even `y`, and `1` an odd `y`.
      --
      -- The Yellow Paper declares the ids 2 and 3 invalid.
      let R ← Point.decompress (Fin.ofNat _ r) (recoveryId == 1)
      -- Step 1.4 asks `n R = O`, which holds for every point: the cofactor is 1.
      --
      -- Step 1.5: `e` from the hash, by steps 2 and 3 of verification.
      let e : Fn := Fin.ofNat _ (hashToInt hash)
      -- Step 1.6.1: `Q = r^(-1) (s R - e G) = (r^(-1) s) R + (-(r^(-1) e)) G`.
      --
      -- It solves `s R = e G + r Q`, the verification equation times `s`.
      let rInv := Fn.inv ⟨r, hr.2⟩
      let q := Point.mulAdd (rInv * ⟨s, hs.2⟩) R (-(rInv * e)) .generator
      -- Step 1.6.2 is left to the caller, and a public key is never `O`.
      if q = .infinity then .error .pointAtInfinity else .ok q
    else .error (.scalarOutOfRange s)
  else .error (.scalarOutOfRange r)

end Ecdsa

end EthLib.Cryptography.Secp256k1
