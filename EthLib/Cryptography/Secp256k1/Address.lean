module

public import EthLib.Base.Address
public import EthLib.Cryptography.Secp256k1.Encoding
public import EthLib.Cryptography.Hash.Keccak

/-!
# `Secp256k1.Address`

The Ethereum address of a public key, from Appendix F of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

The mixed-case checksum of EIP-55 only changes how an address is written, and is not part of it.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- The 64 bytes `ECDSAPUBKEY` gives for the point `(x, y)`: `x` then `y`. -/
def publicKeyBytes (x y : Fp) : ByteArray :=
  -- Appendix F: `p_u` is 64 bytes, from two integers below `2^256`.
  --
  -- Each is 32 big-endian bytes, as in the uncompressed SEC 1 encoding without its `04` prefix.
  x.toBytes ++ y.toBytes

/-- The address of the public key `(x, y)`: the last 20 bytes of its Keccak-256 hash. -/
def address (x y : Fp) : Base.Address :=
  -- `A(p_r) = B_96..255(KEC(ECDSAPUBKEY(p_r)))`, with `ECDSAPUBKEY(p_r)` the 64 bytes of the key.
  let digest := Hash.Keccak.keccak256 (publicKeyBytes x y)
  -- `B_96..255`: bytes 12 to 31 of the digest are its bits 96 to 255.
  Vector.ofFn fun i =>
    digest[12 + i.val]'(by have := i.isLt; simp [Hash.Keccak.DIGEST_LEN_256]; omega)

/-- `A(p_r)`, the address of the private key `d`, with the public key `d G`.

A private key lies in `[1, n - 1]`, by Appendix F, so `d G` is never `O`.

`d = 0` gives `O`, which has no address, and `none`. -/
def addressOfPrivateKey (d : Fn) : Option Base.Address :=
  -- `ECDSAPUBKEY(p_r)` is the point `p_r G`, by SEC 1 v2 §3.2.1 step 2.
  match Point.mul d .generator with
  | .infinity => none
  | .affine x y => some (address x y)

end EthLib.Cryptography.Secp256k1
