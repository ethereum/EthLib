module

public import EthLib.Base.Address
public import EthLib.Cryptography.Secp256k1.Encoding
public import EthLib.Cryptography.Hash.Keccak

/-!
# `Secp256k1.Address`

The Ethereum address of a public key, from Appendix F of the Yellow Paper, Shanghai version.

The source is `Paper.tex` at `efc5f9a`:
<https://github.com/ethereum/yellowpaper/blob/efc5f9a1f356cba376c978eedb63cb0363c2aa85/Paper.tex>

```text
    A(p_r) = B_96..255(KEC(ECDSAPUBKEY(p_r)))
```

`ECDSAPUBKEY` gives the public key as 64 bytes: `x` then `y`, 32 big-endian bytes each.

That is the uncompressed SEC 1 encoding without its `04` prefix.

The address is the last 20 of the 32 bytes of its Keccak-256 hash, bits 96 to 255.

The mixed-case checksum of EIP-55 only changes how an address is written, and is not part of it.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- The 64 bytes `ECDSAPUBKEY` gives for the point `(x, y)`: `x` then `y`. -/
def publicKeyBytes (x y : Fp) : ByteArray := ⟨(x.toBytes ++ y.toBytes).toArray⟩

/-- The address of the public key `(x, y)`.

It is the last 20 bytes of the Keccak-256 hash of the key's 64 bytes. -/
def address (x y : Fp) : Base.Address :=
  let digest := Hash.Keccak.keccak256 (publicKeyBytes x y)
  -- Bytes 12 to 31 of the digest are its bits 96 to 255.
  Vector.ofFn fun i => digest[12 + i.val]'(by have := i.isLt; simp [Hash.Keccak.DIGEST_LEN]; omega)

/-- `A(p_r)`, the address of the private key `d`, with the public key `d G`.

A private key lies in `[1, n - 1]`, by Appendix F, so `d G` is never `O`.

`d = 0` gives `O`, which has no address, and `none`. -/
def addressOfPrivateKey (d : Fn) : Option Base.Address :=
  match Point.mul d .generator with
  | .infinity => none
  | .affine x y => some (address x y)

end EthLib.Cryptography.Secp256k1
