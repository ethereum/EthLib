module

public import EthLib.Cryptography.Secp256k1.Sign

/-!
# Proofs: a known signature over secp256k1

RFC 6979 gives no vectors for secp256k1, so this one comes from `bitcoinjs/tiny-secp256k1`.

It is the first valid case of `tests/fixtures/ecdsa.json` in that repository.

The file is at commit `e1fd7a77bb0ca87fb4726fb1fd4f424f30a04db9`.

That file is under the MIT License, copyright 2018 the bitcoinjs contributors.

The kernel runs the whole signing operation: the nonce generator and the multiple `k G`.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

/-- The private key 1 signs the hash below with `r`, a low `s`, and recovery id 0. -/
theorem sign_tinySecp256k1_0 :
    (sign 0x1 #v[
      0x06, 0xef, 0x2b, 0x19, 0x3b, 0x83, 0xb3, 0xd7, 0x01, 0xf7, 0x65, 0xf1,
      0xdb, 0x34, 0x67, 0x2a, 0xb8, 0x48, 0x97, 0xe1, 0x25, 0x23, 0x43, 0xcc,
      0x21, 0x97, 0x82, 0x9a, 0xf3, 0xa3, 0x04, 0x56]).toOption
      = some (0x33a69cd2065432a30f3d1ce4eb0d59b8ab58c74f27c41a7fdb5696ad4e6108c9,
        0x6f807982866f785d3f6418d24163ddae117b7db4d5fdf0071de069fa54342262, false) := by
  decide +kernel

end Ecdsa

end EthLib.Cryptography.Secp256k1
