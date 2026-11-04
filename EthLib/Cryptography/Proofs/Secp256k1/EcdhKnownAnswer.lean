module

public import EthLib.Cryptography.Secp256k1.Ecdh

/-!
# Proofs: a known ECDH secret over secp256k1

The case is test 1 of `ecdh_secp256k1_test.json` in `C2SP/wycheproof`.

The file is at commit `d17cc89fa5c8f4f4d378b5385ebf75da5d0926c9`, under the Apache License 2.0.

The test encodes the public key in ASN.1, and the point below is its last 65 bytes.

The kernel runs the whole exchange, the multiple `d Q` included.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

/-- Wycheproof ECDH test 1, a normal case. -/
theorem ecdh_wycheproof_1 :
    (ecdh 0xf4b7ff7cccc98813a69fae3df222bfe3f4e28f764bf91b4a10d8096ce446b254
      (.affine 0xd8096af8a11e0b80037e1ee68246b5dcbb0aeb1cf1244fd767db80f3fa27da2b
        0x396812ea1686e7472e9692eaf3e958e50e9500d3b4c77243db1f2acd67ba9cc4)).toOption
      = some #v[
      0x54, 0x4d, 0xfa, 0xe2, 0x2a, 0xf6, 0xaf, 0x93, 0x90, 0x42, 0xb1, 0xd8,
      0x5b, 0x71, 0xa1, 0xe4, 0x9e, 0x9a, 0x56, 0x14, 0x12, 0x3c, 0x4d, 0x6a,
      0xd0, 0xc8, 0xaf, 0x65, 0xba, 0xf8, 0x7d, 0x65] := by
  decide +kernel

end EthLib.Cryptography.Secp256k1
