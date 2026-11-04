# tiny-secp256k1 ECDSA fixtures

`ecdsa.json` is `tests/fixtures/ecdsa.json` of [`bitcoinjs/tiny-secp256k1`](https://github.com/bitcoinjs/tiny-secp256k1) at commit `e1fd7a77bb0ca87fb4726fb1fd4f424f30a04db9`, copied byte for byte.

RFC 6979 gives no test vectors for secp256k1, so the signing test reads its valid cases instead.
Each case gives a private key, a 32-byte hash, the signature with a low `s`, and the recovery id.

The file is under the MIT License, copyright 2018 the bitcoinjs contributors, in `LICENSE`.
`SHA256SUMS` pins both files.
