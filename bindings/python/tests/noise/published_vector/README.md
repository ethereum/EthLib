# Published Noise XX vector

`noise_xx_vector.json` holds the `Noise_XX_25519_ChaChaPoly_SHA256` entry of `tests/vector/noise-c-basic.txt` in [`rweather/noise-c`](https://github.com/rweather/noise-c) at commit `cfe25410979a87391bb9ac8d4d4bef64e9f268c6`, with its fields unchanged.

The Noise specification publishes no test vectors, so the raw handshake test reads this entry.
It gives both parties' keys and prologue, the payload and ciphertext of three handshake messages and three transport messages, and the final handshake hash.

The entry is under the MIT License, copyright 2016 Southern Storm Software, in `LICENSE`.
`SHA256SUMS` pins both files.
