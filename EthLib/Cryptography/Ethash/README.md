# Ethash

Ethash is the proof of work of Ethereum before Paris.
A miner searches for a nonce that makes the hash of a header small enough, and a verifier checks that hash cheaply.

## The epoch, the cache and the dataset

Every 30,000 blocks form an epoch, and each epoch fixes three values.
The seed is 32 zero bytes at epoch 0, and the Keccak-256 hash of the seed before at each later epoch.
The cache is about 16 MiB at genesis: a chain of Keccak-512 hashes of the seed, mixed by three rounds of RandMemoHash.
The dataset is about 1 GiB at genesis, and each of its 64-byte items hashes 256 cache items that its index chooses.
Each epoch adds 128 KiB to the cache and 8 MiB to the dataset.
Each size is cut down until its count of items is prime, which avoids regular access patterns.

A verifier never builds the dataset.
It computes the few items that a header needs from the cache, which takes seconds to build.

## Sources

Appendix J of the Yellow Paper, Berlin version, at commit `beacfbd`, defines Ethash.
In three places it reads differently from every client and from the tests:

- it writes the FNV function as `a · (p ⊕ b)`, where clients compute `(a · p) ⊕ b`;
- it chooses the second item of a cache round by the first byte of an item, where clients use its first 32-bit word;
- it reduces a cache index by the cache size in bytes, where clients reduce it by the count of items.

There the definitions follow the Ethash specification of the Ethereum Foundation, as published on ethereum.org at commit `0899bcb4` of its repository.
Each definition says where it does so.

## What is proved

The proofs are in `EthLib/Cryptography/Proofs/Ethash/`.
Trial division decides primality.
The size search returns the first candidate below the linear size whose count of items is prime.
Every candidate it passes over has a count that is not prime.
Bertrand's postulate gives a prime among the candidates, so at every epoch the cache and the dataset hold a prime number of items.
The seed of an epoch is the Keccak-256 hash of the seed before it.
The cache has one item per 64 bytes of its size, so it is never empty.

## Tests

The Python suite checks the sizes of the 2048 epochs that the Ethash specification tabulates.
It checks the seed, the sizes and the hash of the whole cache of epoch 0 against `PoWTests/ethash_tests.json` of `ethereum/tests`.
It checks dataset items against a transcription of the specification, on small random caches.
The cache of epoch 0 takes seconds, so its test runs weekly.
