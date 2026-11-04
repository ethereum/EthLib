module

/-!
# `Ethash.Sizes`

The parameters of Ethash, and the sizes of its cache and dataset at each epoch.

An epoch is 30,000 blocks, and the cache and the dataset are fixed for an epoch.

At genesis the cache has about 2^24 bytes and the dataset about 2^30 bytes.

Each epoch adds 2^17 bytes to the cache and 2^23 bytes to the dataset.

A size is cut down to the nearest multiple of its unit whose quotient by the unit is prime.

A prime count of items avoids regular patterns in the accesses.

Appendix J.2 of the Yellow Paper, Berlin version, gives the sizes: [`Paper.tex`][yp].

The Ethash specification of the Ethereum Foundation gives the same rule: [Ethash][ethash].

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[ethash]: https://github.com/ethereum/ethereum-org-website/blob/0899bcb4dcb12040ccf46bea0053a422812bf913/public/content/developers/docs/consensus-mechanisms/pow/mining/mining-algorithms/ethash/index.md
-/

@[expose] public section

namespace EthLib.Cryptography.Ethash

/-- The bytes in a word: Ethash mixes 32-bit words. -/
def WORD_BYTES : Nat := 4

/-- The bytes in the dataset at genesis. -/
def DATASET_BYTES_INIT : Nat := 2 ^ 30

/-- The bytes that each epoch adds to the dataset. -/
def DATASET_BYTES_GROWTH : Nat := 2 ^ 23

/-- The bytes in the cache at genesis. -/
def CACHE_BYTES_INIT : Nat := 2 ^ 24

/-- The bytes that each epoch adds to the cache. -/
def CACHE_BYTES_GROWTH : Nat := 2 ^ 17

/-- The blocks in an epoch. -/
def EPOCH_LENGTH : Nat := 30000

/-- The bytes in the mix of the proof-of-work loop, two hashes wide. -/
def MIX_BYTES : Nat := 128

/-- The bytes in a hash: an item of the cache or of the dataset is one Keccak-512 digest. -/
def HASH_BYTES : Nat := 64

/-- The cache items that each dataset item reads. -/
def DATASET_PARENTS : Nat := 256

/-- The rounds of RandMemoHash over the cache. -/
def CACHE_ROUNDS : Nat := 3

/-- The pairs of dataset items that the proof-of-work loop reads. -/
def ACCESSES : Nat := 64

/-- The epoch of a block: its number over the blocks in an epoch, rounded down. -/
def epoch (number : Nat) : Nat :=
  number / EPOCH_LENGTH

/-- Whether no divisor from `d` up divides `n`, among the divisors up to the square root of `n`.

The fuel bounds the divisors tried; `n` of fuel tries every divisor that matters. -/
def noDivisorFrom (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => n < d * d || (n % d != 0 && noDivisorFrom n fuel (d + 1))

/-- Whether `n` is prime, by trial division up to its square root. -/
def isPrime (n : Nat) : Bool :=
  2 ≤ n && noDivisorFrom n n 2

/-- The largest `x - 2 · unit · k` whose quotient by `unit` is prime, from `x` down.

Each step lowers the quotient by 2, so it keeps its parity.

The fuel is the quotient of `x`, which every step lowers. -/
def primeSize (x unit : Nat) : Nat :=
  go (x / unit) x
where
  /-- Try `x`, then the next candidate below it, until the fuel runs out. -/
  go : Nat → Nat → Nat
    | 0, x => x
    | fuel + 1, x => if isPrime (x / unit) then x else go fuel (x - 2 * unit)

/-- The bytes in the cache of the epoch of a block: `c_size` of the Yellow Paper, J.2.

The search starts one hash below the linear size. -/
def cacheSize (number : Nat) : Nat :=
  primeSize (CACHE_BYTES_INIT + CACHE_BYTES_GROWTH * epoch number - HASH_BYTES) HASH_BYTES

/-- The bytes in the dataset of the epoch of a block: `d_size` of the Yellow Paper, J.2.

The search starts one mix below the linear size. -/
def datasetSize (number : Nat) : Nat :=
  primeSize (DATASET_BYTES_INIT + DATASET_BYTES_GROWTH * epoch number - MIX_BYTES) MIX_BYTES

end EthLib.Cryptography.Ethash
