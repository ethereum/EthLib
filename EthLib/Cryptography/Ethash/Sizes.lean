module

/-!
# `Ethash.Sizes`

The parameters of Ethash, and the sizes of its cache and dataset at each epoch.

Source: Appendix J.2 of the Yellow Paper, Berlin version: [`Paper.tex`][yp].

The Ethash specification of the Ethereum Foundation gives the same rule: [Ethash][ethash].

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[ethash]: https://github.com/ethereum/ethereum-org-website/blob/3979915ac0eaa74eb0ae9c9eb6605868ae603bac/public/content/developers/docs/consensus-mechanisms/pow/mining/mining-algorithms/ethash/index.md
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

/-- The blocks in an epoch, over which the cache and the dataset are fixed. -/
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

/-- Whether no divisor from `d` up divides `n`, among the divisors up to the square root of `n`. -/
def noDivisorFrom (n : Nat) : Nat → Nat → Bool
  -- The fuel bounds the divisors tried; `n` of fuel tries every divisor that matters.
  | 0, _ => true
  | fuel + 1, d => n < d * d || (n % d != 0 && noDivisorFrom n fuel (d + 1))

/-- Whether `n` is prime, by trial division up to its square root. -/
def isPrime (n : Nat) : Bool :=
  -- Trial division tries every divisor from 2 to `floor(sqrt(n))`.
  --
  -- The specification skips `floor(sqrt(n))`, but its own tables need it tried.
  2 ≤ n && noDivisorFrom n n 2

/-- The largest `x - 2 · unit · k` whose quotient by `unit` is prime, from `x` down. -/
def primeSize (x unit : Nat) : Nat :=
  -- A size is cut down to the nearest multiple of its unit whose quotient by the unit is prime.
  --
  -- A prime count of items avoids regular patterns in the accesses.
  --
  -- The fuel is the quotient of `x`, which every step lowers.
  go (x / unit) x
where
  /-- Try `x`, then the next candidate below it, until the fuel runs out. -/
  go : Nat → Nat → Nat
    -- The fuel bounds the loop, which the specification leaves unbounded.
    | 0, x => x
    -- While the quotient of the size by the unit is not prime, the size drops by two units.
    --
    -- The unit is one hash, 64 bytes, for the cache, and one mix, 128 bytes, for the dataset.
    --
    -- It is the `E_prime` of J.2.
    --
    -- Each step lowers the quotient by 2, so it keeps its parity.
    | fuel + 1, x => if isPrime (x / unit) then x else go fuel (x - 2 * unit)

/-- The bytes in the cache of the epoch of a block: `c_size` of the Yellow Paper, J.2.

The search for a prime count of items starts one hash, 64 bytes, below the linear size. -/
def cacheSize (number : Nat) : Nat :=
  -- The linear size is `2^24 + 2^17 · floor(number / 30000)` bytes.
  --
  -- So the cache has about 2^24 bytes at genesis, and each epoch adds 2^17 bytes.
  --
  -- One hash, 64 bytes, comes off it, so the prime search starts one hash below it.
  primeSize (CACHE_BYTES_INIT + CACHE_BYTES_GROWTH * epoch number - HASH_BYTES) HASH_BYTES

/-- The bytes in the dataset of the epoch of a block: `d_size` of the Yellow Paper, J.2.

The search for a prime count of items starts one mix, 128 bytes, below the linear size. -/
def datasetSize (number : Nat) : Nat :=
  -- The linear size is `2^30 + 2^23 · floor(number / 30000)` bytes.
  --
  -- So the dataset has about 2^30 bytes at genesis, and each epoch adds 2^23 bytes.
  --
  -- One mix, 128 bytes, comes off it, so the prime search starts one mix below it.
  primeSize (DATASET_BYTES_INIT + DATASET_BYTES_GROWTH * epoch number - MIX_BYTES) MIX_BYTES

end EthLib.Cryptography.Ethash
