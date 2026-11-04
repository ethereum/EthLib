module

public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Cryptography.Ethash.Sizes

/-!
# `Ethash.Cache`

The seed, the cache and the dataset items of Ethash.

The seed of an epoch is Keccak-256 applied to 32 zero bytes once per epoch.

The cache is a chain of Keccak-512 digests of the seed, mixed by three rounds of RandMemoHash.

A dataset item hashes 256 cache items, chosen from its index, with the FNV function.

So a verifier computes any dataset item from the cache alone.

Appendix J.3 of the Yellow Paper, Berlin version, defines them: [`Paper.tex`][yp].

In three places the appendix reads differently from every client and from the tests.

There the definitions follow the Ethash specification of the Ethereum Foundation: [Ethash][ethash].

Each of those places says so.

An item is 64 bytes, read as 16 words of 32 bits, the first byte least significant.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[ethash]: https://github.com/ethereum/ethereum-org-website/blob/0899bcb4dcb12040ccf46bea0053a422812bf913/public/content/developers/docs/consensus-mechanisms/pow/mining/mining-algorithms/ethash/index.md
-/

@[expose] public section

namespace EthLib.Cryptography.Ethash

open EthLib.Cryptography.Hash.Keccak (keccak256 keccak512)

/-- An item of the cache or of the dataset: 16 words of 32 bits, 64 bytes. -/
abbrev Item := Vector UInt32 16

/-- The 16 words that 64 bytes spell, 4 bytes each, the first byte least significant. -/
def itemOfBytes (bytes : Vector UInt8 64) : Item :=
  Vector.ofFn fun k : Fin 16 =>
    -- Word `k` is bytes `4k` to `4k + 3`.
    bytes[4 * k.val].toUInt32 ||| bytes[4 * k.val + 1].toUInt32 <<< 8 |||
      bytes[4 * k.val + 2].toUInt32 <<< 16 ||| bytes[4 * k.val + 3].toUInt32 <<< 24

/-- The bytes of some words, 4 per word, the least significant first. -/
def bytesOfWords {n : Nat} (words : Vector UInt32 n) : ByteArray :=
  ⟨words.toArray.flatMap fun w : UInt32 =>
    (#[w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8] : Array UInt8)⟩

/-- The Keccak-512 digest of some bytes, as an item. -/
def hashItem (bytes : ByteArray) : Item :=
  itemOfBytes ((keccak512 bytes).cast rfl)

/-! ## The seed -/

/-- The seed of the epoch of a block: `C_seedhash` of the Yellow Paper, J.3.1.

It is 32 zero bytes at epoch 0, and the Keccak-256 digest of the previous seed after. -/
def seed (number : Nat) : ByteArray :=
  Nat.repeat (fun s => ⟨(keccak256 s).toArray⟩) (epoch number) ⟨Array.replicate 32 0⟩

/-! ## The cache -/

/-- The cache before the rounds: `c'` of the Yellow Paper, J.3.2.

Item 0 is the Keccak-512 digest of the seed, and each next item the digest of the one before. -/
def initialCache (n : Nat) (s : ByteArray) : Array Item :=
  (List.range n).foldl
    (fun c _ =>
      c.push (match c.back? with
        | none => hashItem s
        | some previous => hashItem (bytesOfWords previous)))
    #[]

/-- One round of RandMemoHash over the cache: `E_RMH` of the Yellow Paper, J.3.2.

Item `i` becomes the Keccak-512 digest of the XOR of two items, taken as they are at that step.

The first is item `i - 1`, which is already new for `i ≥ 1`.

The second is the item that the first word of item `i` names.

The appendix names that item by the first byte, and the specification by the first word.

The definition follows the specification. -/
def cacheRound (cache : Array Item) : Array Item :=
  let n := cache.size
  (List.range n).foldl
    (fun c i =>
      -- Each index is below the size, which the round keeps, so no default is read.
      let current := c.getD i (Vector.replicate 16 0)
      let previous := c.getD ((i + n - 1) % n) (Vector.replicate 16 0)
      let other := c.getD (current[0].toNat % n) (Vector.replicate 16 0)
      c.setIfInBounds i (hashItem (bytesOfWords (Vector.zipWith (· ^^^ ·) previous other))))
    cache

/-- The cache of the epoch of a block: `c` of the Yellow Paper, J.3.2.

It has one item per 64 bytes of the cache size, after three rounds over the initial cache. -/
def cache (number : Nat) : Array Item :=
  Nat.repeat cacheRound CACHE_ROUNDS (initialCache (cacheSize number / HASH_BYTES) (seed number))

/-! ## The dataset items -/

/-- The prime of the FNV function. -/
def FNV_PRIME : UInt32 := 0x01000193

/-- The FNV function of Ethash: `(a · p) ⊕ b`, mod `2^32`.

The appendix writes `a · (p ⊕ b)`, and the specification and every client `(a · p) ⊕ b`.

The definition follows the specification. -/
def fnv (a b : UInt32) : UInt32 :=
  a * FNV_PRIME ^^^ b

/-- The dataset item at an index, from the cache: `E_datasetitem` of the Yellow Paper, J.3.3.

The mix starts as the Keccak-512 digest of a cache item whose first word is XORed with the index.

Each of 256 parents is a cache item that the index and the mix choose, and FNV folds it in.

The item is the Keccak-512 digest of the last mix.

The appendix reads the cache by its size in bytes, and the specification by its count of items.

The definition follows the specification.

The index is below `2^32` while the dataset has fewer than `2^32` items. -/
def datasetItem (cache : Array Item) (i : Nat) : Item :=
  let n := cache.size
  let first := cache.getD (i % n) (Vector.replicate 16 0)
  let mix := hashItem (bytesOfWords (first.set 0 (first[0] ^^^ i.toUInt32)))
  let mix := (List.range DATASET_PARENTS).foldl
    (fun mix j =>
      -- Parent `j` is the cache item that FNV of `i ⊕ j` and word `j mod 16` of the mix names.
      let parent := cache.getD ((fnv (i ^^^ j).toUInt32 mix[j % 16]).toNat % n)
        (Vector.replicate 16 0)
      Vector.zipWith fnv mix parent)
    mix
  hashItem (bytesOfWords mix)

end EthLib.Cryptography.Ethash
