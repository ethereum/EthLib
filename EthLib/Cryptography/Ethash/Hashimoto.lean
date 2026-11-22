module

public import EthLib.Cryptography.Ethash.Cache

/-!
# `Ethash.Hashimoto`

The proof-of-work function of Ethash, from a cache: the hashimoto loop.

Each of 64 accesses folds two adjacent dataset items into a 128-byte mix with FNV.

The seed and the mix choose the items, so a miner cannot know them in advance.

A verifier computes the 128 dataset items from the cache, without the dataset.

Appendix J.4 of the Yellow Paper, Berlin version, defines the function: [`Paper.tex`][yp].

Its compression formula reads its indices differently from every client and from the tests.

There the definition follows the Ethash specification of the Ethereum Foundation: [Ethash][ethash].

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
[ethash]: https://github.com/ethereum/ethereum-org-website/blob/0899bcb4dcb12040ccf46bea0053a422812bf913/public/content/developers/docs/consensus-mechanisms/pow/mining/mining-algorithms/ethash/index.md
-/

@[expose] public section

namespace EthLib.Cryptography.Ethash

open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- The output of the proof-of-work function: the mix digest and the result, 32 bytes each. -/
structure PowOutput where
  /-- The compressed mix: 8 words of FNV over groups of 4 words of the mix. -/
  mixDigest : ByteArray
  /-- The Keccak-256 hash of the seed and the mix digest, compared with the target. -/
  result : ByteArray

/-- The 32 words of the mix compressed to 8: `fnv(fnv(fnv(m[4k], m[4k+1]), m[4k+2]), m[4k+3])`.

The appendix writes a compression whose indices do not match the clients.

The definition follows the specification. -/
def compress (mix : Vector UInt32 32) : Vector UInt32 8 :=
  -- `for i in range(0, len(mix), 4)`, with `i = 4 k`.
  --
  -- `cmix.append(fnv(fnv(fnv(mix[i], mix[i+1]), mix[i+2]), mix[i+3]))`.
  Vector.ofFn fun k : Fin 8 =>
    fnv (fnv (fnv mix[4 * k.val] mix[4 * k.val + 1]) mix[4 * k.val + 2]) mix[4 * k.val + 3]

/-- The proof-of-work function from a cache: `PoW` of the Yellow Paper, J.4.

The header hash is the Keccak-256 hash of the header without its mix digest and nonce.

The nonce is 8 bytes, the most significant first, and the seed reads them reversed.

The dataset size fixes the count of pairs of items that an access can choose. -/
def hashimotoLight (datasetSize : Nat) (cache : Array Item) (headerHash nonce : ByteArray) :
    PowOutput :=
  -- `s = sha3_512(header + nonce[::-1])`.
  let s := hashItem (headerHash ++ ⟨nonce.data.reverse⟩)
  -- `n // mixhashes`, with `n = full_size / HASH_BYTES` and `mixhashes = 2`.
  let pairs := datasetSize / MIX_BYTES
  -- `for i in range(ACCESSES)`.
  let mix := (List.range ACCESSES).foldl
    (fun mix i =>
      -- `p = fnv(i ^ s[0], mix[i % w]) % (n // mixhashes) * mixhashes`, with `w = 32`.
      --
      -- Here `p` counts pairs, so the items read are `2 p` and `2 p + 1`.
      let p := (fnv (i.toUInt32 ^^^ s[0]) mix[i % 32]).toNat % pairs
      -- `mix = map(fnv, mix, newdata)`, with `newdata` the items `2 p + j` for `j < 2`.
      --
      -- `dataset_lookup(x)` is `calc_dataset_item(cache, x)`, as in `hashimoto_light`.
      Vector.zipWith fnv mix (datasetItem cache (2 * p) ++ datasetItem cache (2 * p + 1)))
    -- `mix.extend(s)` twice: the mix starts as `s` replicated.
    (s ++ s)
  -- `"mix digest": serialize_hash(cmix)`.
  let mixDigest := bytesOfWords (compress mix)
  -- `"result": serialize_hash(sha3_256(s+cmix))`.
  ⟨mixDigest, ⟨(keccak256 (bytesOfWords s ++ mixDigest)).toArray⟩⟩

end EthLib.Cryptography.Ethash
