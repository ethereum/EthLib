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

/-- The 32 words of the mix compressed to 8, each FNV folded over 4 consecutive words.

The appendix writes a compression whose indices do not match the clients.

The definition follows the specification. -/
def compress (mix : Vector UInt32 32) : Vector UInt32 8 :=
  -- For `k < 8`, word `k` is FNV folded from the left over words `4 k` to `4 k + 3` of the mix.
  Vector.ofFn fun k : Fin 8 =>
    fnv (fnv (fnv mix[4 * k.val] mix[4 * k.val + 1]) mix[4 * k.val + 2]) mix[4 * k.val + 3]

/-- The proof-of-work function from a cache: `PoW` of the Yellow Paper, J.4.

The header hash is the Keccak-256 hash of the header without its mix digest and nonce.

The nonce is 8 bytes, the most significant first, and the seed reads them reversed.

The dataset size fixes the count of pairs of items that an access can choose. -/
def hashimotoLight (datasetSize : Nat) (cache : Array Item) (headerHash nonce : ByteArray) :
    PowOutput :=
  -- `s` is the Keccak-512 digest of the header hash and of the nonce with its bytes reversed.
  let s := hashItem (headerHash ++ ⟨nonce.data.reverse⟩)
  -- The dataset has one item per 64 bytes, so one pair of adjacent items per 128 bytes.
  let pairs := datasetSize / MIX_BYTES
  -- The 64 accesses, for `i < 64`.
  let mix := (List.range ACCESSES).foldl
    (fun mix i =>
      -- Access `i` picks the pair `p = FNV(i ⊕ s_0, mix_(i mod 32))` mod the number of pairs.
      --
      -- Here `p` counts pairs, so the items read are `2 p` and `2 p + 1`.
      let p := (fnv (i.toUInt32 ^^^ s[0]) mix[i % 32]).toNat % pairs
      -- Word `w` of the mix becomes `FNV(mix_w, d_w)`, with `d` item `2 p` then item `2 p + 1`.
      --
      -- Each item is computed from the cache, as a verifier without the dataset does.
      Vector.zipWith fnv mix (datasetItem cache (2 * p) ++ datasetItem cache (2 * p + 1)))
    -- The mix starts as `s` twice, 32 words.
    (s ++ s)
  -- The mix digest is the compressed mix, 4 bytes per word, the least significant first.
  let mixDigest := bytesOfWords (compress mix)
  -- The result is the Keccak-256 digest of `s` and the mix digest.
  ⟨mixDigest, ⟨(keccak256 (bytesOfWords s ++ mixDigest)).toArray⟩⟩

end EthLib.Cryptography.Ethash
