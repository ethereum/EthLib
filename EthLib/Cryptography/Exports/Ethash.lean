module

public import EthLib.Base.BigEndian
public import EthLib.Base.Exports
public import EthLib.Cryptography.Ethash

/-!
# Exports: Ethash

The C exports of the sizes, the seed, the cache and the dataset items of Ethash.

A number crosses the boundary as its big-endian bytes.

A cache crosses it as its items in order, 64 bytes each.

A dataset item needs a cache of at least one item, and the export rejects any other with code 0.

The proof-of-work function also rejects, with code 0, a header hash or a nonce of the wrong size.
-/

public section

namespace EthLib.Cryptography.Ethash.Exports

open EthLib.Base (bytesToNat natToBytes)
open EthLib.Exports (Result)

/-- The number that big-endian bytes encode. -/
def numberOf (bytes : ByteArray) : Nat :=
  bytesToNat bytes.toList

/-- The shortest big-endian bytes of a number, one byte for 0. -/
def bytesOfNumber (n : Nat) : ByteArray :=
  ⟨(natToBytes (n.log2 / 8 + 1) n).toArray⟩

/-- The bytes of a cache: its items in order, 64 bytes each. -/
def bytesOfCache (c : Array Item) : ByteArray :=
  c.foldl (fun out item => out ++ bytesOfWords item) ByteArray.empty

/-- The cache that bytes spell, 64 bytes per item. -/
def cacheOfBytes (bytes : ByteArray) : Result (Array Item) := do
  if bytes.size = 0 ∨ bytes.size % HASH_BYTES ≠ 0 then
    throw (0, s!"Ethash: a cache is a positive multiple of 64 bytes, got {bytes.size}")
  let data := bytes.data
  pure <| Array.ofFn fun i : Fin (bytes.size / HASH_BYTES) =>
    itemOfBytes (Vector.ofFn fun k : Fin 64 => data.getD (HASH_BYTES * i.val + k.val) 0)

/-- The bytes in the cache of the epoch of a block. -/
@[export eth_ethash_cache_size]
def cacheSizeExport (number : ByteArray) : ByteArray :=
  bytesOfNumber (cacheSize (numberOf number))

/-- The bytes in the dataset of the epoch of a block. -/
@[export eth_ethash_dataset_size]
def datasetSizeExport (number : ByteArray) : ByteArray :=
  bytesOfNumber (datasetSize (numberOf number))

/-- The 32-byte seed of the epoch of a block. -/
@[export eth_ethash_seed]
def seedExport (number : ByteArray) : ByteArray :=
  seed (numberOf number)

/-- The cache of the epoch of a block, its items in order, 64 bytes each. -/
@[export eth_ethash_cache]
def cacheExport (number : ByteArray) : ByteArray :=
  bytesOfCache (cache (numberOf number))

/-- The 64-byte dataset item at an index, from a cache given as its bytes. -/
@[export eth_ethash_dataset_item]
def datasetItemExport (cacheBytes index : ByteArray) : Result ByteArray := do
  let c ← cacheOfBytes cacheBytes
  pure (bytesOfWords (datasetItem c (numberOf index)))

/-- The 32-byte mix digest and the 32-byte result of the proof-of-work function, from a cache.

The header hash must be 32 bytes and the nonce 8 bytes. -/
@[export eth_ethash_hashimoto_light]
def hashimotoLightExport (datasetSize cacheBytes headerHash nonce : ByteArray) :
    Result ByteArray := do
  let c ← cacheOfBytes cacheBytes
  if headerHash.size ≠ 32 then
    throw (0, s!"Ethash: a header hash is 32 bytes, got {headerHash.size}")
  if nonce.size ≠ 8 then
    throw (0, s!"Ethash: a nonce is 8 bytes, got {nonce.size}")
  let out := hashimotoLight (numberOf datasetSize) c headerHash nonce
  pure (out.mixDigest ++ out.result)

end EthLib.Cryptography.Ethash.Exports
