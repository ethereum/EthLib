module

public import EthLib.Base.Exports.Proofs.PyValue
public import EthLib.Cryptography.Ethash

/-!
# Exports: Ethash

The C exports of the sizes, the seed, the cache and the dataset items of Ethash.

Their arguments and results are typed Python values, and a number crosses as an `int`.

A cache crosses the boundary as its items in order, 64 bytes each.

An argument of the wrong type fails with code 0.

A dataset item needs a cache of at least one item, and the export rejects any other with code 0.

The proof-of-work function also rejects, with code 0, a header hash or a nonce of the wrong size.
-/

public section

namespace EthLib.Cryptography.Ethash.Exports

open EthLib.Exports (Result PyValue pyExport)

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
def cacheSizeExport (args : PyValue) : Result PyValue :=
  pyExport (fun number => pure (cacheSize number)) args

/-- The bytes in the dataset of the epoch of a block. -/
@[export eth_ethash_dataset_size]
def datasetSizeExport (args : PyValue) : Result PyValue :=
  pyExport (fun number => pure (datasetSize number)) args

/-- The 32-byte seed of the epoch of a block. -/
@[export eth_ethash_seed]
def seedExport (args : PyValue) : Result PyValue :=
  pyExport (fun number => pure (seed number)) args

/-- The cache of the epoch of a block, its items in order, 64 bytes each. -/
@[export eth_ethash_cache]
def cacheExport (args : PyValue) : Result PyValue :=
  pyExport (fun number => pure (bytesOfCache (cache number))) args

/-- The 64-byte dataset item at an index, from a cache given as its bytes. -/
def datasetItemOf (args : ByteArray × Nat) : Result ByteArray := do
  let (cacheBytes, index) := args
  let c ← cacheOfBytes cacheBytes
  pure (bytesOfWords (datasetItem c index))

/-- The 64-byte dataset item at an index, from a cache given as its bytes.

The arguments are the cache and the index, and a cache of the wrong size fails with code 0. -/
@[export eth_ethash_dataset_item]
def datasetItemExport (args : PyValue) : Result PyValue :=
  pyExport datasetItemOf args

/-- The 32-byte mix digest and the 32-byte result of the proof-of-work function, from a cache.

The arguments are the size of the dataset, the cache, the header hash and the nonce.

The header hash must be 32 bytes and the nonce 8 bytes. -/
def hashimotoLightOf (args : Nat × ByteArray × ByteArray × ByteArray) :
    Result (ByteArray × ByteArray) := do
  let (datasetSize, cacheBytes, headerHash, nonce) := args
  let c ← cacheOfBytes cacheBytes
  if headerHash.size ≠ 32 then
    throw (0, s!"Ethash: a header hash is 32 bytes, got {headerHash.size}")
  if nonce.size ≠ 8 then
    throw (0, s!"Ethash: a nonce is 8 bytes, got {nonce.size}")
  let out := hashimotoLight datasetSize c headerHash nonce
  pure (out.mixDigest, out.result)

/-- The 32-byte mix digest and the 32-byte result of the proof-of-work function, from a cache.

The arguments are the size of the dataset, the cache, the header hash and the nonce.

The result is the pair of the mix digest and the result, and a wrong size fails with code 0. -/
@[export eth_ethash_hashimoto_light]
def hashimotoLightExport (args : PyValue) : Result PyValue :=
  pyExport hashimotoLightOf args

end EthLib.Cryptography.Ethash.Exports
