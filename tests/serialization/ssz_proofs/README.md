# SSZ vectors of generalized indices, Merkle proofs and chunk roots

A light client proves one field of a large SSZ value with a Merkle proof.
It needs three operations for that.
The first gives the generalized index of a path, which names one node of the value's tree.
The second gives the proof of a generalized index: the siblings of every node from that node up to the root, bottom first.
The third gives the root of a list of 32-byte chunks, padded with zero chunks to the next power of two.
With a limit, it pads to the next power of two at least the limit instead.

The cases here give the answer of the SSZ specification for each operation.
That specification is the Python package of the SSZ specification repository, which EthLib does not import.
The consensus specification at the commit that `tests/sources.toml` pins takes its generalized indices and proofs from this package, version 0.1.0.

- Package: `eth-ssz-specs` 0.1.0 on PyPI
- Wheel sha256: `466c6cef854cca45022a7cdc3922dd636e30b1a1dd5385845819e3d45ddddf41`
- Repository: [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs)
- Release: `v0.1.0`
- Commit: `7bce07ff7d51b1a3c66ff4e2bd3233ac248ede70`

`generate.py` does not import EthLib, and every run writes the same file:

```bash
uv run --no-project --python 3.12 --with eth-ssz-specs==0.1.0 \
  python -I tests/serialization/ssz_proofs/generate.py tests/serialization/ssz_proofs
```

`cases.json` holds four tables.

- `types` names each type and gives it in the form that the EthLib bindings read.
  The script derives that form from the class that the package uses.
- `generalized_indices` gives a type and a path, then the index of the path.
  A path holds field names, positions and the mixed-in words `__len__`, `__active_fields__` and `__selector__`.
  Each case gives `type`, `path` and `gindex`.
  A path that the package refuses has a `null` index and the name of the package's fault in `fault`.
  When the fault names the step that it refused, the case gives that step in `step`.
- `values` gives each value as its SSZ bytes, with its hash tree root.
  It asks the proof of every index below 32, of every index of a path of its type, and of the index 2^200.
  For the list of 2^64 chunks, it also asks the index 2^66, inside packed data.
  Each proof gives `gindex`, then `branch` and the node `leaf` that the branch proves.
  For an index that the package refuses, it has a `null` branch and gives `fault` instead of `leaf`, with `index` where the fault names it.
- `chunk_roots` gives `chunks` and `limit`, then their `root`.
  A limit below the number of chunks has a `null` root, the `fault`, and the `count` of chunks.

The cases cover empty lists, a list of limit 0, lists filled to a limit that is a power of two, and limits just below and above one.
They also cover the length node of a list, the index 0 and the root.
Other indices go into packed data, into a length, into an empty position, and past the end of a progressive list.
Lists of 2^64 and 2^65 chunks have element indices above 2^64, which no 64-bit integer holds.
Their proofs hold 65 and 66 siblings, and the chunk roots go up to a limit of 2^65.

The package roots a zero subtree of at most 2^64 leaves.
So it refuses a limit past 2^64 for empty or zero chunks, and any limit past 2^65, where EthLib gives a root.
No case has such a limit.
No case has a negative position, index or limit, since the EthLib bindings refuse a negative integer before they call EthLib.

`bindings/python/tests/ssz/test_ssz_proof_vectors.py` checks that EthLib gives each index, proof and root, and refuses each case that the package refuses.
It expects the whole message and the code of EthLib for each fault of the package.
EthLib refuses a field name on a type that the path reaches and that is not a container as a missing field, with code 0.
The package calls it not a position on any other composite type, and a value with no parts on a basic value.
The test expects the message of EthLib in each of these cases.
It reads each value from its bytes, and checks that EthLib gives each value the root of the file.
It also hashes each branch of the file up from its node, and checks that it reaches the root of the value.

`SHA256SUMS` pins `cases.json` and `generate.py`.
