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
  A path that the package refuses has a `null` index and the name of the package's fault.
  When the fault names the step that it refused, the case gives that step too.
- `values` gives each value as its SSZ bytes, with its hash tree root.
  For every index below 32, for every index of a path of its type, and for the index 2^200, it gives the proof, or the fault that refuses the index.
- `chunk_roots` gives chunks and a limit, then their root, or the fault that refuses a limit below the number of chunks.

The cases cover empty lists, a list of limit 0, lists filled to a limit that is a power of two, and limits just below and above one.
They also cover the length node of a list, the index 0, the root, and indices into packed data, a length, an empty position and past the end of a progressive list.
A list of 2^64 chunks has element indices above 2^64 and proofs of 65 siblings, which no 64-bit integer holds.

No case goes past a chunk limit of 2^64, since the package roots an empty subtree of at most 2^64 leaves and refuses a larger limit.
No case has a negative position, index or limit, since the EthLib bindings refuse a negative integer before they call EthLib.

The test helpers of the consensus specification also have a chunk root function of their own, in `tests/core/pyspec/eth_consensus_specs/utils/merkle_minimal.py`.
That function gives the same root, or the same refusal, for every chunk case here.

`bindings/python/tests/ssz/test_ssz_proof_vectors.py` checks that EthLib gives each index, proof and root, and refuses each case that the package refuses.
It expects the whole message of EthLib for each fault of the package.
One wording differs: the package refuses a field name on a union as not a position, and EthLib as a missing field.
It reads each value from its bytes, and checks that EthLib gives each value the root of the file.

`SHA256SUMS` pins `cases.json` and `generate.py`.
