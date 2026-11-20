# SSZ vectors of generalized indices, Merkle proofs and chunk roots

A light client proves one field of a large SSZ value with a Merkle proof.
It needs three operations for that.
The first gives the generalized index of a path, which names one node of the value's tree.
The second gives the proof of a generalized index: the siblings of every node from that node up to the root, bottom first.
The third gives the root of a list of 32-byte chunks, padded with zero chunks to a power of two at least a limit.

The cases here give the answer of an independent SSZ implementation for each operation.
That implementation is the Python package of the SSZ specification repository.
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
  A path that the package refuses has a `null` index, the name of the package's fault, and the step that it refused.
- `values` gives each value as its SSZ bytes, with its hash tree root.
  For every index below 32, and for every index of a path of its type, it gives the proof, or the fault that refuses the index.
- `chunk_roots` gives chunks and a limit, then their root, or the fault that refuses a limit below the number of chunks.

The cases cover empty lists, lists filled to a limit that is a power of two, and limits just below and above one.
They also cover a length below a list, the index 0, the root, and indices into packed data, a length, an empty position and past the end of a progressive list.

The consensus specification computes chunk roots with a function of its own, not with this package.
That function gives the same root, or the same refusal, for every chunk case here.

`bindings/python/tests/ssz/test_ssz_proof_vectors.py` checks that EthLib gives each index, proof and root, and refuses each case that the package refuses.
It reads each value from its bytes, and first checks that EthLib gives the value the root of the file.

`SHA256SUMS` pins each file.
