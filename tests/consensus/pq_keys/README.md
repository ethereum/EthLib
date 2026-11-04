# SSZ vectors of the post-quantum key registry

EIP-8450 adds the containers of a post-quantum key registry.
They hold the keys of a validator or builder, a registration, a proof of possession, and lists of these.
The EIP is a Draft and ships no test vectors, so the cases here are derived.

An independent SSZ implementation writes them: the Python package of the SSZ specification repository.

- Package: `eth-ssz-specs` 0.1.0 on PyPI
- Wheel sha256: `466c6cef854cca45022a7cdc3922dd636e30b1a1dd5385845819e3d45ddddf41`
- Repository: [`ethereum/ssz-specs`](https://github.com/ethereum/ssz-specs)
- Release: `v0.1.0`
- Commit: `7bce07ff7d51b1a3c66ff4e2bd3233ac248ede70`

`generate.py` defines each container as the EIP writes it, at the commit that `EthLib/Consensus/PqKeys/Containers.lean` cites.
It does not import EthLib.
Its inputs come from SHA-256 of fixed labels, so every run writes the same files:

```bash
uv run --no-project --python 3.12 --with eth-ssz-specs==0.1.0 \
  python -I tests/consensus/pq_keys/generate.py tests/consensus/pq_keys/ssz
```

Each case is a file `ssz/<container>/<case>/data.yaml`.
A valid case gives the bytes of a value and its hash tree root.
An invalid case gives bytes that encode no value of the container, and its root is `null`.
The package rejects each invalid case before the script writes it.

The list cases have lengths that cross the subtrees of a progressive list, which hold 1, 4, 16 and 64 chunks.

`bindings/python/tests/consensus/test_pq_keys.py` decodes each case in Lean, then checks the root and the bytes encoded again.
`SHA256SUMS` pins each file.
