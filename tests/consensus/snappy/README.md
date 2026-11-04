# Snappy files of consensus-spec-tests

The consensus test release compresses every SSZ file as a Snappy block.
The files here are 50 of them, copied byte for byte from `mainnet.tar.gz` under their path in the archive.

- Repository: [`ethereum/consensus-specs`](https://github.com/ethereum/consensus-specs)
- Release: `v1.7.0-beta.4`
- Commit: `aa16bb4c156184e9548a997d53efaf2a228a6304`
- Archive: `mainnet.tar.gz`, whose digest `tests/consensus/README.md` records
- Licence: CC0 1.0

The archive holds 30,914 such files from Phase 0 to Fulu.
The 50 here are chosen by size, in the order of their size and then their path:

- 48 of the 22,455 files below 100,000 bytes, at evenly spaced ranks;
- the smallest file of at least 100,000 bytes, a blob;
- the largest file of at most 200,000 bytes, a beacon state of about 2.8 MB.

The test `bindings/python/tests/snappy/test_consensus_spec_tests.py` decompresses each file.
It compares the size and the sha256 of the data with those that cramjam 2.11.0, an independent Snappy implementation, gives.
`SHA256SUMS` pins each file.
