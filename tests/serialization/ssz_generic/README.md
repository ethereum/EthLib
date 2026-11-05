# The ssz_generic vectors of consensus-spec-tests

The files here are the generic SSZ vectors of the consensus specification tests.

- Repository: [`ethereum/consensus-specs`](https://github.com/ethereum/consensus-specs)
- Release: `v1.7.0-alpha.13`, the last release that ships the suite
- Archive: `general.tar.gz`
- Archive sha256: `b98e5328037a84993254085700b8d9eae304beca81d0944fe05274ca3523ed8b`
- Files: every file of eight handlers under `tests/general/phase0/ssz_generic/`, copied without change
- Cases: 3,919, of which 1,984 valid and 1,935 invalid
- Licence: CC0 1.0

The repository pins a later release of consensus-specs for its other vectors.
That release has no `ssz_generic`, so the archive above is the source of these files.
The release `v1.7.0-alpha.12` holds the same files, byte for byte.

The eight handlers are `basic_progressive_list`, `basic_vector`, `bitlist`, `bitvector`, `boolean`, `compatible_unions`, `progressive_bitlist` and `uints`.

The handlers `containers` and `progressive_containers` are not vendored.
They hold 260 MB, too much to vendor.
The same test reads them from the pinned archive `consensus-specs/v1.7.0-alpha.12/general` of `tests/sources.toml`, in the weekly run of the archive tests.
They hold 1,226 cases, of which 724 valid and 502 invalid.

A valid case gives a value, its SSZ bytes compressed as a Snappy block, and its hash tree root.
An invalid case gives only bytes that no value of the type has.
The name of a case declares its type, by the templates of the format of the suite.

The test `bindings/python/tests/ssz/test_ssz_generic.py` reads these files and never rewrites them.
`SHA256SUMS` pins each file.
