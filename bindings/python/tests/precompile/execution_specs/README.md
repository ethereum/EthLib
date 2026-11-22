# Precompile cases of execution-specs

The ECRECOVER and alt_bn128 cases that the precompile tests read, taken from the test files of execution-specs.

- Repository: [`ethereum/execution-specs`](https://github.com/ethereum/execution-specs)
- Commit: `391d8a05d5cb182542ac7e7330c858b6ee03f990`
- Licence: CC0-1.0

`SHA256SUMS` pins both files.

The repository holds these cases as `pytest.param` lists in Python test files, not as vector files.
So each file here was written from those lists, without running the tests:

- `ecrecover_cases.json` holds the 52 cases of `test_precompiles` in `tests/frontier/precompiles/test_ecrecover.py`.
  Each case joins the four words of the call, `hash || v || r || s`, into one 128-byte input.
- `alt_bn128_cases.json` holds the 371 cases of the EIP-196 and EIP-197 tests in `tests/byzantium`.
  `extract_alt_bn128_cases.py` writes it again from that directory, byte for byte:

```text
python -I extract_alt_bn128_cases.py <execution-specs>/tests/byzantium alt_bn128_cases.json
```
