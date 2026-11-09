# ERC-2335 keystore and Unicode vectors

`scrypt.json` and `pbkdf2.json` are the two keystores from ERC-2335 at ethereum/ERCs commit `be307c948f28897adb8f25afcc253c2c909de35d`.
Their password is `𝔱𝔢𝔰𝔱𝔭𝔞𝔰𝔰𝔴𝔬𝔯𝔡🔑`, whose prepared bytes are `0x7465737470617373776f7264f09f9491`.
Both decrypt to `0x000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f`.
The ERC material is CC0.

`unicode/UnicodeData.txt` and `unicode/NormalizationTest.txt` are the unmodified Unicode Character Database 16.0.0 files from <https://www.unicode.org/Public/16.0.0/ucd/>.
The data and the generated Lean table retain the Unicode License V3 in `unicode/LICENSE` and `EthLib/Base/Unicode/LICENSE`.
`SHA256SUMS` pins the downloaded bytes.

The Python suite checks all five NFKD column relations in `NormalizationTest.txt`.
It also checks the file's identity rule for assigned Unicode scalar values absent from Part 1.
The keystore tests run both ERC vectors through the bindings.

To regenerate the Lean normalization table from the pinned data:

```bash
uv run --no-project --python 3.12 python scripts/generate_unicode_nfkd.py
```

With `--check`, the command checks the table without writing it.
