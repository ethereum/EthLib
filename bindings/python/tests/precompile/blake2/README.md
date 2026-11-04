# BLAKE2b known answers

The BLAKE2b entries of the BLAKE2 known answers.

- File excerpted: `testvectors/blake2-kat.json`, sha256 `5031ac14800798ae15cee79c04d65e326a575f2c968c7e2846a79bd07a1c0e61`, as `blake2b-kat.jsonl`
- Repository: [`BLAKE2/BLAKE2`](https://github.com/BLAKE2/BLAKE2)
- Commit: `ed1974ea83433eba7b2d95c5dcd9ac33cb847913`
- Licence: CC0 1.0 (`COPYING`), one of the three licences the repository offers

`SHA256SUMS` pins both files.

The file holds 3072 known answers for six BLAKE2 functions.
The precompile is the compression function of BLAKE2b, so only the 512 BLAKE2b entries are kept, one JSON object per line.
They hash the messages of 0 to 255 bytes, first without a key, then with a 64-byte key.
This command makes the excerpt again from the file in the repository:

```text
jq -c '.[] | select(.hash == "blake2b")' blake2-kat.json > blake2b-kat.jsonl
```
