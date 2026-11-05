"""
The Keccak team's Keccak-256, Keccak-512 and Keccak-f[1600] test vectors.

The Keccak-256 vectors are (message, digest) pairs:

- the byte-aligned cases of `kat/ShortMsgKAT_256.txt`, 256 vectors from 0 to 255 bytes;
- two cases of `LongMsgKAT_256.txt`, of 256 and 319 bytes, copied below;
- the message `abc`.

The Keccak-512 vectors are the byte-aligned cases of `kat/ShortMsgKAT_512.txt`, and the same two
long messages with the digests of `LongMsgKAT_512.txt`.

The permutation vectors are (input, output) pairs of 200-byte states, from
`kat/KeccakPermutationIntermediateValues.txt`.

The files are parsed at import time, so a parsing bug fails collection, not a single test.

No independent Keccak-256 is in the Python standard library, so the digests are the files' own.
"""

from itertools import pairwise
from pathlib import Path

# The vendored files sit next to this module.
_KAT_DIR = Path(__file__).resolve().parent / "kat"
_KAT_FILE = _KAT_DIR / "ShortMsgKAT_256.txt"
_KAT_512_FILE = _KAT_DIR / "ShortMsgKAT_512.txt"
_PERMUTATION_FILE = _KAT_DIR / "KeccakPermutationIntermediateValues.txt"


def _parse_kat(path: Path) -> list[tuple[str, bytes, bytes]]:
    """The (case name, message, digest) triples of the byte-aligned cases.

    Each case is three lines:

    ```text
    Len = 24        the message length, in bits
    Msg = 616263    the message, in hexadecimal
    MD = 4E03...    the digest, in hexadecimal
    ```

    A case whose length is not a whole number of bytes is skipped.
    """
    cases = []
    # The fields of the case being read, reset after each digest.
    len_bits: int | None = None
    msg_hex: str | None = None
    for line in path.read_text().splitlines():
        # Skip comments, headers and blank lines: they have no " = ".
        key, sep, value = line.partition(" = ")
        if not sep:
            continue
        key, value = key.strip(), value.strip()
        if key == "Len":
            len_bits = int(value)
        elif key == "Msg":
            msg_hex = value
        elif key == "MD":
            # The digest closes a case, so both other fields must be set.
            if len_bits is None or msg_hex is None:
                raise ValueError(f"{path.name}: MD without Len or Msg")
            if len_bits % 8 == 0:
                # Why truncate: the empty message is written as one placeholder byte.
                #
                #     Len = 0, Msg = 00  ->  message b""
                message = bytes.fromhex(msg_hex)[: len_bits // 8]
                cases.append((f"hash_case_short_len_{len_bits}", message, bytes.fromhex(value)))
            len_bits, msg_hex = None, None
    return cases


_CASES = _parse_kat(_KAT_FILE)

# Invariant: the file holds one byte-aligned case per byte length from 0 to 255.
assert [len(message) for _, message, _ in _CASES] == list(range(256)), "unexpected cases"

# `Len = 2048` and `Len = 2552` of `KeccakKAT/LongMsgKAT_256.txt`, in the same archive as
# `kat/ShortMsgKAT_256.txt`: two and three blocks.
#
# The file is 2.3 MB, so only these two cases are copied, as (case name, message, digest).
_LONG_CASES = [
    (
        "hash_case_long_len_2048",
        bytes.fromhex(
            "724627916C50338643E6996F07877EAFD96BDF01DA7E991D4155B9BE1295EA7D"
            "21C9391F4C4A41C75F77E5D27389253393725F1427F57914B273AB862B9E31DA"
            "BCE506E558720520D33352D119F699E784F9E548FF91BC35CA14704212870982"
            "0D69A8287EA3257857615EB0321270E94B84F446942765CE882B191FAEE7E1C8"
            "7E0F0BD4E0CD8A927703524B559B769CA4ECE1F6DBF313FDCF67C572EC4185C1"
            "A88E86EC11B6454B371980020F19633B6B95BD280E4FBCB0161E1A82470320CE"
            "C6ECFA25AC73D09F1536F286D3F9DACAFB2CD1D0CE72D64D197F5C7520B3CCB2"
            "FD74EB72664BA93853EF41EABF52F015DD591500D018DD162815CC993595B195"
        ),
        bytes.fromhex("EA0E416C0F7B4F11E3F00479FDDF954F2539E5E557753BD546F69EE375A5DE29"),
    ),
    (
        "hash_case_long_len_2552",
        bytes.fromhex(
            "3139840B8AD4BCD39092916FD9D01798FF5AA1E48F34702C72DFE74B12E98A11"
            "4E318CDD2D47A9C320FFF908A8DBC2A5B1D87267C8E983829861A567558B37B2"
            "92D4575E200DE9F1DE45755FAFF9EFAE34964E4336C259F1E66599A7C904EC02"
            "539F1A8EAB8706E0B4F48F72FEC2794909EE4A7B092D6061C74481C9E21B9332"
            "DC7C6E482D7F9CC3210B38A6F88F7918C2D8C55E64A428CE2B68FD07AB572A8B"
            "0A2388664F99489F04EB54DF1376271810E0E7BCE396F52807710E0DEA94EB49"
            "F4B367271260C3456B9818FC7A72234E6BF2205FF6A36546205015EBD7D8C252"
            "7AA430F58E0E8AC97A7B6B793CD403D517D66295F37A34D0B7D2FA7BC345AC04"
            "CA1E266480DEEC39F5C88641C9DC0BD1358158FDECDD96685BBBB5C1FE5EA89D"
            "2CB4A9D5D12BB8C893281FF38E87D6B4841F0650092D447E013F20EA934E18"
        ),
        bytes.fromhex("59E904B2AA0CCBF2A9D127446F113B7CC3D07B970E07A322325ECEE66AE0C9CA"),
    ),
]

# The three ASCII bytes `abc`, asked for by issue #64 because SHA3-256 gives them another digest.
#
# No Keccak team file holds this message, so the digest is not theirs.
_ABC_CASE = (
    "hash_case_abc",
    b"abc",
    bytes.fromhex("4E03657AEA45A94FC7D47BA826C8D667C0D1E6E33A64A036EC44F58FA12D6C45"),
)

_ALL_CASES = _CASES + _LONG_CASES + [_ABC_CASE]

# The case names, one output directory each.
CASE_NAMES: list[str] = [name for name, _, _ in _ALL_CASES]

# The (message, digest) pairs, in the same order as the names.
VECTORS: list[tuple[bytes, bytes]] = [(message, digest) for _, message, digest in _ALL_CASES]

_CASES_512 = _parse_kat(_KAT_512_FILE)

# Invariant: the file holds one byte-aligned case per byte length from 0 to 255.
assert [len(message) for _, message, _ in _CASES_512] == list(range(256)), "unexpected cases"

# The digests of the two long messages above, from `KeccakKAT/LongMsgKAT_512.txt`.
_LONG_DIGESTS_512 = {
    "hash_case_long_len_2048": bytes.fromhex(
        "4E987768469F546296AD1A43D54C0A0A6C87E7E4E26B686612B1E5B1554B689B"
        "FFD56D6A4B454CE4A5717625BBAD321F8D05F19C225259646F21416AA2D7C2ED"
    ),
    "hash_case_long_len_2552": bytes.fromhex(
        "3D370DC850BC7E159CEE3F24D9E915B5B1306FF403C32C7A3A3844F3FC8D90E3"
        "5F56D83BDD9C637BC45E440E1F27CCD56B6B3872EC19101BBE31845108DCE929"
    ),
}

_ALL_CASES_512 = _CASES_512 + [
    (name, message, _LONG_DIGESTS_512[name]) for name, message, _ in _LONG_CASES
]

# The Keccak-512 case names, one output directory each.
CASE_NAMES_512: list[str] = [name for name, _, _ in _ALL_CASES_512]

# The Keccak-512 (message, digest) pairs, in the same order as the names.
VECTORS_512: list[tuple[bytes, bytes]] = [(m, digest) for _, m, digest in _ALL_CASES_512]


def _parse_permutations(path: Path) -> list[tuple[bytes, bytes]]:
    """The (input, output) states of each example of the file.

    Each example gives its input and its output as one line of 200 bytes in hexadecimal:

    ```text
    Input of permutation:
    00 00 ... 00
    ...
    State after permutation:
    E7 DD ... 8B
    ```

    The lines between them, the values after each step, are skipped.
    """
    pairs = []
    lines = path.read_text().splitlines()
    state_in: bytes | None = None
    for label, value in pairwise(lines):
        if label.strip() == "Input of permutation:":
            state_in = bytes.fromhex(value)
        elif label.strip() == "State after permutation:":
            # An output closes an example, so its input must be set.
            if state_in is None:
                raise ValueError(f"{path.name}: output without input")
            pairs.append((state_in, bytes.fromhex(value)))
            state_in = None
    return pairs


# The all-zero state, then the output of the first example as the input of the second.
PERMUTATIONS: list[tuple[bytes, bytes]] = _parse_permutations(_PERMUTATION_FILE)

# Invariant: two examples of 200-byte states, the second starting where the first ends.
assert len(PERMUTATIONS) == 2, "unexpected examples"
assert all(len(a) == len(b) == 200 for a, b in PERMUTATIONS), "unexpected state size"
assert PERMUTATIONS[0][0] == bytes(200) and PERMUTATIONS[1][0] == PERMUTATIONS[0][1]

# The case names of the two examples.
PERMUTATION_NAMES: list[str] = ["permutation_zero", "permutation_zero_twice"]
