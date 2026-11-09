"""ERC-2335 vectors, Unicode 16.0.0 NFKD conformance and malformed keystores."""

import hashlib
import json
from pathlib import Path

import pytest

from ethlib.cryptography import keystore
from ethlib.errors import KeystoreError
from raising import raises

ROOT = Path(__file__).resolve().parents[4] / "tests/cryptography/keystore"
PASSWORD = "𝔱𝔢𝔰𝔱𝔭𝔞𝔰𝔰𝔴𝔬𝔯𝔡🔑"
SECRET = bytes.fromhex("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f")


def normalization_rows() -> list[list[str]]:
    """Read the five columns of the pinned NormalizationTest.txt."""
    rows = []
    for line in (ROOT / "unicode/NormalizationTest.txt").read_text().splitlines():
        data = line.split("#")[0].strip()
        if data and not data.startswith("@"):
            rows.append(
                [
                    "".join(chr(int(code, 16)) for code in field.split())
                    for field in data.split(";")[:5]
                ]
            )
    return rows


@pytest.mark.parametrize("column", range(5))
def test_nfkd_conformance(column: int) -> None:
    # UAX15-C3 and the file header require every column to normalize to column 5.
    for index, row in enumerate(normalization_rows()):
        assert keystore.nfkd(row[column]) == row[4], (index, column)


def test_nfkd_unlisted_identity() -> None:
    # Part 2 of the conformance header covers assigned code points absent from Part 1.
    listed = set()
    part_one = False
    for line in (ROOT / "unicode/NormalizationTest.txt").read_text().splitlines():
        data = line.split("#")[0].strip()
        if data.startswith("@"):
            part_one = data.startswith("@Part1")
        elif part_one and data:
            listed.add(int(data.split(";")[0], 16))
    pending = None
    batch = []
    for line in (ROOT / "unicode/UnicodeData.txt").read_text().splitlines():
        fields = line.split(";")
        code = int(fields[0], 16)
        if fields[1].endswith(", First>"):
            pending = code
            continue
        if fields[1].endswith(", Last>"):
            assert pending is not None
            codes = range(pending, code + 1)
        else:
            codes = [code]
        pending = None
        for scalar in codes:
            if scalar in listed or 0xD800 <= scalar <= 0xDFFF:
                continue
            # A class-zero separator prevents ordering between adjacent test cases.
            batch.append(chr(scalar) + "\0")
            if len(batch) == 4096:
                text = "".join(batch)
                assert keystore.nfkd(text) == text
                batch.clear()
    text = "".join(batch)
    assert keystore.nfkd(text) == text


def test_password_preparation() -> None:
    assert keystore.password_bytes(PASSWORD) == bytes.fromhex("7465737470617373776f7264f09f9491")
    controls = "".join(chr(code) for code in [*range(0x20), *range(0x7F, 0xA0)])
    assert keystore.password_bytes(controls + " pass word " + controls) == b" pass word "
    assert keystore.nfkd("\u0301\u0323a\u0301\u0323") == "\u0323\u0301a\u0323\u0301"
    assert keystore.nfkd("a\u0301\u0300") == "a\u0301\u0300"


@pytest.mark.parametrize("name", ["pbkdf2", "scrypt"])
def test_erc2335(name: str) -> None:
    # ethereum/ERCs at be307c948f28897adb8f25afcc253c2c909de35d, ERC-2335 Test Cases.
    assert keystore.decrypt((ROOT / f"{name}.json").read_text(), PASSWORD) == SECRET


def empty_store() -> dict:
    """A small authenticated empty secret, with an independent hashlib checksum."""
    key = hashlib.pbkdf2_hmac("sha256", b"password", b"salt", 1, 32)
    return {
        "crypto": {
            "kdf": {
                "function": "pbkdf2",
                "params": {"dklen": 32, "c": 1, "prf": "hmac-sha256", "salt": b"salt".hex()},
                "message": "",
            },
            "checksum": {
                "function": "sha256",
                "params": {},
                "message": hashlib.sha256(key[16:32]).hexdigest(),
            },
            "cipher": {"function": "aes-128-ctr", "params": {"iv": "00" * 16}, "message": ""},
        },
        "path": "",
        "uuid": "64625def-3331-4eea-ab6f-782f3ed16a83",
        "version": 4,
    }


def test_empty_secret_and_long_key() -> None:
    store = empty_store()
    assert keystore.decrypt(json.dumps(store), "password") == b""
    store["crypto"]["kdf"]["params"]["dklen"] = 64
    assert keystore.decrypt(json.dumps(store), "password") == b""


@pytest.mark.parametrize("change", ["password", "checksum", "ciphertext"])
def test_checksum_rejection(change: str) -> None:
    store = empty_store()
    password = "password"
    if change == "password":
        password = "wrong"
    elif change == "checksum":
        store["crypto"]["checksum"]["message"] = "00" * 32
    else:
        store["crypto"]["cipher"]["message"] = "00"
    with raises(
        KeystoreError, "EthLib.Cryptography.Keystore.KeystoreError.checksumMismatch"
    ) as exc:
        keystore.decrypt(json.dumps(store), password)
    assert exc.value.code == 8


@pytest.mark.parametrize(
    "path, value, message, code",
    [
        (["version"], 3, "unsupportedVersion 3", 3),
        (["crypto", "kdf", "params", "dklen"], 16, "shortKey 16", 5),
        (
            ["crypto", "kdf", "params", "c"],
            0,
            "pbkdf2 (EthLib.Cryptography.Hash.Pbkdf2.Pbkdf2Error.zeroIterations)",
            6,
        ),
        (
            ["crypto", "kdf", "params", "prf"],
            "hmac-sha512",
            'unsupportedFunction "kdf.prf" "hmac-sha512"',
            4,
        ),
        (
            ["crypto", "checksum", "function"],
            "keccak256",
            'unsupportedFunction "checksum" "keccak256"',
            4,
        ),
        (
            ["crypto", "cipher", "function"],
            "aes-256-ctr",
            'unsupportedFunction "cipher" "aes-256-ctr"',
            4,
        ),
        (
            ["crypto", "cipher", "params", "iv"],
            "00",
            'invalidField "cipher.iv" "expected 16 bytes"',
            2,
        ),
        (
            ["crypto", "kdf", "params", "salt"],
            "0",
            'invalidField "kdf.salt" "odd number of hex digits"',
            2,
        ),
        (
            ["crypto", "cipher", "message"],
            "gg",
            'invalidField "cipher.message" "not a hex digit"',
            2,
        ),
        (
            ["crypto", "checksum", "message"],
            "00",
            'invalidField "checksum.message" "expected 32 bytes"',
            2,
        ),
        (["crypto", "cipher", "params"], [], 'invalidField "cipher.params" "object expected"', 2),
        (["path"], None, 'invalidField "path" "String expected"', 2),
    ],
)
def test_invalid_fields(path: list[str], value: object, message: str, code: int) -> None:
    store = empty_store()
    parent = store
    for name in path[:-1]:
        parent = parent[name]
    parent[path[-1]] = value
    with raises(KeystoreError, "EthLib.Cryptography.Keystore.KeystoreError." + message) as exc:
        keystore.decrypt(json.dumps(store), "password")
    assert exc.value.code == code


def test_scrypt_parameter_error() -> None:
    store = empty_store()
    store["crypto"]["kdf"] = {
        "function": "scrypt",
        "params": {"dklen": 32, "n": 3, "r": 1, "p": 1, "salt": ""},
        "message": "",
    }
    with raises(
        KeystoreError,
        "EthLib.Cryptography.Keystore.KeystoreError.scrypt "
        "(EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidCost 3)",
    ) as exc:
        keystore.decrypt(json.dumps(store), "password")
    assert exc.value.code == 7


def test_required_module_field() -> None:
    store = empty_store()
    del store["crypto"]["kdf"]["message"]
    with raises(
        KeystoreError,
        'EthLib.Cryptography.Keystore.KeystoreError.invalidField "kdf.message" '
        '"property not found: message"',
    ):
        keystore.decrypt(json.dumps(store), "password")


def test_unsupported_kdf_before_parameters() -> None:
    store = empty_store()
    store["crypto"]["kdf"]["function"] = "argon2id"
    store["crypto"]["kdf"]["params"] = {}
    with raises(
        KeystoreError,
        'EthLib.Cryptography.Keystore.KeystoreError.unsupportedFunction "kdf" "argon2id"',
    ) as exc:
        keystore.decrypt(json.dumps(store), "password")
    assert exc.value.code == 4


def test_uppercase_hex() -> None:
    store = empty_store()
    store["crypto"]["checksum"]["message"] = store["crypto"]["checksum"]["message"].upper()
    assert keystore.decrypt(json.dumps(store), "password") == b""


def sha_blocks(size: int) -> int:
    """SHA-256 compressions for a message of this many bytes, FIPS 180-4 padding included."""
    return -(-(size + 9) // 64)


def hmac_blocks(key: int, message: int) -> int:
    """SHA-256 compressions of one RFC 2104 HMAC call, from the key and message sizes."""
    return (sha_blocks(key) if key > 64 else 0) + sha_blocks(64 + message) + sha_blocks(96)


def pbkdf2_blocks(password: int, salt: int, iterations: int, length: int) -> int:
    """SHA-256 compressions of RFC 8018 PBKDF2: U_1 on the salt and index, then U_2 to U_c."""
    per_block = hmac_blocks(password, salt + 4) + (iterations - 1) * hmac_blocks(password, 32)
    return -(-length // 32) * per_block


def scrypt_cost(password: int, salt: int, n: int, r: int, p: int, dklen: int) -> tuple[int, int]:
    """Memory and work of RFC 7914 scrypt: its buffers, then Salsa20/8 cores and PBKDF2 blocks."""
    memory = 128 * r * (n + 2 * p) + dklen
    work = (
        4 * n * r * p
        + pbkdf2_blocks(password, salt, 1, 128 * r * p)
        + pbkdf2_blocks(password, 128 * r * p, 1, dklen)
    )
    return memory, work


@pytest.mark.parametrize(
    "name, memory, work",
    [
        # c = 262144 with a 16-byte password, a 32-byte salt and one block: four compressions each.
        ("pbkdf2", 32, 4 * 262144),
        # n = 262144, r = 8, p = 1: the table, two buffers and the key take the memory.
        # Work: the Salsa20/8 cores, 32 expansion blocks of 4, and 20 over the 1024-byte blocks.
        ("scrypt", 128 * 8 * (262144 + 2) + 32, 4 * 262144 * 8 + 32 * 4 + 20),
    ],
)
def test_erc2335_limits(name: str, memory: int, work: int) -> None:
    if name == "scrypt":
        assert scrypt_cost(16, 32, 262144, 8, 1, 32) == (memory, work)
    else:
        assert pbkdf2_blocks(16, 32, 262144, 32) == work
    text = (ROOT / f"{name}.json").read_text()
    assert keystore.decrypt(text, PASSWORD, max_memory=memory, max_work=work) == SECRET
    for max_memory, max_work in [(memory - 1, work), (memory, work - 1)]:
        with raises(
            KeystoreError,
            f"EthLib.Cryptography.Keystore.KeystoreError.limitExceeded {memory} {work}",
        ) as exc:
            keystore.decrypt(text, PASSWORD, max_memory=max_memory, max_work=max_work)
        assert exc.value.code == 9


def scrypt_store(n: int, r: int, p: int, dklen: int) -> str:
    """An empty-secret store whose KDF is scrypt with the given parameters and an empty salt."""
    store = empty_store()
    store["crypto"]["kdf"] = {
        "function": "scrypt",
        "params": {"dklen": dklen, "n": n, "r": r, "p": p, "salt": ""},
        "message": "",
    }
    return json.dumps(store)


@pytest.mark.parametrize(
    "n, r, p, dklen",
    [
        # Twice the ERC-2335 example's p, just over the default work.
        (2**18, 8, 2, 32),
        # A long output from long blocks, with a tiny table.
        (2, 2**16, 1, 2**12),
        # A long output with tiny costs otherwise.
        (2, 1, 1, 2**27),
        # A table of 2^50 bytes.
        (2**40, 8, 1, 32),
    ],
)
def test_default_limits_refuse(n: int, r: int, p: int, dklen: int) -> None:
    memory, work = scrypt_cost(len("password"), 0, n, r, p, dklen)
    assert memory > keystore.MAX_MEMORY or work > keystore.MAX_WORK
    with raises(
        KeystoreError,
        f"EthLib.Cryptography.Keystore.KeystoreError.limitExceeded {memory} {work}",
    ) as exc:
        keystore.decrypt(scrypt_store(n, r, p, dklen), "password")
    assert exc.value.code == 9


def test_default_limits_values() -> None:
    assert (keystore.MAX_MEMORY, keystore.MAX_WORK) == (2**30, 2**24)


def test_negative_limit() -> None:
    with raises(ValueError, "cannot pass a negative int to Lean"):
        keystore.decrypt(json.dumps(empty_store()), "password", max_memory=-1)


def version_text(number: str) -> str:
    """The empty-secret store with its version written as the given JSON number."""
    return json.dumps(empty_store()).replace('"version": 4', f'"version": {number}')


@pytest.mark.parametrize(
    "number, reason",
    [
        ("1e1000000000", "exponents too large"),
        ("1E+00004097", "exponents too large"),
        ("[" + ",".join(["1e2048"] * 2) + ",1e1]", "exponents too large"),
        ("1" * 81, "digit run too long"),
        ("4e-" + "0" * 81, "digit run too long"),
    ],
)
def test_screen_refuses(number: str, reason: str) -> None:
    with raises(
        KeystoreError, f'EthLib.Cryptography.Keystore.KeystoreError.invalidJson "{reason}"'
    ) as exc:
        keystore.decrypt(version_text(number), "password")
    assert exc.value.code == 1


@pytest.mark.parametrize("number", ["4e0", "4E+0000", "0.4e1"])
def test_small_numbers_read(number: str) -> None:
    assert keystore.decrypt(version_text(number), "password") == b""


@pytest.mark.parametrize(
    "number, message",
    [
        # A long value makes the error text wrap onto an indented line.
        ("1e4096", f"unsupportedVersion\n  {10**4096}"),
        ("1" + "0" * 79, f"unsupportedVersion\n  {10**79}"),
        ("4e-99999999999999999999", 'invalidField "version" "Natural number expected"'),
    ],
)
def test_screen_passes_to_reader(number: str, message: str) -> None:
    # The screen lets each through, and the reader then finds no version 4.
    with raises(KeystoreError, "EthLib.Cryptography.Keystore.KeystoreError." + message):
        keystore.decrypt(version_text(number), "password")


def test_exponent_letters_in_strings_ignored() -> None:
    store = empty_store()
    store["description"] = "1e999999999 " + "[" * 100 + "1" * 100
    assert keystore.decrypt(json.dumps(store), "password") == b""


@pytest.mark.parametrize("depth, accepted", [(63, True), (64, False)])
def test_nesting_bound(depth: int, accepted: bool) -> None:
    # The keystore object is one level, so the extra field reaches depth plus one.
    text = json.dumps(empty_store())[:-1] + ', "x": ' + "[" * depth + "]" * depth + "}"
    if accepted:
        assert keystore.decrypt(text, "password") == b""
    else:
        with raises(
            KeystoreError,
            'EthLib.Cryptography.Keystore.KeystoreError.invalidJson "nesting too deep"',
        ):
            keystore.decrypt(text, "password")
