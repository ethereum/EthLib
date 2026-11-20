"""The values of the Keymanager API against the examples of its schemas."""

import hashlib
import json
from functools import cache
from pathlib import Path
from typing import Any, Final

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.consensus import SlashingProtectionError
from ethlib.cryptography import aes, keystore
from ethlib.networking import snappy
from raising import raises

# The OpenAPI document and the types of the Keymanager API, pinned in tests/sources.toml.
SOURCE = Path(__file__).resolve().parents[4] / "tests/consensus/keymanager_api"
ERROR = consensus.KeymanagerError
# The codes of the Lean error: a malformed field, text that is not JSON, rejected EIP-3076 data.
FIELD, NOT_JSON, PROTECTION = 1, 2, 3
# The schemas of the source whose values carry hex, which the writer gives in lowercase.
HEX = {"Pubkey", "EthAddress", "Signature"}
# The schemas whose values hold a JSON document as text.
EMBEDDED = {"Keystore", "SlashingProtectionData"}


@cache
def _load(name: str) -> Any:
    """A file of the source, read as YAML."""
    return YAML(typ="safe").load(SOURCE / name)


def _resolve(ref: str, base: str) -> tuple[Any, str]:
    """The schema that a reference names, with the file that holds it."""
    path, _, pointer = ref.partition("#")
    name = (Path(base).parent / path).as_posix() if path else base
    # The references of the source climb out of types/ only to the top-level document.
    name = name.removeprefix("types/../")
    schema = _load(name)
    for part in filter(None, pointer.split("/")):
        schema = schema[part]
    return schema, name


def _example(schema: Any, base: str) -> Any:
    """The example of a schema, built from the examples of its parts when it gives none."""
    if "$ref" in schema:
        return _example(*_resolve(schema["$ref"], base))
    if "example" in schema:
        return schema["example"]
    if "allOf" in schema:
        return _example(schema["allOf"][0], base)
    return {
        name: _example(part, base)
        for name, part in schema["properties"].items()
        if part.get("type") != "boolean"
    }


def _schema(name: str) -> tuple[Any, str]:
    """A schema of the components of the OpenAPI document, with the file that defines it."""
    return _resolve(f"#/components/schemas/{name}", "keymanager-oapi.yaml")


def _schemas() -> list[str]:
    """The names of the schemas of the source."""
    return list(_load("keymanager-oapi.yaml")["components"]["schemas"])


# The schemas of the builder configuration, which the tests of its calls read and write.
THROUGH_THE_CALLS: Final = ["BuilderConfig", "BuilderEntry"]


def _expected(name: str, value: str) -> str:
    """What the writer gives for a scalar example: hex in lowercase, the rest as it is."""
    return value.lower() if name in HEX else value


def test_schemas_named():
    """The test names every schema of the components of the source."""
    assert _schemas() == [
        "Pubkey",
        "EthAddress",
        "Keystore",
        "BuilderConfig",
        "BuilderEntry",
        "FeeRecipient",
        "GasLimit",
        "Graffiti",
        "Uint64",
        "SignerDefinition",
        "ImportRemoteSignerDefinition",
        "SlashingProtectionData",
        "ErrorResponse",
        "SignedVoluntaryExit",
    ]


@pytest.mark.parametrize("name", [name for name in _schemas() if name not in THROUGH_THE_CALLS])
def test_example_reads_back(name: str):
    """The example of each schema reads, and the writer gives it back in canonical form."""
    example = _example(*_schema(name))
    written = consensus.keymanager_json(name, example)
    if name in EMBEDDED:
        assert json.loads(written) == json.loads(example)
    elif name == "FeeRecipient":
        assert written == {**example, "ethaddress": example["ethaddress"].lower()}
    elif name in {"SignerDefinition", "ImportRemoteSignerDefinition", "GasLimit"}:
        assert written == {**example, "pubkey": example["pubkey"].lower()}
    elif name == "SignedVoluntaryExit":
        assert written == {**example, "signature": example["signature"].lower()}
    else:
        assert written == _expected(name, example)
    assert consensus.keymanager_json(name, written) == written


def test_url_example():
    """The example of the address of a remote signer reads back as itself."""
    example = _load("types/url.yaml")["example"]
    assert consensus.keymanager_json("Url", example) == example


def test_signer_definition_readonly():
    """The flag of a remote key that cannot be deleted reads back, and must be a boolean."""
    pubkey = _load("types/public_key.yaml")["example"]
    for flag in (True, False):
        document = {"pubkey": pubkey, "readonly": flag}
        assert consensus.keymanager_json("SignerDefinition", document) == document
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json("SignerDefinition", {"pubkey": pubkey, "readonly": "true"})


def test_hex_in_either_case():
    """A key and an address read the same with their hex digits in uppercase."""
    pubkey = _load("types/public_key.yaml")["example"]
    address = _load("types/eth_address.yaml")["example"]
    for name, value in (("Pubkey", pubkey), ("EthAddress", address)):
        upper = "0x" + value[2:].upper()
        assert consensus.keymanager_json(name, upper) == value.lower()
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json("Pubkey", "0X" + pubkey[2:])


@pytest.mark.parametrize(
    "text",
    ["0", "30000000", "18446744073709551615", "1" + "0" * 19],
)
def test_uint64_accepts(text: str):
    """A string of the pattern with a value below 2^64 reads back as itself."""
    assert consensus.keymanager_json("Uint64", text) == text


@pytest.mark.parametrize(
    "text",
    [
        "",
        "030000000",
        "00",
        "18446744073709551616",
        "99999999999999999999",
        "+1",
        "-1",
        "1 ",
        "1e3",
    ],
)
def test_uint64_refuses(text: str):
    """A string outside the pattern, or with a value of 2^64 or more, is refused."""
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json("Uint64", text)


def test_uint64_refuses_number():
    """An integer must be a string, so a bare JSON number is refused."""
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json("Uint64", 30000000)


@pytest.mark.parametrize(
    ("name", "value"),
    [
        ("Pubkey", "0x" + "ab" * 47),
        ("EthAddress", "0x" + "ab" * 21),
        ("Signature", "0x" + "ab" * 95),
        ("Signature", "0x" + "zz" * 96),
        ("EthAddress", "ab" * 20),
    ],
)
def test_hex_refused(name: str, value: str):
    """Hex of the wrong length, with a non-hex digit, or without its marker is refused."""
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json(name, value)


def test_optional_field_null():
    """An optional field may be absent but not null, since no schema of the source is nullable."""
    pubkey = _load("types/public_key.yaml")["example"]
    assert consensus.keymanager_json("ImportRemoteSignerDefinition", {"pubkey": pubkey}) == {
        "pubkey": pubkey
    }
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json("ImportRemoteSignerDefinition", {"pubkey": pubkey, "url": None})


def test_undeclared_names():
    """A name that a schema does not declare is ignored, except in a signed voluntary exit."""
    pubkey = _load("types/public_key.yaml")["example"]
    document = {"pubkey": pubkey, "extra": "1"}
    assert consensus.keymanager_json("ImportRemoteSignerDefinition", document) == {"pubkey": pubkey}
    signed = _example(*_schema("SignedVoluntaryExit"))
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json("SignedVoluntaryExit", {**signed, "extra": "1"})


def test_required_field():
    """An object without a field that its schema requires is refused."""
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        consensus.keymanager_json(
            "FeeRecipient", {"pubkey": _load("types/public_key.yaml")["example"]}
        )


def test_keystore_not_json():
    """A keystore whose text is not JSON is refused with its own code."""
    with raises(ERROR, f"keymanager value rejected with code {NOT_JSON}"):
        consensus.keymanager_json("Keystore", "{not json")


def test_slashing_protection_malformed():
    """Slashing protection data without its list of keys is refused with the EIP-3076 code."""
    document = json.loads(_load("types/slashing_protection.yaml")["example"])
    del document["data"]
    with raises(ERROR, f"keymanager value rejected with code {PROTECTION}"):
        consensus.keymanager_json("SlashingProtectionData", json.dumps(document))


def test_slashing_protection_version():
    """Slashing protection data of another version of EIP-3076 is refused with the EIP-3076 code."""
    document = json.loads(_load("types/slashing_protection.yaml")["example"])
    document["metadata"]["interchange_format_version"] = "4"
    with raises(ERROR, f"keymanager value rejected with code {PROTECTION}"):
        consensus.keymanager_json("SlashingProtectionData", json.dumps(document))


def test_unknown_schema():
    """A name that the source gives no schema has code 0."""
    with raises(ERROR, "the Keymanager API has no schema Validator"):
        consensus.keymanager_json("Validator", "0")


# The PBKDF2 keystore of ERC-2335 and its password, pinned in tests/cryptography/keystore.
KEYSTORE_VECTOR = Path(__file__).resolve().parents[4] / "tests/cryptography/keystore/pbkdf2.json"
VECTOR_PASSWORD = "𝔱𝔢𝔰𝔱𝔭𝔞𝔰𝔰𝔴𝔬𝔯𝔡🔑"
# The derivation of the keystores that the tests build: few PBKDF2 rounds, so that they run fast.
ROUNDS = 2
SALT = bytes(range(32))
IV = bytes(range(16))
PATH = "m/12381/3600/0/0/0"
# Bounds on key derivation that every keystore of the tests meets.
MEMORY, WORK = 2**20, 2**20
# The genesis validators root of the slashing protection example of the source.
GENESIS = json.loads(_load("types/slashing_protection.yaml")["example"])["metadata"][
    "genesis_validators_root"
]
# The defaults of the client: the examples of the address, the integer and the graffiti.
DEFAULT_FEE_RECIPIENT = _load("types/eth_address.yaml")["example"].lower()
DEFAULT_GAS_LIMIT = int(_load("types/uint.yaml")["Uint64"]["example"])
DEFAULT_GRAFFITI = _load("types/graffiti.yaml")["example"]
DEFAULTS = (bytes.fromhex(DEFAULT_FEE_RECIPIENT[2:]), DEFAULT_GAS_LIMIT, DEFAULT_GRAFFITI)
# Secret keys of the tests, each a nonzero scalar below the order of the group.
SECRETS = [bytes(31) + bytes([n]) for n in (1, 2, 3)]


def _keystore(secret: bytes, password: str) -> str:
    """An ERC-2335 keystore of a secret key under a password, with PBKDF2 and AES-128-CTR."""
    key = hashlib.pbkdf2_hmac("sha256", keystore.password_bytes(password), SALT, ROUNDS, 32)
    message = aes.ctr(key[:16], IV, secret)
    checksum = hashlib.sha256(key[16:32] + message).digest()
    kdf = {"dklen": 32, "c": ROUNDS, "prf": "hmac-sha256", "salt": SALT.hex()}
    return json.dumps(
        {
            "version": 4,
            "uuid": "00000000-0000-4000-8000-000000000000",
            "path": PATH,
            "crypto": {
                "kdf": {"function": "pbkdf2", "params": kdf, "message": ""},
                "checksum": {"function": "sha256", "params": {}, "message": checksum.hex()},
                "cipher": {
                    "function": "aes-128-ctr",
                    "params": {"iv": IV.hex()},
                    "message": message.hex(),
                },
            },
        }
    )


def _interchange(entries: list[dict[str, Any]]) -> str:
    """The text of EIP-3076 slashing protection data with the genesis root of the source."""
    metadata = {"interchange_format_version": "5", "genesis_validators_root": GENESIS}
    return json.dumps({"metadata": metadata, "data": entries})


def _entry(pubkey: str, slot: int, source: int, target: int) -> dict[str, Any]:
    """The entry of a key that signed one block and one vote."""
    return {
        "pubkey": pubkey,
        "signed_blocks": [{"slot": str(slot)}],
        "signed_attestations": [{"source_epoch": str(source), "target_epoch": str(target)}],
    }


def _run(
    calls: list[tuple[str, str, Any]], memory: int = MEMORY, work: int = WORK
) -> tuple[list[tuple[int, Any]], bytes, list[bytes]]:
    """The responses of calls on a client with no key, the record and the keys afterwards."""
    responses, state = consensus.keymanager_run(
        memory, work, *DEFAULTS, _interchange([]), None, calls
    )
    keys = [bytes.fromhex(key[2:]) for key in state["local_keys"]]
    return responses, state["slashing_protection"].encode(), keys


def _import(
    keystores: list[str], passwords: list[str], protection: str | None = None
) -> tuple[str, str, Any]:
    """The call that imports keystores."""
    body: dict[str, Any] = {"keystores": keystores, "passwords": passwords}
    if protection is not None:
        body["slashing_protection"] = protection
    return ("POST", "/eth/v1/keystores", body)


@cache
def _pubkeys() -> list[str]:
    """The public keys of the secret keys of the tests, from a client that imports them."""
    calls = [_import([_keystore(secret, "pass")], ["pass"]) for secret in SECRETS]
    _, _, pubkeys = _run(calls)
    return ["0x" + pubkey.hex() for pubkey in pubkeys]


def _statuses(response: tuple[int, Any]) -> list[str]:
    """The statuses of a response with HTTP 200."""
    code, body = response
    assert code == 200
    return [entry["status"] for entry in body["data"]]


def test_import_erc_2335_vector():
    """The PBKDF2 keystore of ERC-2335 imports the key that the ERC names."""
    vector = json.loads(KEYSTORE_VECTOR.read_text())
    responses, _, pubkeys = _run([_import([json.dumps(vector)], [VECTOR_PASSWORD])])
    assert responses == [(200, {"data": [{"status": "imported"}]})]
    assert pubkeys == [bytes.fromhex(vector["pubkey"])]


def test_import_example():
    """The example of the issue: one keystore with its data, then a repeat and a length mismatch."""
    a = _pubkeys()[0]
    protection = _interchange([_entry(a, 81952, 2290, 3007)])
    keystore_a = _keystore(SECRETS[0], "pass")
    responses, record, _ = _run(
        [
            _import([keystore_a], ["pass"], protection),
            _import([keystore_a], ["pass"]),
            _import([keystore_a, keystore_a], ["pass"]),
        ]
    )
    assert responses[0] == (200, {"data": [{"status": "imported"}]})
    assert responses[1] == (200, {"data": [{"status": "duplicate"}]})
    assert responses[2][0] == 400
    key = bytes.fromhex(a[2:])
    root = bytes(32)
    # A block at the slot of the limit conflicts with it, which has no signing root.
    with raises(SlashingProtectionError, "slashing protection failed with code 3"):
        consensus.check_block_signing(record, key, 81952, root)
    consensus.check_block_signing(record, key, 81953, root)
    # A vote with the target of the limit is a double vote with it.
    with raises(SlashingProtectionError, "slashing protection failed with code 5"):
        consensus.check_attestation_signing(record, key, 2290, 3007, root)
    consensus.check_attestation_signing(record, key, 2290, 3008, root)


def test_duplicate_in_one_request():
    """A key imported earlier in the same request is a duplicate, as the use cases say."""
    keystore_a = _keystore(SECRETS[0], "pass")
    responses, _, pubkeys = _run([_import([keystore_a, keystore_a], ["pass", "pass"])])
    assert [_statuses(response) for response in responses] == [["imported", "duplicate"]]
    assert len(pubkeys) == 1


def test_data_of_imported_keys_only():
    """Keystores of a and b with data of a, b and c load the data of a and b only."""
    a, b, c = _pubkeys()
    protection = _interchange([_entry(key, 100, 9, 10) for key in (a, b, c)])
    keystores = [_keystore(secret, "pass") for secret in SECRETS[:2]]
    responses, record, _ = _run([_import(keystores, ["pass", "pass"], protection)])
    assert [_statuses(response) for response in responses] == [["imported", "imported"]]
    root = bytes(32)
    for key in (a, b):
        with raises(SlashingProtectionError, "slashing protection failed with code 3"):
            consensus.check_block_signing(record, bytes.fromhex(key[2:]), 100, root)
    consensus.check_block_signing(record, bytes.fromhex(c[2:]), 100, root)


def test_failure_does_not_stop_the_others():
    """A wrong password gives an error status, and the next keystore is still imported."""
    keystores = [_keystore(secret, "pass") for secret in SECRETS[:2]]
    responses, _, pubkeys = _run([_import(keystores, ["wrong", "pass"])])
    code, body = responses[0]
    assert code == 200
    assert body["data"][0] == {
        "status": "error",
        "message": "the keystore did not decrypt, with code 8",
    }
    assert body["data"][1] == {"status": "imported"}
    assert ["0x" + key.hex() for key in pubkeys] == [_pubkeys()[1]]


def test_example_keystore_of_the_source():
    """The keystore example of the source does not decrypt with the password example of the call."""
    example = _load("types/keystore.yaml")["example"]
    password = "ABCDEFGH01234567ABCDEFGH01234567"
    responses, _, pubkeys = _run([_import([example], [password])], 2**30, 2**24)
    error = {"status": "error", "message": "the keystore did not decrypt, with code 8"}
    assert responses == [(200, {"data": [error]})]
    assert pubkeys == []


def test_empty_request():
    """A request with no keystore succeeds with no status, even with data that does not read."""
    responses, _, _ = _run([_import([], [], "{not json")])
    assert responses == [(200, {"data": []})]


@pytest.mark.parametrize(
    ("body", "message"),
    [
        (
            {"keystores": ["{}"], "passwords": []},
            "the keystores and the passwords differ in number",
        ),
        (
            {"keystores": ["{}"], "passwords": ["pass"], "slashing_protection": "{not json"},
            "the slashing protection data does not read",
        ),
        ({"keystores": ["{}"]}, "the request does not read"),
        ({"keystores": [1], "passwords": ["pass"]}, "the request does not read"),
    ],
)
def test_bad_request(body: dict[str, Any], message: str):
    """A request refused as a whole gets HTTP 400 and the body of an error, and changes nothing."""
    responses, _, pubkeys = _run([("POST", "/eth/v1/keystores", body)])
    assert responses == [(400, {"message": message})]
    assert pubkeys == []


def test_unknown_call():
    """A method and path that the API does not define get HTTP 404, and change nothing."""
    responses, _, pubkeys = _run([("GET", "/eth/v1/unknown", {})])
    assert responses == [(404, {"message": "Path not found"})]
    assert pubkeys == []


def test_bad_starting_record():
    """A starting record that does not read is refused with the code of EIP-3076 data."""
    with raises(ERROR, f"keymanager value rejected with code {PROTECTION}"):
        consensus.keymanager_run(MEMORY, WORK, *DEFAULTS, '{"metadata": {}}', None, [])


def _calls(*calls: tuple[str, str, Any]) -> tuple[list[tuple[int, Any]], dict[str, Any]]:
    """The responses of calls on a client with no key, and its state afterwards."""
    return consensus.keymanager_run(MEMORY, WORK, *DEFAULTS, _interchange([]), None, list(calls))


def test_list_keys():
    """The list gives each key that the client holds, in order, with its path."""
    keystores = [_keystore(secret, "pass") for secret in SECRETS[:2]]
    responses, _ = _calls(
        ("GET", "/eth/v1/keystores", {}),
        _import(keystores, ["pass", "pass"]),
        ("GET", "/eth/v1/keystores", {}),
    )
    assert responses[0] == (200, {"data": []})
    listed = [
        {"validating_pubkey": key, "derivation_path": PATH, "readonly": False}
        for key in _pubkeys()[:2]
    ]
    assert responses[2] == (200, {"data": listed})


def test_delete_use_case():
    """The use case of the source: a request a, a, b, c on a client that holds a and c."""
    a, b, c = _pubkeys()
    protection = _interchange([_entry(a, 100, 9, 10), _entry(c, 200, 19, 20)])
    keystores = [_keystore(SECRETS[0], "pass"), _keystore(SECRETS[2], "pass")]
    delete = ("DELETE", "/eth/v1/keystores", {"pubkeys": [a, a, b, c]})
    responses, state = _calls(
        _import(keystores, ["pass", "pass"], protection),
        delete,
        ("GET", "/eth/v1/keystores", {}),
        delete,
    )
    code, body = responses[1]
    assert code == 200
    statuses = [entry["status"] for entry in body["data"]]
    assert statuses == ["deleted", "not_active", "not_found", "deleted"]
    returned = json.loads(body["slashing_protection"])
    assert sorted(entry["pubkey"] for entry in returned["data"]) == sorted([a, c])
    assert responses[2] == (200, {"data": []})
    # A second delete finds no key, and returns the same data, which the record keeps.
    again = responses[3][1]
    statuses = [entry["status"] for entry in again["data"]]
    assert statuses == ["not_active", "not_active", "not_found", "not_active"]
    assert json.loads(again["slashing_protection"]) == returned
    assert state["local_keys"] == []
    record = state["slashing_protection"].encode()
    with raises(SlashingProtectionError, "slashing protection failed with code 3"):
        consensus.check_block_signing(record, bytes.fromhex(a[2:]), 100, bytes(32))


def test_delete_bad_request():
    """A delete whose body does not read gets HTTP 400."""
    responses, _ = _calls(("DELETE", "/eth/v1/keystores", {"pubkeys": ["0x12"]}))
    assert responses == [(400, {"message": "the request does not read"})]


# Two remote keys, and the address of a remote signer from the example of the source.
REMOTE_A = "0x" + "aa" * 48
REMOTE_B = "0x" + "bb" * 48
REMOTE_C = "0x" + "cc" * 48
SIGNER = _load("types/url.yaml")["example"]


def _remote(*pubkeys: str) -> tuple[str, str, Any]:
    """The call that imports remote keys, each at the signer of the example."""
    keys = [{"pubkey": pubkey, "url": SIGNER} for pubkey in pubkeys]
    return ("POST", "/eth/v1/remotekeys", {"remote_keys": keys})


def test_remote_keys_example():
    """The example of the issue: import a, b, b onto a, then delete b, c."""
    listed = ("GET", "/eth/v1/remotekeys", {})
    responses, _ = _calls(
        _remote(REMOTE_A),
        _remote(REMOTE_A, REMOTE_B, REMOTE_B),
        listed,
        ("DELETE", "/eth/v1/remotekeys", {"pubkeys": [REMOTE_B, REMOTE_C]}),
        listed,
    )
    statuses = [[entry["status"] for entry in body["data"]] for _, body in responses[:2]]
    assert statuses == [["imported"], ["duplicate", "imported", "duplicate"]]
    definitions = [
        {"pubkey": key, "url": SIGNER, "readonly": False} for key in (REMOTE_A, REMOTE_B)
    ]
    assert responses[2] == (200, {"data": definitions})
    deleted = {"data": [{"status": "deleted"}, {"status": "not_found"}]}
    assert responses[3] == (200, deleted)
    assert responses[4] == (200, {"data": definitions[:1]})


def test_remote_key_held_locally():
    """A key that the client holds locally is known, so its remote import is a duplicate."""
    local = _pubkeys()[0]
    responses, _ = _calls(_import([_keystore(SECRETS[0], "pass")], ["pass"]), _remote(local))
    assert responses[1] == (200, {"data": [{"status": "duplicate"}]})


def test_remote_bad_request():
    """A remote call whose body does not read gets HTTP 400."""
    responses, _ = _calls(
        ("POST", "/eth/v1/remotekeys", {"remote_keys": [{"url": SIGNER}]}),
        ("DELETE", "/eth/v1/remotekeys", {}),
    )
    assert responses == [(400, {"message": "the request does not read"})] * 2


def test_move_a_key():
    """The use case "Move a key": the new client refuses what the old one refused."""
    a = _pubkeys()[0]
    key = bytes.fromhex(a[2:])
    keystore_a = _keystore(SECRETS[0], "pass")
    # The old client signed a block at slot 100 and a vote from 9 to 10 with the key.
    history = _interchange([_entry(a, 100, 9, 10)])
    old, old_state = _calls(
        _import([keystore_a], ["pass"], history),
        ("DELETE", "/eth/v1/keystores", {"pubkeys": [a]}),
    )
    assert old_state["local_keys"] == []
    moved = old[1][1]["slashing_protection"]
    new, new_state = _calls(_import([keystore_a], ["pass"], moved))
    assert new == [(200, {"data": [{"status": "imported"}]})]
    old_record = old_state["slashing_protection"].encode()
    new_record = new_state["slashing_protection"].encode()
    root = b"\x01" * 32
    for record in (old_record, new_record):
        # A block at slot 100 with another root, and a vote around the old one, are refused.
        with raises(SlashingProtectionError, "slashing protection failed with code 3"):
            consensus.check_block_signing(record, key, 100, root)
        with raises(SlashingProtectionError, "slashing protection failed with code 5"):
            consensus.check_attestation_signing(record, key, 8, 11, root)
    consensus.check_block_signing(new_record, key, 101, root)


def test_fee_recipient_example():
    """The example of issue #2140: get the default, set, get, delete, get, then an unknown key."""
    k = _pubkeys()[0]
    path = f"/eth/v1/validator/{k}/feerecipient"
    other = "0x6fdfab408c56b6105a76eff5c0435d09fc6ed7a9"
    unknown = f"/eth/v1/validator/{REMOTE_C}/feerecipient"
    responses, _ = _calls(
        _import([_keystore(SECRETS[0], "pass")], ["pass"]),
        ("GET", path, {}),
        ("POST", path, {"ethaddress": other}),
        ("GET", path, {}),
        ("DELETE", path, {}),
        ("GET", path, {}),
        ("DELETE", unknown, {}),
    )
    default = (200, {"data": {"pubkey": k, "ethaddress": DEFAULT_FEE_RECIPIENT}})
    assert responses[1:] == [
        default,
        (202, None),
        (200, {"data": {"pubkey": k, "ethaddress": other}}),
        (204, None),
        default,
        (404, {"message": "The key was not found on the server"}),
    ]


def test_fee_recipient_zero():
    """A fee recipient of zero is refused, and the default stays."""
    k = _pubkeys()[0]
    path = f"/eth/v1/validator/{k}/feerecipient"
    responses, _ = _calls(
        _import([_keystore(SECRETS[0], "pass")], ["pass"]),
        ("POST", path, {"ethaddress": "0x" + "00" * 20}),
        ("GET", path, {}),
    )
    message = "Cannot specify the 0x00 fee recipient address through the API"
    assert responses[1:] == [
        (400, {"message": message}),
        (200, {"data": {"pubkey": k, "ethaddress": DEFAULT_FEE_RECIPIENT}}),
    ]


def test_gas_limit_and_graffiti():
    """A gas limit and a graffiti set for one key leave the defaults of another key."""
    k, other = _pubkeys()[:2]
    keystores = [_keystore(secret, "pass") for secret in SECRETS[:2]]
    responses, _ = _calls(
        _import(keystores, ["pass", "pass"]),
        ("POST", f"/eth/v1/validator/{k}/gas_limit", {"gas_limit": "36000000"}),
        ("POST", f"/eth/v1/validator/{k}/graffiti", {"graffiti": "moved"}),
        ("GET", f"/eth/v1/validator/{k}/gas_limit", {}),
        ("GET", f"/eth/v1/validator/{other}/gas_limit", {}),
        ("GET", f"/eth/v1/validator/{k}/graffiti", {}),
        ("GET", f"/eth/v1/validator/{other}/graffiti", {}),
    )
    assert responses[1:] == [
        (202, None),
        (202, None),
        (200, {"data": {"pubkey": k, "gas_limit": "36000000"}}),
        (200, {"data": {"pubkey": other, "gas_limit": str(DEFAULT_GAS_LIMIT)}}),
        (200, {"data": {"pubkey": k, "graffiti": "moved"}}),
        (200, {"data": {"pubkey": other, "graffiti": DEFAULT_GRAFFITI}}),
    ]


def test_setting_bad_path_and_body():
    """A path whose key does not read, or a body that does not read, gets HTTP 400."""
    k = _pubkeys()[0]
    responses, _ = _calls(
        _import([_keystore(SECRETS[0], "pass")], ["pass"]),
        ("GET", "/eth/v1/validator/0x12/gas_limit", {}),
        ("POST", f"/eth/v1/validator/{k}/gas_limit", {"gas_limit": 1}),
    )
    assert responses[1:] == [
        (400, {"message": "the public key of the path does not read"}),
        (400, {"message": "the request does not read"}),
    ]


def test_setting_of_unmanaged_key():
    """Every call on a setting of a key that the client does not manage gets HTTP 404."""
    path = f"/eth/v1/validator/{REMOTE_C}/graffiti"
    responses, _ = _calls(
        ("GET", path, {}), ("POST", path, {"graffiti": "x"}), ("DELETE", path, {})
    )
    assert responses == [(404, {"message": "The key was not found on the server"})] * 3


# The minimal operations of consensus-specs, whose voluntary exit cases "basic" the tests sign.
# They are pinned in tests/sources.toml; Capella signs with the domain of the state, Deneb not.
EXIT_CASES = Path(__file__).resolve().parents[4] / "tests/consensus/operations/minimal"
# The width of an integer in SSZ, and the place of the slot in the bytes of a state.
UINT64 = 8
SLOT = slice(40, 48)
SLOTS_PER_EPOCH_MINIMAL = 8


def _exit_case(name: str) -> tuple[bytes, int, int, bytes]:
    """The state of the case at a fork, and the epoch, the index and the signature of its exit."""
    case = EXIT_CASES / name / "operations/voluntary_exit/pyspec_tests/basic"
    state = snappy.decompress((case / "pre.ssz_snappy").read_bytes())
    signed = snappy.decompress((case / "voluntary_exit.ssz_snappy").read_bytes())
    epoch = int.from_bytes(signed[:UINT64], "little")
    index = int.from_bytes(signed[UINT64 : 2 * UINT64], "little")
    return state, epoch, index, signed[2 * UINT64 :]


@pytest.mark.parametrize(("fork", "name"), [("dencun", "deneb"), ("shapella", "capella")])
def test_voluntary_exit_matches_consensus_specs(fork: str, name: str):
    """The exit that the client signs is the signed exit of the case, byte for byte."""
    state, epoch, index, signature = _exit_case(name)
    # The keys of the test states of consensus-specs are the integers from 1, by validator index.
    keystore_v = _keystore((index + 1).to_bytes(32, "big"), "pass")
    _, held = _calls(_import([keystore_v], ["pass"]))
    pubkey = held["local_keys"][0]
    chain = ("minimal", "minimal", fork, state)
    path = f"/eth/v1/validator/{pubkey}/voluntary_exit"
    responses, _ = consensus.keymanager_run(
        MEMORY,
        WORK,
        *DEFAULTS,
        _interchange([]),
        chain,
        [
            _import([keystore_v], ["pass"]),
            ("POST", f"{path}?epoch={epoch}", {}),
            ("POST", path, {}),
            ("POST", f"{path}?epoch=x", {}),
            _remote(REMOTE_C),
            ("POST", f"/eth/v1/validator/{REMOTE_C}/voluntary_exit", {}),
        ],
    )
    message = {"epoch": str(epoch), "validator_index": str(index)}
    assert responses[1] == (
        200,
        {"data": {"message": message, "signature": "0x" + signature.hex()}},
    )
    current = int.from_bytes(state[SLOT], "little") // SLOTS_PER_EPOCH_MINIMAL
    assert responses[2][0] == 200
    assert responses[2][1]["data"]["message"] == {
        "epoch": str(current),
        "validator_index": str(index),
    }
    assert responses[3] == (400, {"message": "the epoch of the query does not read"})
    assert responses[5] == (404, {"message": "The key was not found on the server"})


def test_voluntary_exit_without_chain():
    """A client with no view of the chain cannot sign an exit."""
    pubkey = _pubkeys()[0]
    responses, _ = _calls(
        _import([_keystore(SECRETS[0], "pass")], ["pass"]),
        ("POST", f"/eth/v1/validator/{pubkey}/voluntary_exit", {}),
    )
    assert responses[1] == (500, {"message": "the client has no view of the chain"})


def _builder_calls(builder: dict[str, Any], *calls: tuple[str, str, Any]) -> list[tuple[int, Any]]:
    """The responses of calls on a client with one key and a builder configuration of its own."""
    responses, _ = consensus.keymanager_run(
        MEMORY,
        WORK,
        *DEFAULTS,
        _interchange([]),
        None,
        [_import([_keystore(SECRETS[0], "pass")], ["pass"]), *calls],
        builder,
    )
    return responses[1:]


def _ascii_hex(text: str) -> str:
    """The default authentication data of a host, the hex of its ASCII bytes."""
    return "0x" + text.encode().hex()


# A client with no builder, no floor, a cap of 0 on the execution payment and a weight of 100.
NO_BUILDER: Final = {
    "min_bid": "0",
    "builder_boost_factor": "100",
    "max_execution_payment": "0",
    "builders": [],
}

# The examples of the source's `apis/builder_config.yaml`, read from the vendored file.
BUILDER_CONFIG_EXAMPLES: Final = YAML(typ="safe").load(
    (SOURCE / "apis" / "builder_config.yaml").read_text()
)


def _builder_path() -> str:
    return f"/eth/v1/validator/{_pubkeys()[0]}/builder_config"


def test_builder_config_set_example():
    """The example of a set resolves each omitted value, as the schema says."""
    body = BUILDER_CONFIG_EXAMPLES["post"]["requestBody"]["content"]["application/json"]
    example = body["examples"]["BuilderConfig"]["value"]
    path = _builder_path()
    responses = _builder_calls(NO_BUILDER, ("POST", path, example), ("GET", path, {}))
    pubkey = example["builders"][1]["builder_pubkeys"][0]
    assert responses == [
        (202, None),
        (
            200,
            {
                "data": {
                    "min_bid": "10000000",
                    "builder_boost_factor": "100",
                    "builders": [
                        {
                            "url": "https://builder-a.example.com",
                            "auth_data": _ascii_hex("builder-a.example.com"),
                            "builder_pubkeys": [],
                            "max_execution_payment": "0",
                            "min_bid": "10000000",
                            "builder_boost_factor": "100",
                        },
                        {
                            "url": "https://builder-b.example.com",
                            "auth_data": _ascii_hex("builder-b.example.com"),
                            "builder_pubkeys": [pubkey],
                            "max_execution_payment": "0",
                            "min_bid": "10000000",
                            "builder_boost_factor": "120",
                        },
                    ],
                }
            },
        ),
    ]


def test_builder_config_get_example():
    """The example of a get, set again, is answered unchanged: it is fully resolved."""
    content = BUILDER_CONFIG_EXAMPLES["get"]["responses"]["200"]["content"]["application/json"]
    example = content["examples"]["BuilderConfig"]["value"]
    path = _builder_path()
    responses = _builder_calls(NO_BUILDER, ("POST", path, example["data"]), ("GET", path, {}))
    assert responses == [(202, None), (200, example)]


def test_builder_config_example_of_the_issue():
    """A key set over the client's builders, then deleted, follows the client again."""
    client = dict(NO_BUILDER, builders=[{"url": "https://a.example"}])
    path = _builder_path()
    set_body = {"builder_boost_factor": "120", "builders": [{"url": "https://b.example"}]}
    responses = _builder_calls(
        client,
        ("GET", path, {}),
        ("POST", path, set_body),
        ("GET", path, {}),
        ("DELETE", path, {}),
        ("GET", path, {}),
        ("DELETE", path, {}),
    )

    def answer(url: str, host: str, boost: str) -> tuple[int, Any]:
        entry = {
            "url": url,
            "auth_data": _ascii_hex(host),
            "builder_pubkeys": [],
            "max_execution_payment": "0",
            "min_bid": "0",
            "builder_boost_factor": boost,
        }
        return (200, {"data": {"min_bid": "0", "builder_boost_factor": boost, "builders": [entry]}})

    own = answer("https://a.example", "a.example", "100")
    assert responses == [
        own,
        (202, None),
        answer("https://b.example", "b.example", "120"),
        (204, None),
        own,
        (204, None),
    ]


@pytest.mark.parametrize(
    ("body", "message"),
    [
        pytest.param({"builders": [{}]}, "the request does not read", id="no-url"),
        pytest.param(
            {"builders": [{"url": "https://a.example"}, {"url": "https://a.example"}]},
            "two entries share their URL and authentication data",
            id="same-url-and-default-data",
        ),
        pytest.param(
            {"builders": [{"url": "a.example"}]},
            "an entry has no authentication data and its URL gives none",
            id="no-default-data",
        ),
        pytest.param(
            {"builders": [{"url": "https://a.example", "auth_data": "0x"}]},
            "the request does not read",
            id="empty-data",
        ),
    ],
)
def test_builder_config_refused(body: dict[str, Any], message: str):
    """A set that breaks a rule of a set is refused with 400, and nothing is stored."""
    path = _builder_path()
    responses = _builder_calls(NO_BUILDER, ("POST", path, body), ("GET", path, {}))
    empty = {"data": {"min_bid": "0", "builder_boost_factor": "100", "builders": []}}
    assert responses == [(400, {"message": message}), (200, empty)]


def test_builder_config_same_url_other_data():
    """Two entries may share a URL when their authentication data differ."""
    path = _builder_path()
    body = {
        "builders": [
            {"url": "https://a.example", "auth_data": "0x01"},
            {"url": "https://a.example", "auth_data": "0x02"},
        ]
    }
    responses = _builder_calls(NO_BUILDER, ("POST", path, body))
    assert responses == [(202, None)]


def test_builder_config_unknown_key():
    """Each call on a key that the client does not manage gets 404."""
    path = f"/eth/v1/validator/{REMOTE_C}/builder_config"
    responses = _builder_calls(
        NO_BUILDER, ("GET", path, {}), ("POST", path, {}), ("DELETE", path, {})
    )
    assert responses == [(404, {"message": "The key was not found on the server"})] * 3


def test_builder_config_hex_case_duplicate():
    """Authentication data is compared as bytes, so hex case does not tell two entries apart."""
    path = _builder_path()
    data = _ascii_hex("a.example")
    body = {
        "builders": [
            {"url": "https://a.example", "auth_data": data.upper().replace("0X", "0x")},
            {"url": "https://a.example"},
        ]
    }
    responses = _builder_calls(NO_BUILDER, ("POST", path, body))
    assert responses == [(400, {"message": "two entries share their URL and authentication data"})]


def test_builder_config_set_replaces():
    """A set replaces the stored configuration in full, and an empty list names no builder."""
    client = dict(NO_BUILDER, builders=[{"url": "https://a.example"}])
    path = _builder_path()
    responses = _builder_calls(
        client,
        ("POST", path, {"min_bid": "5", "builders": []}),
        ("POST", path, {"builder_boost_factor": "7"}),
        ("GET", path, {}),
        ("POST", path, {"builders": []}),
        ("GET", path, {}),
    )
    entry = {
        "url": "https://a.example",
        "auth_data": _ascii_hex("a.example"),
        "builder_pubkeys": [],
        "max_execution_payment": "0",
        "min_bid": "0",
        "builder_boost_factor": "7",
    }
    assert responses[2] == (
        200,
        {"data": {"min_bid": "0", "builder_boost_factor": "7", "builders": [entry]}},
    )
    assert responses[4] == (
        200,
        {"data": {"min_bid": "0", "builder_boost_factor": "100", "builders": []}},
    )


def test_builder_config_client_meets_the_rules():
    """A client whose own builders break a rule of a set is refused."""
    client = dict(NO_BUILDER, builders=[{"url": "https://a.example"}, {"url": "https://a.example"}])
    with raises(ERROR, f"keymanager value rejected with code {FIELD}"):
        _builder_calls(client)
