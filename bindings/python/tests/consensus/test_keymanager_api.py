"""The values of the Keymanager API against the examples of its schemas."""

import json
from functools import cache
from pathlib import Path
from typing import Any

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
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


def _expected(name: str, value: str) -> str:
    """What the writer gives for a scalar example: hex in lowercase, the rest as it is."""
    return value.lower() if name in HEX else value


def test_schemas_named():
    """The test covers every schema of the components of the source."""
    assert _schemas() == [
        "Pubkey",
        "EthAddress",
        "Keystore",
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


@pytest.mark.parametrize("name", _schemas())
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
