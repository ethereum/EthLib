"""The JSON of the Beacon API for the beacon containers, against the types of beacon-APIs."""

import functools
import hashlib
import json
import posixpath
import re
from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path
from typing import Any, TypeAlias

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.errors import SszError
from ethlib.networking import snappy
from raising import raises, raises_shape

from .containers import FORKS

VECTORS = Path(__file__).resolve().parents[4] / "tests" / "consensus"
# The types of ethereum/beacon-APIs at 7911555e, pinned in tests/sources.toml.
# Some of them refer to others through the OpenAPI document at the top of the repository.
BEACON_API = VECTORS / "beacon_api"
SSZ_STATIC = VECTORS / "ssz_static"

# The types files key the containers of a fork by its consensus version, capitalized.
# They key the containers of every fork, such as Checkpoint, by name alone in one file.
FORKLESS = "types/misc.yaml"

# The keywords of the schemas that the validator reads, or that constrain nothing.
# A schema with any other keyword fails, so that no constraint passes unread.
KEYWORDS = {
    "$ref",
    "allOf",
    "type",
    "properties",
    "required",
    "items",
    "pattern",
    "minItems",
    "maxItems",
    "minLength",
    "maxLength",
    "format",
    "description",
    "example",
}

# The keywords that a schema may give beside a reference.
# OpenAPI 3.1, the version of the document, applies them as well as the schema it names.
REFERENCE_KEYWORDS = {"$ref", "description", "example", "minLength", "maxLength"}

# The API names of the containers whose consensus-specs names differ.
API_NAMES = {"SyncCommitteeMessage": "SyncCommitteeSignature"}

# The containers of the vendored cases that no types file defines, with what each one is.
# Neither the types files nor the endpoints of beacon-APIs at 7911555e name them.
# A test checks that this is exactly the set of containers without a schema.
NO_SCHEMA = {
    "SigningData": "the object whose root a signature signs",
    "ForkData": "the object whose root gives the fork digest and the signing domain",
    "DepositMessage": "the object whose root a deposit signs",
    "SyncAggregatorSelectionData": "the object whose root a sync selection proof signs",
    "HistoricalBatch": "the object whose root the state appends to its historical roots",
    "Eth1Block": "a block of the deposit chain, as the honest validator reads it",
    "PowBlock": "a block of proof of work, as the merge transition reads it",
    "NewPayloadRequest": "the request that the beacon chain gives the execution engine",
    "BlobSidecar": "a sidecar of the networking specification",
    "BlobIdentifier": "an identifier of a request of the networking specification",
    "DataColumnsByRootIdentifier": "an identifier of a request of the networking specification",
    "MatrixEntry": "an entry of the extended blob matrix of data availability sampling",
    "PartialDataColumnSidecar": "a partial column of the networking specification",
    "PartialDataColumnHeader": "the header of a partial column of the networking specification",
    "PartialDataColumnPartsMetadata": "the cells of a column that a peer has, and those it wants",
    "PartialDataColumnGroupID": "the group of a partial column of the networking specification",
    "IndexedPayloadAttestation": "a payload attestation with its attesters, as the state checks it",
}

# The strings whose SSZ type has a variable length, by the name of their type in the types files.
# An example of another type replaces a string of the same length only.
VARIABLE_LENGTH = {"BitList", "Transaction", "ExtraData", "BlockAccessList"}

# A checkpoint in the JSON of the API, which the tests of the validator change.
CHECKPOINT = {"epoch": "1", "root": "0x" + "00" * 32}

# The examples that must stand in for a leaf, in the cases of the minimal preset.
# They are the participation flags of each state from Altair.
# They are also a transaction and the block access list of a Gloas payload.
FLAGS = {("Uint8", "previous_epoch_participation/*"), ("Uint8", "current_epoch_participation/*")}
REQUIRED_EXAMPLES = {
    **{
        ("minimal", fork, "BeaconState"): FLAGS
        for fork in ["altair", "bellatrix", "capella", "deneb", "electra", "fulu", "gloas"]
    },
    ("minimal", "gloas", "ExecutionPayload"): {
        ("Transaction", "transactions/*"),
        ("BlockAccessList", "block_access_list"),
    },
}

# The examples of the Builder API and their JSON forms, written by the builder specification.
# Each gives its directory, its file, the container, and the key of its JSON form under "value".
BUILDER_EXAMPLES = [
    *(
        (fork, "signed_builder_bid", "SignedBuilderBid", "data")
        for fork in ["bellatrix", "capella", "deneb", "electra", "fulu"]
    ),
    *(
        (fork, "signed_blinded_beacon_block", "SignedBlindedBeaconBlock", None)
        for fork in ["bellatrix", "capella", "deneb", "electra", "fulu"]
    ),
    ("gloas", "signed_builder_request_auth", "SignedBuilderRequestAuth", None),
    ("gloas", "builder_preferences", "BuilderPreferences", None),
    ("gloas", "builder_preferences_request", "BuilderPreferencesRequest", None),
]

# A location in a JSON document: a key of an object, or an index of an array, at each step.
Location: TypeAlias = tuple[str | int, ...]


@dataclass(frozen=True, slots=True)
class Schema:
    """A schema of a vendored file, and the file against which its references resolve."""

    node: Mapping[str, object]
    file: str


@dataclass(frozen=True, slots=True)
class Leaf:
    """A string of a document, with the name of its type and the example the types give."""

    path: Location
    type_name: str
    example: str | None


def _mapping(value: object, where: str) -> Mapping[str, object]:
    """A value of a vendored file that must be a mapping."""
    if not isinstance(value, Mapping):
        raise TypeError(f"{where}: {value!r} is not a mapping")
    return value


def _list(value: object, where: str) -> list[object]:
    """A value of a vendored file that must be a list."""
    if not isinstance(value, list):
        raise TypeError(f"{where}: {value!r} is not a list")
    return value


def _int(node: Mapping[str, object], key: str, default: int) -> int:
    """A bound of a schema, or the default when the schema gives none."""
    value = node.get(key, default)
    if not isinstance(value, int):
        raise TypeError(f"{key} is {value!r}, not an integer")
    return value


@functools.cache
def _file(name: str) -> Mapping[str, object]:
    """A vendored file of beacon-APIs by its path in that repository."""
    root = BEACON_API.resolve()
    path = (root / name).resolve()
    # A reference names a file relative to its own, and it must stay among the vendored files.
    if root not in path.parents:
        raise ValueError(f"a reference leaves the vendored files: {name}")
    return _mapping(YAML(typ="safe", pure=True).load(path.read_text(encoding="utf-8")), name)


def _resolve(reference: str, file: str) -> Schema:
    """The schema that a reference names: a file relative to the referring one, and a pointer."""
    target, _, pointer = reference.partition("#")
    name = posixpath.normpath(posixpath.join(posixpath.dirname(file), target)) if target else file
    node: object = _file(name)
    for key in pointer.split("/")[1:]:
        node = _mapping(node, f"{file}: {reference}").get(key)
    return Schema(_mapping(node, f"{file}: {reference}"), name)


@functools.cache
def _definitions() -> Mapping[tuple[str, str], Schema]:
    """Each schema of a container, by its fork key, or by the empty key in the forkless file."""
    definitions: dict[tuple[str, str], Schema] = {
        ("", name): Schema(_mapping(node, FORKLESS), FORKLESS)
        for name, node in _file(FORKLESS).items()
    }
    for path in sorted((BEACON_API / "types").glob("*/*.yaml")):
        name = path.relative_to(BEACON_API).as_posix()
        for key, containers in _file(name).items():
            for container, node in _mapping(containers, name).items():
                assert (key, container) not in definitions, (key, container)
                definitions[key, container] = Schema(_mapping(node, name), name)
    return definitions


def _api_fork(fork: str) -> str | None:
    """The key of the types files for a fork of consensus-specs, or None for a fork they omit."""
    version = consensus.consensus_version(FORKS[fork])
    return version.capitalize() if version else None


def _schema(container: str, fork: str) -> Schema | None:
    """The schema of a container at a fork, under the latest fork key at or before it."""
    name = API_NAMES.get(container, container)
    forks = list(FORKS)
    for earlier in reversed(forks[: forks.index(fork) + 1]):
        key = _api_fork(earlier)
        if key is not None and (key, name) in _definitions():
            return _definitions()[key, name]
    return _definitions().get(("", name))


class SchemaError(AssertionError):
    """A value that does not conform to its schema, or a schema that the validator cannot read."""


def _require(condition: bool, message: str) -> None:
    """Raise a schema error with the message unless the condition holds."""
    if not condition:
        raise SchemaError(message)


def _check_keywords(schema: Schema, where: str) -> None:
    """Fail on a keyword that the validator does not read."""
    unread = set(schema.node) - KEYWORDS
    _require(not unread, f"{where}: unread keywords {sorted(unread)}")
    _require(schema.node.get("format", "hex") == "hex", f"{where}: a format other than hex")


def _branches(schema: Schema, where: str) -> list[Schema]:
    """The branches of allOf in a schema, or none."""
    branches = _list(schema.node.get("allOf", []), where)
    return [Schema(_mapping(branch, where), schema.file) for branch in branches]


def _is_object(schema: Schema) -> bool:
    """Whether a schema describes an object, directly, by a reference or by a branch of allOf."""
    reference = schema.node.get("$ref")
    if isinstance(reference, str):
        return _is_object(_resolve(reference, schema.file))
    return schema.node.get("type") == "object" or any(
        _is_object(branch) for branch in _branches(schema, schema.file)
    )


def _properties(schema: Schema, where: str) -> tuple[dict[str, Schema], set[str]]:
    """The properties of an object schema and its required keys, merged across allOf."""
    _check_keywords(schema, where)
    reference = schema.node.get("$ref")
    if isinstance(reference, str):
        return _properties(_resolve(reference, schema.file), where)
    children = _mapping(schema.node.get("properties", {}), where)
    properties = {
        key: Schema(_mapping(child, where), schema.file) for key, child in children.items()
    }
    required = set()
    for key in _list(schema.node.get("required", []), where):
        if not isinstance(key, str):
            raise SchemaError(f"{where}: the required key {key!r}")
        required.add(key)
    for branch in _branches(schema, where):
        more, more_required = _properties(branch, where)
        _require(not properties.keys() & more.keys(), f"{where}: a key in two branches")
        properties |= more
        required |= more_required
    return properties, required


def _check_length(value: object, node: Mapping[str, object], where: str) -> None:
    """Check the bounds that a schema sets on the length of a string."""
    if "minLength" in node or "maxLength" in node:
        if not isinstance(value, str):
            raise SchemaError(f"{where}: {value!r} is no string")
        low, high = _int(node, "minLength", 0), _int(node, "maxLength", len(value))
        _require(
            low <= len(value) <= high, f"{where}: {len(value)} characters, not {low} to {high}"
        )


@functools.cache
def _pattern(pattern: str) -> re.Pattern[str]:
    """A pattern of the types files, compiled once with the meaning that JSON Schema gives it."""
    # JSON Schema patterns are ECMA-262 regular expressions, where $ matches only at the end.
    # In Python, $ also matches before a final newline, so the final $ becomes \Z.
    # Each pattern of the vendored files starts with ^ and ends with $.
    _require(pattern.startswith("^") and pattern.endswith("$"), f"the pattern {pattern} is open")
    return re.compile(pattern[:-1] + r"\Z", re.ASCII)


def _conform(
    value: object,
    schema: Schema,
    path: Location,
    leaves: list[Leaf],
    *,
    bounds: bool,
    type_name: str = "",
    example: str | None = None,
) -> None:
    """Check a JSON value against a schema, and add each string of the value to the leaves."""
    # The schemas give the bounds of lists and strings for the mainnet preset.
    # So `bounds` is false for the cases of the minimal preset.
    where = f"{schema.file} at {path}"
    _check_keywords(schema, where)
    node = schema.node
    found = node.get("example")
    # An example beside a reference replaces the example of the schema that it names.
    if example is None and isinstance(found, str):
        example = found
    reference = node.get("$ref")
    if isinstance(reference, str):
        _require(set(node) <= REFERENCE_KEYWORDS, f"{where}: keywords beside a reference")
        if bounds:
            _check_length(value, node, where)
        target = _resolve(reference, schema.file)
        name = reference.rsplit("/", 1)[-1]
        _conform(value, target, path, leaves, bounds=bounds, type_name=name, example=example)
        return
    if "allOf" in node and not _is_object(schema):
        # A value that is no object conforms to each branch, such as a reference and a description.
        for branch in _branches(schema, where):
            _conform(value, branch, path, leaves, bounds=bounds, example=example)
        return
    if not node.keys() & {"type", "allOf"}:
        # A schema of a description alone constrains nothing.
        return
    kind = node.get("type", "object")
    if kind == "object":
        properties, required = _properties(schema, where)
        declared = sorted(properties)
        _require(required == set(declared), f"{where}: required {sorted(required)}, not {declared}")
        if not isinstance(value, dict):
            raise SchemaError(f"{where}: {value!r} is no object")
        keys, expected = sorted(value), sorted(properties)
        _require(keys == expected, f"{where}: keys {keys}, not {expected}")
        for key, child in properties.items():
            _conform(value[key], child, (*path, key), leaves, bounds=bounds)
    elif kind == "array":
        if not isinstance(value, list):
            raise SchemaError(f"{where}: {value!r} is no array")
        if bounds:
            low, high = _int(node, "minItems", 0), _int(node, "maxItems", len(value))
            _require(low <= len(value) <= high, f"{where}: {len(value)} items, not {low} to {high}")
        items = Schema(_mapping(node.get("items"), where), schema.file)
        for index, item in enumerate(value):
            _conform(item, items, (*path, index), leaves, bounds=bounds)
    elif kind == "string":
        if not isinstance(value, str):
            raise SchemaError(f"{where}: {value!r} is no string")
        if bounds:
            _check_length(value, node, where)
        # Some strings, such as Uint64, have no pattern, so that any string conforms.
        source = node.get("pattern")
        if source is not None:
            if not isinstance(source, str):
                raise SchemaError(f"{where}: the pattern {source!r}")
            pattern = _pattern(source)
            _require(bool(pattern.search(value)), f"{where}: {value!r} against {source}")
            if example is not None:
                _require(bool(pattern.search(example)), f"{where}: the example {example!r}")
        leaves.append(Leaf(path, type_name, example))
    elif kind == "boolean":
        _require(isinstance(value, bool), f"{where}: {value!r} is no boolean")
    else:
        raise SchemaError(f"{where}: the type {kind!r}")


def _leaves(document: object, schema: Schema, *, bounds: bool) -> list[Leaf]:
    """Check that a document conforms to a schema, and give its strings."""
    leaves: list[Leaf] = []
    _conform(document, schema, (), leaves, bounds=bounds)
    return leaves


def _hex_case(value: object, case: Callable[[str], str]) -> object:
    """A JSON value with the digits of each hex string after 0x changed by the case function."""
    if isinstance(value, dict):
        return {key: _hex_case(child, case) for key, child in value.items()}
    if isinstance(value, list):
        return [_hex_case(child, case) for child in value]
    if isinstance(value, str) and value.startswith("0x"):
        return "0x" + case(value[2:])
    return value


def _at(document: object, path: Location) -> object:
    """The value at a path of a document."""
    for step in path:
        if isinstance(document, dict) and isinstance(step, str):
            document = document[step]
        elif isinstance(document, list) and isinstance(step, int):
            document = document[step]
        else:
            raise AssertionError(f"no value at {path}")
    return document


def _replaced(document: object, path: Location, value: str) -> object:
    """A copy of a document with the value at a path replaced."""
    if not path:
        return value
    step, rest = path[0], path[1:]
    if isinstance(document, dict) and isinstance(step, str):
        return {**document, step: _replaced(document[step], rest, value)}
    assert isinstance(document, list) and isinstance(step, int), f"no value at {path}"
    return [*document[:step], _replaced(document[step], rest, value), *document[step + 1 :]]


def _fits(leaf: Leaf, current: object) -> bool:
    """Whether the example of a leaf can stand in place of the string of the document."""
    assert leaf.example is not None and isinstance(current, str)
    if not leaf.example.startswith("0x") or leaf.type_name in VARIABLE_LENGTH:
        return True
    return len(leaf.example) == len(current)


def _shape(path: Location) -> str:
    """A path with each index of an array as a star."""
    return "/".join("*" if isinstance(step, int) else step for step in path)


@functools.cache
def _cases() -> tuple[tuple[str, str, str, Path], ...]:
    """Every vendored case at a fork that the types files describe."""
    # The types files describe only the forks that have a consensus version.
    cases = []
    for serialized in sorted(SSZ_STATIC.rglob("serialized.ssz_snappy")):
        case = serialized.parent
        preset, fork, _, container = case.relative_to(SSZ_STATIC).parts[:4]
        if _api_fork(fork) is not None:
            cases.append((preset, fork, container, case))
    return tuple(cases)


def _with_schema() -> list[tuple[str, str, str, Path]]:
    """The cases of the containers that the types files define."""
    return [case for case in _cases() if case[2] not in NO_SCHEMA]


def _size(case: Path) -> int:
    """The size of the compressed bytes of a case."""
    return (case / "serialized.ssz_snappy").stat().st_size


@functools.cache
def _largest() -> Mapping[tuple[str, str, str], Path]:
    """For each preset, fork and container with a schema, its case of the most compressed bytes."""
    # The examples replace one string at a time, so one case of each container keeps the run short.
    # The case of the most compressed bytes tends to have the most non-empty lists and strings.
    largest: dict[tuple[str, str, str], Path] = {}
    for preset, fork, container, case in _with_schema():
        best = largest.get((preset, fork, container))
        if best is None or _size(case) > _size(best):
            largest[preset, fork, container] = case
    return largest


def _identify(value: object) -> str | None:
    """The id of a case: its path under the ssz_static directory."""
    return value.relative_to(SSZ_STATIC).as_posix() if isinstance(value, Path) else None


def _data(case: Path) -> bytes:
    """The SSZ bytes of a case."""
    return snappy.decompress((case / "serialized.ssz_snappy").read_bytes())


def _read_examples(preset: str, fork: str, container: str, case: Path) -> set[tuple[str, str]]:
    """Read each example of the types in place of a string of a case, and give the leaves read."""
    # A leaf read is the name of its type and the shape of its path.
    # One string of each shape is enough, so the others are not read.
    schema = _schema(container, fork)
    assert schema is not None
    lean_fork = FORKS[fork]
    document = consensus.api_json(preset, lean_fork, container, _data(case))
    read: set[tuple[str, str]] = set()
    for leaf in _leaves(document, schema, bounds=preset == "mainnet"):
        shape = (leaf.type_name, _shape(leaf.path))
        if leaf.example is None or shape in read or not _fits(leaf, _at(document, leaf.path)):
            continue
        edited = _replaced(document, leaf.path, leaf.example)
        data = consensus.api_ssz(preset, lean_fork, container, edited)
        again = consensus.api_json(preset, lean_fork, container, data)
        assert again == _hex_case(edited, str.lower)
        read.add(shape)
    return read


def _largest_document(preset: str, fork: str, container: str) -> dict[str, Any]:
    """The JSON of the case of the most compressed bytes of a container at a preset and fork."""
    case = _largest()[preset, fork, container]
    return consensus.api_json(preset, FORKS[fork], container, _data(case))


def test_digests():
    lines = (BEACON_API / "SHA256SUMS").read_text(encoding="utf-8").splitlines()
    entries = [line.split() for line in lines if line.strip() and not line.startswith("#")]
    files = [path for path in BEACON_API.rglob("*") if path.is_file() and path.name != "SHA256SUMS"]
    names = sorted(path.relative_to(BEACON_API).as_posix() for path in files)
    assert sorted(name for _, name in entries) == names
    for digest, name in entries:
        assert hashlib.sha256((BEACON_API / name).read_bytes()).hexdigest() == digest, name


def test_fork_keys_are_the_consensus_versions():
    keys = {key for key, _ in _definitions()} - {""}
    versions = {_api_fork(fork) for fork in FORKS} - {None}
    assert keys == versions


def test_containers_without_a_schema():
    # The containers whose cases the schema tests skip are exactly the listed ones.
    missing = {
        (container, fork) for _, fork, container, _ in _cases() if not _schema(container, fork)
    }
    assert {container for container, _ in missing} == set(NO_SCHEMA)
    # Such a container has no schema at any fork, so no fork of another container passes in silence.
    for _, fork, container, _ in _cases():
        if container in NO_SCHEMA:
            assert (container, fork) in missing


@pytest.mark.parametrize(
    "reference, document, bounds, message",
    [
        pytest.param(
            "types/misc.yaml#/Checkpoint",
            {"epoch": "1"},
            False,
            "types/misc.yaml at (): keys ['epoch'], not ['epoch', 'root']",
            id="missing-key",
        ),
        pytest.param(
            "types/misc.yaml#/Checkpoint",
            {**CHECKPOINT, "slot": "1"},
            False,
            "types/misc.yaml at (): keys ['epoch', 'root', 'slot'], not ['epoch', 'root']",
            id="undeclared-key",
        ),
        pytest.param(
            "types/misc.yaml#/Checkpoint",
            {**CHECKPOINT, "epoch": 1},
            False,
            "types/primitive.yaml at ('epoch',): 1 is no string",
            id="number",
        ),
        pytest.param(
            "types/misc.yaml#/Checkpoint",
            {**CHECKPOINT, "root": "0x" + "00" * 32 + "\n"},
            False,
            "types/primitive.yaml at ('root',): "
            "'0x0000000000000000000000000000000000000000000000000000000000000000\\n' "
            "against ^0x[a-fA-F0-9]{64}$",
            id="final-newline",
        ),
        pytest.param(
            "types/misc.yaml#/Checkpoint",
            {**CHECKPOINT, "root": "0x00"},
            False,
            "types/primitive.yaml at ('root',): '0x00' against ^0x[a-fA-F0-9]{64}$",
            id="short-root",
        ),
        pytest.param(
            "types/altair/epoch_participation.yaml#/Altair/EpochParticipation",
            ["256"],
            False,
            "types/primitive.yaml at (0,): '256' against "
            "^([0-9]{1,2}|1[0-9]{2}|2[0-4][0-9]|25[0-5])$",
            id="flag-out-of-range",
        ),
        pytest.param(
            "types/altair/sync_committee.yaml#/Altair/SyncCommittee",
            {"pubkeys": ["0x" + "00" * 48], "aggregate_pubkey": "0x" + "00" * 48},
            True,
            "types/altair/sync_committee.yaml at ('pubkeys',): 1 items, not 512 to 512",
            id="mainnet-bounds",
        ),
        pytest.param(
            "types/gloas/payload_attestation.yaml#/Gloas/PayloadAttestation",
            {"aggregation_bits": "0x00", "data": {}, "signature": "0x"},
            True,
            "types/gloas/payload_attestation.yaml at ('aggregation_bits',): "
            "4 characters, not 130 to 130",
            id="length-beside-a-reference",
        ),
    ],
)
def test_the_validator_refuses_a_wrong_document(reference, document, bounds, message):
    # The documents of the bindings conform, so these show that the validator can refuse one.
    with raises(SchemaError, message):
        _leaves(document, _resolve(reference, ""), bounds=bounds)


def test_the_validator_refuses_an_unread_keyword():
    schema = Schema({"type": "string", "minimum": 1}, "types/primitive.yaml")
    with raises(SchemaError, "types/primitive.yaml at (): unread keywords ['minimum']"):
        _leaves("1", schema, bounds=False)


@pytest.mark.parametrize("preset, fork, container, case", _with_schema(), ids=_identify)
def test_json_conforms_to_the_types(preset, fork, container, case):
    schema = _schema(container, fork)
    assert schema is not None
    document = consensus.api_json(preset, FORKS[fork], container, _data(case))
    _leaves(document, schema, bounds=preset == "mainnet")


@pytest.mark.parametrize("preset, fork, container, case", _with_schema(), ids=_identify)
def test_json_reads_back_in_either_case(preset, fork, container, case):
    data = _data(case)
    document = consensus.api_json(preset, FORKS[fork], container, data)
    assert consensus.api_ssz(preset, FORKS[fork], container, document) == data
    upper = _hex_case(document, str.upper)
    assert consensus.api_ssz(preset, FORKS[fork], container, upper) == data


@pytest.mark.parametrize(
    "preset, fork, container, case",
    [(*key, case) for key, case in _largest().items()],
    ids=_identify,
)
def test_examples_read_in_place(preset, fork, container, case):
    read = _read_examples(preset, fork, container, case)
    assert read
    assert REQUIRED_EXAMPLES.get((preset, fork, container), set()) <= read


def test_required_examples_have_cases():
    # A required example of a container without a case would pass in silence.
    assert set(REQUIRED_EXAMPLES) <= set(_largest())


@pytest.mark.parametrize("directory, name, container, key", BUILDER_EXAMPLES)
def test_builder_examples(directory, name, container, key):
    # The builder specification writes these JSON forms apart from EthLib.
    examples = VECTORS / "builder_api" / directory
    data = (examples / f"{name}.ssz").read_bytes()
    value = json.loads((examples / f"{name}.json").read_text(encoding="utf-8"))["value"]
    expected = value[key] if key else value
    fork = consensus.consensus_version_fork(directory)
    assert consensus.api_json("mainnet", fork, container, data) == expected
    assert consensus.api_ssz("mainnet", fork, container, expected) == data


def _without(document: dict[str, Any], key: str) -> dict[str, Any]:
    """A copy of a document without one key."""
    return {name: value for name, value in document.items() if name != key}


def _with_key(document: dict[str, Any], key: str) -> dict[str, Any]:
    """A copy of a document with one more key."""
    return {**document, key: "1"}


def _first_withdrawal_with_key(document: dict[str, Any], key: str) -> dict[str, Any]:
    """A copy of a payload whose first withdrawal has one more key."""
    first, *rest = document["withdrawals"]
    return {**document, "withdrawals": [_with_key(first, key), *rest]}


def _flags_as_hex(document: dict[str, Any]) -> dict[str, Any]:
    """A copy of a state whose current participation flags are one hex string."""
    flags = bytes(int(flag) for flag in document["current_epoch_participation"])
    assert flags
    return {**document, "current_epoch_participation": "0x" + flags.hex()}


def _transactions_as_decimals(document: dict[str, Any]) -> dict[str, Any]:
    """A copy of a payload whose transactions are arrays of decimal bytes."""
    transactions = document["transactions"]
    assert any(transaction != "0x" for transaction in transactions)
    arrays = [[str(byte) for byte in bytes.fromhex(item[2:])] for item in transactions]
    return {**document, "transactions": arrays}


@pytest.mark.parametrize(
    "fork, container, edit, message",
    [
        pytest.param(
            "altair",
            "BeaconState",
            _flags_as_hex,
            "document rejected: EthLib.Serialization.Ssz.Err.typeMismatch",
            id="flags-as-hex",
        ),
        pytest.param(
            "gloas",
            "ExecutionPayload",
            _transactions_as_decimals,
            "document rejected: EthLib.Serialization.Ssz.Err.elementKind",
            id="gloas-transactions-as-decimal-arrays",
        ),
        pytest.param(
            "gloas",
            "ExecutionPayload",
            lambda document: _with_key(document, "slot"),
            'document rejected: EthLib.Serialization.Ssz.Err.undeclaredField "slot"',
            id="undeclared-key",
        ),
        pytest.param(
            "gloas",
            "ExecutionPayload",
            lambda document: _first_withdrawal_with_key(document, "slot"),
            'document rejected: EthLib.Serialization.Ssz.Err.undeclaredField "slot"',
            id="undeclared-key-in-a-list",
        ),
        pytest.param(
            "gloas",
            "ExecutionPayload",
            lambda document: _without(document, "block_access_list"),
            'document rejected: EthLib.Serialization.Ssz.Err.missingField "block_access_list"',
            id="missing-key",
        ),
        pytest.param(
            "phase0",
            "Validator",
            lambda document: {**document, "slashed": "false"},
            "document rejected: EthLib.Serialization.Ssz.Err.typeMismatch",
            id="boolean-as-string",
        ),
    ],
)
def test_wrong_documents_are_refused(fork, container, edit, message):
    edited = edit(_largest_document("minimal", fork, container))
    with raises(SszError, message):
        consensus.api_ssz("minimal", FORKS[fork], container, edited)


@pytest.mark.parametrize(
    "fork, container, data, message",
    [
        pytest.param(
            "phase0",
            "Checkpoint",
            b"\x00",
            "input rejected: EthLib.Serialization.Ssz.Err.scope {n} {n}",
            id="truncated-bytes",
        ),
        pytest.param(
            "phase0", "NoSuchContainer", b"", "no container NoSuchContainer at phase0", id="unknown"
        ),
    ],
)
def test_wrong_bytes_are_refused(fork, container, data, message):
    with raises_shape(SszError, message):
        consensus.api_json("minimal", fork, container, data)
