"""The cases of the official test suites at every fork in scope."""

import hashlib
import json
from dataclasses import dataclass
from functools import cache
from pathlib import Path

import archives

EXECUTION = "execution-specs/tests@v21.0.2/fixtures"
# The devnet pre-releases of execution-spec-tests, by the suite name of their report.
DEVNETS = {
    "tests-heze-devnet": "execution-specs/tests-heze-devnet@v3.0.0/fixtures",
    "tests-bogota-devnet": "execution-specs/tests-bogota-devnet@v2.0.0/fixtures",
}
CONSENSUS = {
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
}

# The source of ethereum/legacytests at its pinned commit, and the directory that holds its files.
LEGACY = "legacytests@1f581b8c/source"
LEGACY_ROOT = "legacytests-1f581b8ccdc4c63acf5f2c5c1b155c690c32a8eb"

# The state tests of ethereum/tests in the form of blockchain tests.
# Each runs its one block through the state transition only.
LEGACY_STATE_DIRECTORIES = (
    "Constantinople/BlockchainTests/GeneralStateTests",
    "Cancun/BlockchainTests/GeneralStateTests",
)

# The blockchain tests of ethereum/legacytests.
# The directory Constantinople holds the networks up to Constantinople Fix.
# The directory Cancun holds the later ones.
LEGACY_DIRECTORIES = (
    "Constantinople/BlockchainTests/ValidBlocks",
    "Constantinople/BlockchainTests/InvalidBlocks",
    "Cancun/BlockchainTests/ValidBlocks",
    "Cancun/BlockchainTests/InvalidBlocks",
    "Cancun/BlockchainTests/TransitionTests",
    *LEGACY_STATE_DIRECTORIES,
)

# The forged blocks name no exception, so no check can tell why a client rejects them.
LEGACY_FORGED = "bcForgedTest"

# The networks of the legacy blockchain tests from Frontier to London, with the forks of EthLib.
# A transition network takes its first fork before block 5, and its second from block 5 on.
# Each transition comes after the fork that it leaves.
LEGACY_FORKS = {
    "Frontier": ("frontier",),
    "FrontierToHomesteadAt5": ("frontier", "homestead"),
    "Homestead": ("homestead",),
    "HomesteadToDaoAt5": ("homestead", "daoFork"),
    "HomesteadToEIP150At5": ("homestead", "tangerineWhistle"),
    "EIP150": ("tangerineWhistle",),
    "EIP158": ("spuriousDragon",),
    "EIP158ToByzantiumAt5": ("spuriousDragon", "byzantium"),
    "Byzantium": ("byzantium",),
    "ByzantiumToConstantinopleFixAt5": ("byzantium", "petersburg"),
    "Constantinople": ("constantinople",),
    "ConstantinopleFix": ("petersburg",),
    "Istanbul": ("istanbul",),
    "Berlin": ("berlin",),
    "BerlinToLondonAt5": ("berlin", "london"),
    "London": ("london",),
}

# The network Constantinople runs EIP-1283, which EIP-1716 removed before the fork reached mainnet.
# EthLib treats Constantinople as Petersburg, so the state transition leaves that network out.
# Its headers, ommers and rewards are those of Petersburg, so the other groups run it.
LEGACY_EIP1283 = "Constantinople"

# The networks of the legacy blockchain tests that are out of scope.
# From Paris on, execution-spec-tests covers each fork.
# The transition to Paris at a total difficulty needs a rule that EthLib leaves out (decision 39).
LEGACY_OUT_OF_SCOPE = {
    "Paris",
    "Shanghai",
    "Cancun",
    "ParisToShanghaiAtTime15k",
    "ShanghaiToCancunAtTime15k",
    "ArrowGlacierToParisAtDiffC0000",
}

# The formats of execution-spec-tests that the parity covers.
# The format blockchain_test_sync checks a client's sync, which no specification defines.
FORMATS = (
    "state_test",
    "blockchain_test",
    "blockchain_test_engine",
    "blockchain_test_engine_x",
    "transaction_test",
)

# The networks of execution-spec-tests from Frontier to Amsterdam.
# Each transition comes after the fork that it leaves.
# The BPO scenario networks after Amsterdam change only the blob schedule of the chain.
EXECUTION_FORKS = (
    "Frontier",
    "Homestead",
    "TangerineWhistle",
    "SpuriousDragon",
    "Byzantium",
    "ConstantinopleFix",
    "Istanbul",
    "Berlin",
    "London",
    "Paris",
    "ParisToShanghaiAtTime15k",
    "Shanghai",
    "ShanghaiToCancunAtTime15k",
    "Cancun",
    "CancunToPragueAtTime15k",
    "Prague",
    "PragueToOsakaAtTime15k",
    "Osaka",
    "OsakaToBPO1AtTime15k",
    "BPO1",
    "BPO1ToBPO2AtTime15k",
    "BPO2",
    "BPO2ToBPO3AtTime15k",
    "BPO3ToBPO4AtTime15k",
    "BPO2ToAmsterdamAtTime15k",
    "Amsterdam",
    "AmsterdamToBPOIncreaseAtTime15k",
    "AmsterdamBPOIncrease",
    "AmsterdamToBPODecreaseAtTime15k",
    "AmsterdamBPODecrease",
)

# The networks of the devnets from Bogota on, whose rules EthLib does not hold yet.
# Each devnet gives Bogota its own EIPs, so no case of these networks runs.
BOGOTA_NETWORKS = (
    "AmsterdamToBogotaAtTime15k",
    "Bogota",
    "BogotaToBPOIncreaseAtTime15k",
    "BogotaBPOIncrease",
    "BogotaToBPODecreaseAtTime15k",
    "BogotaBPODecrease",
)

# The forks of consensus-specs from Phase 0 to Heze.
CONSENSUS_FORKS = (
    "phase0",
    "altair",
    "bellatrix",
    "capella",
    "deneb",
    "electra",
    "fulu",
    "gloas",
    "heze",
)


@dataclass(frozen=True)
class Case:
    """One case: its suite, preset, fork, group of cases, identifier and path in the archive."""

    suite: str
    preset: str
    fork: str
    group: str
    id: str
    path: str

    @property
    def row(self) -> str:
        """The row of the report: suite, preset, fork and runner, separated by spaces."""
        return " ".join((self.suite, self.preset or "-", self.fork, self.group.split("/")[0]))

    @property
    def rank(self) -> int:
        """The place of the case's fork on the timeline."""
        execution = EXECUTION_FORKS + BOGOTA_NETWORKS
        forks = {
            "execution-spec-tests": execution,
            **dict.fromkeys(DEVNETS, execution),
            "legacytests": tuple(LEGACY_FORKS),
        }
        return forks.get(self.suite, CONSENSUS_FORKS).index(self.fork)


# The index of a release of execution-spec-tests, in its archive.
INDEX = "fixtures/.meta/index.json"


def execution_index(name: str = EXECUTION) -> list[dict]:
    """The entries of the index of a release: one fixture each, with its format and network."""
    return _read_index(archives.unpack(name, INDEX))


def _read_index(root: Path) -> list[dict]:
    return json.loads((root / INDEX).read_text())["test_cases"]


def execution_cases() -> list[Case]:
    """Every fixture of the formats in scope, from the index of the release."""
    return [
        Case(
            "execution-spec-tests",
            "",
            entry["fork"],
            entry["format"],
            entry["id"],
            "fixtures/" + entry["json_path"],
        )
        for entry in execution_index()
        if entry["format"] in FORMATS and entry["fork"] in EXECUTION_FORKS
    ]


def devnet_cases(suite: str) -> list[Case]:
    """The cases of a devnet whose identifier the pinned release lacks.

    The list is computed once and kept in the cache, since both indexes take gigabytes to read.
    """
    # A case that the pinned release holds with another hash is a refill of the same test.
    # The Heze devnet refills about 134,000 cases, which take about 11 hours on four workers.
    name = DEVNETS[suite]
    pinned = archives.fetch_archives.load(archives.REPO)[EXECUTION]
    devnet = archives.fetch_archives.load(archives.REPO)[name]
    scope = json.dumps([FORMATS, EXECUTION_FORKS, BOGOTA_NETWORKS]).encode()
    key = hashlib.sha256(pinned.sha256.encode() + devnet.sha256.encode() + scope).hexdigest()
    listing = archives.CACHE / f"{devnet.sha256}.new-cases-{key[:16]}.json"
    # Both indexes are unpacked before the lock, since unpacking takes the same lock.
    roots = archives.unpack(EXECUTION, INDEX), archives.unpack(name, INDEX)
    # One process computes the list while the others wait, so one process reads the indexes.
    with archives.fetch_archives.locked(archives.CACHE, devnet):
        if not listing.is_file():
            known = {
                (entry["id"], entry["format"], entry["fork"]) for entry in _read_index(roots[0])
            }
            entries = [
                (entry["fork"], entry["format"], entry["id"], "fixtures/" + entry["json_path"])
                for entry in _read_index(roots[1])
                if entry["format"] in FORMATS
                and entry["fork"] in EXECUTION_FORKS + BOGOTA_NETWORKS
                and (entry["id"], entry["format"], entry["fork"]) not in known
            ]
            listing.write_text(json.dumps(entries))
    return [
        Case(suite, "", fork, group, ident, path)
        for fork, group, ident, path in json.loads(listing.read_text())
    ]


def consensus_cases() -> list[Case]:
    """Every case directory of both presets, at the forks from Phase 0 to Heze."""
    cases = set()
    for preset, name in CONSENSUS.items():
        archive = archives.fetch_archives.load(archives.REPO)[name]
        for member in archives.fetch_archives.members(archive, archives.CACHE):
            # tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>/<file>
            parts = member.split("/")
            if len(parts) == 8 and parts[1] == preset and parts[2] in CONSENSUS_FORKS:
                path = "/".join(parts[:7])
                cases.add(
                    Case(
                        "consensus-spec-tests",
                        preset,
                        parts[2],
                        f"{parts[3]}/{parts[4]}",
                        path,
                        path,
                    )
                )
    return sorted(cases, key=lambda case: case.path)


def legacy_networks(root: Path) -> set[str]:
    """Every network of the legacy blockchain tests under `root`."""
    return {network for _, _, network, _ in _legacy_index(root)}


def legacy_cases(root: Path) -> list[Case]:
    """Every legacy blockchain test from Frontier to London under `root`, once per group."""
    return [
        Case("legacytests", "", network, group, f"{path}::{name}", path)
        for path, name, network, groups in _legacy_index(root)
        if network in LEGACY_FORKS and LEGACY_FORGED not in path.split("/")
        for group in groups
    ]


def _legacy_groups(directory: str, fixture: dict) -> tuple[str, ...]:
    """The groups of runners of a test: the state transition, headers, ommers and the DAO Fork."""

    # An error in the header of an ommer belongs to the header checks.
    def ommers(entry: dict) -> bool:
        named = any(
            "Uncle" in value for key, value in entry.items() if key.startswith("expectException")
        )
        return named or ("blockHeader" in entry and bool(entry.get("uncleHeaders")))

    network = fixture["network"]
    transition = () if network == LEGACY_EIP1283 else ("legacy_blockchain",)
    if directory in LEGACY_STATE_DIRECTORIES:
        return transition
    groups = (*transition, "legacy_header")
    if any(ommers(entry) for entry in fixture["blocks"]):
        groups += ("legacy_ommers",)
    if "daoFork" in LEGACY_FORKS.get(network, ()):
        groups += ("legacy_dao",)
    return groups


@cache
def _legacy_index(root: Path) -> tuple[tuple[str, str, str, tuple[str, ...]], ...]:
    """Each blockchain test under `root`: its path from `root`, its name, network and groups."""
    index = []
    for directory in LEGACY_DIRECTORIES:
        for path in sorted((root / directory).rglob("*.json")):
            for name, fixture in json.loads(path.read_text()).items():
                index.append(
                    (
                        path.relative_to(root).as_posix(),
                        name,
                        fixture["network"],
                        _legacy_groups(directory, fixture),
                    )
                )
    return tuple(index)
