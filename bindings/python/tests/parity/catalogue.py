"""The cases of execution-spec-tests and consensus-spec-tests at every fork in scope."""

import json
from dataclasses import dataclass

import archives

EXECUTION = "execution-specs/tests@v21.0.2/fixtures"
CONSENSUS = {
    "mainnet": "consensus-specs/v1.7.0-beta.4/mainnet",
    "minimal": "consensus-specs/v1.7.0-beta.4/minimal",
}

# The formats of execution-spec-tests that the parity covers.
# The format blockchain_test_sync checks a client's sync, which no specification defines.
FORMATS = ("state_test", "blockchain_test", "blockchain_test_engine",
           "blockchain_test_engine_x", "transaction_test")

# The networks of execution-spec-tests from Frontier to BPO2.
# Each transition comes after the fork that it leaves.
EXECUTION_FORKS = (
    "Frontier", "Homestead", "TangerineWhistle", "SpuriousDragon", "Byzantium",
    "ConstantinopleFix", "Istanbul", "Berlin", "London", "Paris", "ParisToShanghaiAtTime15k",
    "Shanghai", "ShanghaiToCancunAtTime15k", "Cancun", "CancunToPragueAtTime15k", "Prague",
    "PragueToOsakaAtTime15k", "Osaka", "OsakaToBPO1AtTime15k", "BPO1", "BPO1ToBPO2AtTime15k",
    "BPO2",
)

# The forks of consensus-specs from Phase 0 to Fulu.
CONSENSUS_FORKS = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu")


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
        forks = EXECUTION_FORKS if self.suite == "execution-spec-tests" else CONSENSUS_FORKS
        return forks.index(self.fork)


def execution_index() -> list[dict]:
    """The entries of the index of the release: one fixture each, with its format and network."""
    root = archives.unpack(EXECUTION, "fixtures/.meta/index.json")
    return json.loads((root / "fixtures/.meta/index.json").read_text())["test_cases"]


def execution_cases() -> list[Case]:
    """Every fixture of the formats in scope, from the index of the release."""
    return [Case("execution-spec-tests", "", entry["fork"], entry["format"], entry["id"],
                 "fixtures/" + entry["json_path"])
            for entry in execution_index()
            if entry["format"] in FORMATS and entry["fork"] in EXECUTION_FORKS]


def consensus_cases() -> list[Case]:
    """Every case directory of both presets, at the forks from Phase 0 to Fulu."""
    cases = set()
    for preset, name in CONSENSUS.items():
        archive = archives.fetch_archives.load(archives.REPO)[name]
        for member in archives.fetch_archives.members(archive, archives.CACHE):
            # tests/<preset>/<fork>/<runner>/<handler>/<suite>/<case>/<file>
            parts = member.split("/")
            if len(parts) == 8 and parts[1] == preset and parts[2] in CONSENSUS_FORKS:
                path = "/".join(parts[:7])
                cases.add(Case("consensus-spec-tests", preset, parts[2],
                               f"{parts[3]}/{parts[4]}", path, path))
    return sorted(cases, key=lambda case: case.path)
