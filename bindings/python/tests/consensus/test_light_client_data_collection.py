"""The light client data collection vectors of consensus-specs."""

from pathlib import Path

import pytest
from ruamel.yaml import YAML

from ethlib import consensus
from ethlib.networking import snappy

from .containers import FORKS
from .test_light_client_sync import FILES, SPECIFIED, case_config, fork_digests

_YAML = YAML(typ="safe")

# The size of a beacon block header, the first field of a light client header.
BEACON = 112

# The forks whose blocks the state transition of EthLib processes.
# A case whose forks are all among them runs every block, across the fork boundaries, and its
# served data is checked against what the full node functions give from the post states.
TRANSITION = ("altair", "bellatrix", "capella", "deneb")


def runs_data_collection(fork: str, name: str) -> bool:
    """Whether EthLib runs a data collection case: every case from Altair."""
    return fork in SPECIFIED


def _case_forks(fork: str, name: str) -> list:
    """The forks of a case: its own, and those that a reorg case names, such as `capella_deneb`."""
    return [fork] + (name.split("_reorg_")[0].split("_") if "_reorg_" in name else [])


def _transition_runs(fork: str, name: str) -> bool:
    """Whether the blocks of a case go through the state transition."""
    return all(each in TRANSITION for each in _case_forks(fork, name))


def _read(case: Path, name: str) -> bytes:
    return snappy.decompress((case / f"{name}.ssz_snappy").read_bytes())


def _uint(data: bytes) -> int:
    return int.from_bytes(data, "little")


class Shapes:
    """The sizes of the fields of the light client containers, for a preset and a fork."""

    def __init__(self, preset: str, fork: str):
        size = consensus.preset(preset)["SYNC_COMMITTEE_SIZE"]
        self.committee = size * 48 + 48
        self.aggregate = size // 8 + 96
        # From Capella to Fulu a header has variable size; from Electra the state is deeper.
        # From Gloas a header is fixed again: the beacon header, a hash and a branch of 11 nodes.
        at = SPECIFIED.index(fork)
        gloas = at >= SPECIFIED.index("gloas")
        electra = at >= SPECIFIED.index("electra")
        self.variable = SPECIFIED.index("capella") <= at and not gloas
        self.header = BEACON + 32 + 11 * 32 if gloas else BEACON
        self.committee_branch = 32 * (11 if gloas else 6 if electra else 5)
        self.finality_branch = 32 * (9 if gloas else 7 if electra else 6)
        self.slot = 8

    def split(self, data: bytes, fields: list) -> list:
        """The bytes of each field of a container; a field named `header` is a header."""
        sizes = [None if field == "header" else getattr(self, field) for field in fields]
        if not self.variable:
            sizes = [self.header if size is None else size for size in sizes]
        parts, offsets, at = [], [], 0
        for size in sizes:
            if size is None:
                offsets.append(len(parts))
                parts.append(_uint(data[at:at + 4]))
                at += 4
            else:
                parts.append(data[at:at + size])
                at += size
        # Each variable field runs from its offset to the next offset, or to the end.
        ends = [parts[i] for i in offsets[1:]] + [len(data)]
        for i, end in zip(offsets, ends):
            parts[i] = data[parts[i]:end]
        return parts


class Chain:
    """The blocks of a case, with the light client header that EthLib derives from each."""

    def __init__(self, case: Path, preset: str):
        self.case, self.preset = case, preset
        self.values, self.config = case_config(case, preset)
        state = _read(case, "initial_state")
        root = state[8:40]
        self.digests = fork_digests(self.values, preset, root, self.config)
        self.genesis_validators_root = root
        # The block of the initial state is not in the case, so its header comes from the state.
        epoch = _uint(state[40:48]) // consensus.preset(preset)["SLOTS_PER_EPOCH"]
        self.state_fork = [fork for fork in SPECIFIED
                           if self.values[f"{fork.upper()}_FORK_EPOCH"] <= epoch][-1]
        latest = state[64:64 + BEACON]
        if not any(latest[48:80]):
            state_root = consensus.ssz_static(preset, FORKS[self.state_fork], "BeaconState",
                                              state)[0]
            latest = latest[:48] + state_root + latest[80:]
        self.initial_state, self.initial_root = state, self.beacon_root(latest)
        self.headers = {self.initial_root: (None, latest)}
        self.slots = {}

    def beacon_root(self, beacon: bytes) -> bytes:
        return consensus.ssz_static(self.preset, FORKS["altair"], "BeaconBlockHeader", beacon)[0]

    def add_block(self, fork: str, name: str) -> None:
        """Derive the header of a block, and index it by its root and its slot."""
        root, header = consensus.block_to_light_client_header(
            self.preset, FORKS[fork], _read(self.case, name), self.config)
        assert self.beacon_root(header[:BEACON]) == root
        self.headers[root] = (header, header[:BEACON])
        self.slots.setdefault(_uint(header[:8]), []).append(header[:BEACON])

    def check_header(self, header: bytes, empty_allowed: bool = False) -> bytes:
        """Check a served header against the block it names, and return that block's root."""
        # The proof check already holds the rest of a header with a zero beacon header to zero.
        if empty_allowed and not any(header[:BEACON]):
            return bytes(32)
        root = self.beacon_root(header[:BEACON])
        derived, beacon = self.headers[root]
        assert header[:BEACON] == beacon
        if derived is not None:
            assert header == derived
        return root

    def check_signature_slot(self, attested: bytes, slot: int) -> None:
        """A block of the case at the signature slot has the attested block as its parent."""
        assert any(beacon[16:48] == attested for beacon in self.slots.get(slot, []))


class Block:
    """A block of a full node: its fork, its signed bytes, its slot, its parent and post state."""

    def __init__(self, fork: str, signed: bytes, post: bytes):
        self.fork, self.signed, self.post = fork, signed, post
        message = signed[100:]
        self.slot, self.parent = _uint(message[:8]), message[16:48]
        self.body = message[_uint(message[80:84]):]
        self.bootstrap = None


class FullNode:
    """The blocks of a case with their post states, and the data a full node serves from them."""

    def __init__(self, chain: Chain):
        self.chain = chain
        preset = consensus.preset(chain.preset)
        self.slots_per_epoch = preset["SLOTS_PER_EPOCH"]
        self.period_slots = self.slots_per_epoch * preset["EPOCHS_PER_SYNC_COMMITTEE_PERIOD"]
        self.committee_size = preset["SYNC_COMMITTEE_SIZE"]
        self.min_participants = preset["MIN_SYNC_COMMITTEE_PARTICIPANTS"]
        # The finalized checkpoint follows the fields that every fork keeps from Phase 0.
        self.finalized_at = (8 + 32 + 8 + 16 + BEACON + 2 * 32 * preset["SLOTS_PER_HISTORICAL_ROOT"]
                             + 4 + 72 + 4 + 8 + 4 + 4
                             + 32 * preset["EPOCHS_PER_HISTORICAL_VECTOR"]
                             + 8 * preset["EPOCHS_PER_SLASHINGS_VECTOR"] + 4 + 4 + 1 + 40 + 40)
        fork, state = chain.state_fork, chain.initial_state
        genesis = consensus.genesis_block(chain.preset, FORKS[fork], state)
        root = consensus.ssz_static(chain.preset, FORKS[fork], "BeaconBlock", genesis[100:])[0]
        # The initial state is that of the genesis block, so the two roots agree.
        assert root == chain.initial_root
        self.blocks = {root: Block(fork, genesis, state)}
        # The data collection starts at the slot of the initial state.
        self.tail = self.blocks[root].slot
        epoch, finalized = self.finalized(state)
        self.latest = (epoch, finalized, epoch * self.slots_per_epoch)
        self.updates = {}

    def finalized(self, state: bytes) -> tuple[int, bytes]:
        """The epoch and the root of the finalized checkpoint of a state."""
        checkpoint = state[self.finalized_at:self.finalized_at + 40]
        return _uint(checkpoint[:8]), checkpoint[8:]

    def participants(self, block: Block) -> int:
        """The number of members of the sync committee that signed a block."""
        bits = block.body[220:220 + self.committee_size // 8]
        return sum(bin(byte).count("1") for byte in bits)

    def period(self, slot: int) -> int:
        return slot // self.period_slots

    def add_block(self, fork: str, name: str) -> None:
        """Run a block through the state transition from the post state of its parent."""
        signed = _read(self.chain.case, name)
        parent = self.blocks[signed[100:][16:48]]
        # The parent's state upgrades at each fork epoch between the two blocks.
        post = consensus.state_transition_across(self.chain.preset, FORKS[parent.fork],
                                                 parent.post, FORKS[fork], signed, True,
                                                 config=self.chain.config)
        root = consensus.ssz_static(self.chain.preset, FORKS[fork], "BeaconBlock",
                                    signed[100:])[0]
        self.blocks[root] = Block(fork, signed, post)

    def ancestry(self, root: bytes) -> list:
        """The blocks from a block back to the genesis block, newest first."""
        chain = []
        while root in self.blocks:
            chain.append(self.blocks[root])
            root = self.blocks[root].parent
        return chain

    def update(self, kind: str, signature: Block) -> bytes:
        """The update of a kind that a block gives, as the full node functions build it."""
        key = (kind, signature.signed)
        if key not in self.updates:
            attested = self.blocks[signature.parent]
            epoch, root = self.finalized(attested.post)
            # A zero root is the genesis checkpoint, whose block is at the genesis slot.
            finalized = (self.blocks[self.chain.initial_root] if not any(root)
                         else self.blocks.get(root))
            # The update is of the attested block's fork, which may precede the signature's.
            self.updates[key] = consensus.create_light_client_update(
                self.chain.preset, FORKS[signature.fork], kind, signature.post,
                signature.signed, attested.post, attested.signed,
                finalized.signed if finalized else None, config=self.chain.config,
                attested_fork=FORKS[attested.fork],
                finalized_fork=FORKS[finalized.fork] if finalized else None)
        return self.updates[key]

    def candidates(self, head: list, period: int) -> list:
        """The blocks of the head's chain whose update can be the best of a period."""
        return [block for block in head[:-1]
                if block.parent in self.blocks
                and self.blocks[block.parent].slot >= self.tail
                and self.period(self.blocks[block.parent].slot) == period
                and self.period(block.slot) == period
                and self.participants(block) >= self.min_participants]

    def check_head(self, head_root: bytes, checks: dict) -> None:
        """Check the data served after a new head against what the post states give."""
        preset, head = self.chain.preset, self.ancestry(bytes.fromhex(head_root[2:]))
        old_slot = self.latest[2]
        # The finalized checkpoint moves when the head's names a later block, on any branch.
        epoch, root = self.finalized(head[0].post)
        if epoch != 0 and self.blocks[root].slot > old_slot:
            self.latest = (epoch, root, self.blocks[root].slot)
        served = checks["latest_finalized_checkpoint"]
        assert (served["epoch"], bytes.fromhex(served["root"][2:])) == self.latest[:2]
        for entry in checks["bootstraps"]:
            if "bootstrap" not in entry:
                continue
            block = self.blocks[bytes.fromhex(entry["block_root"][2:])]
            fork = self.chain.digests[entry["bootstrap"]["fork_digest"]]
            if block.bootstrap is None:
                block.bootstrap = consensus.create_light_client_bootstrap(
                    preset, FORKS[fork], block.post, block.signed, config=self.chain.config)
            assert _read(self.chain.case, entry["bootstrap"]["data"]) == block.bootstrap
        for entry in checks["best_updates"]:
            candidates = self.candidates(head, entry["period"])
            if "update" not in entry:
                assert candidates == []
                continue
            fork = self.chain.digests[entry["update"]["fork_digest"]]
            data = _read(self.chain.case, entry["update"]["data"])
            # The served update is that of a block of the head's chain, and none ranks above it.
            # Each update is of its attested block's fork, and ranks at the later of two forks.
            assert data in [self.update("LightClientUpdate", block) for block in candidates]
            assert not any(consensus.is_better_update(
                preset, FORKS[self.blocks[block.parent].fork],
                self.update("LightClientUpdate", block), data, old_fork=FORKS[fork],
                config=self.chain.config)
                for block in candidates)
        # The latest updates come from the latest block of the head's chain with enough
        # signatures, after the finalized block, and from its parent as the attested block.
        low = max(self.tail, old_slot)
        signed = [block for block in head[:-1]
                  if self.participants(block) >= self.min_participants]
        latest = signed[0] if signed and signed[0].slot > low else None
        if latest is not None and self.blocks[latest.parent].slot < low:
            latest = None
        for key, kind in (("latest_finality_update", "LightClientFinalityUpdate"),
                          ("latest_optimistic_update", "LightClientOptimisticUpdate")):
            assert (key in checks) == (latest is not None)
            if latest is not None:
                assert _read(self.chain.case, checks[key]["data"]) == self.update(kind, latest)


def _check_new_head(chain: Chain, checks: dict) -> None:
    preset, config = chain.preset, chain.config
    for entry in checks["bootstraps"]:
        if "bootstrap" not in entry:
            continue
        fork = chain.digests[entry["bootstrap"]["fork_digest"]]
        data = _read(chain.case, entry["bootstrap"]["data"])
        # A store starts from the bootstrap only if it proves its committee for that block.
        root = bytes.fromhex(entry["block_root"][2:])
        consensus.light_client_sync(preset, FORKS[fork], FORKS[fork], root,
                                    chain.genesis_validators_root, data, [], config)
        header, _, _ = Shapes(preset, fork).split(data, ["header", "committee",
                                                         "committee_branch"])
        assert chain.check_header(header) == root
    for entry in checks["best_updates"]:
        if "update" not in entry:
            continue
        fork = chain.digests[entry["update"]["fork_digest"]]
        data = _read(chain.case, entry["update"]["data"])
        consensus.light_client_update_proofs(preset, FORKS[fork], "LightClientUpdate", data,
                                             config)
        attested, _, _, finalized, _, _, slot = Shapes(preset, fork).split(
            data, ["header", "committee", "committee_branch", "header", "finality_branch",
                   "aggregate"] + ["slot"])
        root = chain.check_header(attested)
        chain.check_header(finalized, empty_allowed=True)
        chain.check_signature_slot(root, _uint(slot))
        # An update counts for the period of its attested header, signed in that period.
        period = _period(preset)
        assert _uint(attested[:8]) // period == entry["period"] == _uint(slot) // period
    if "latest_finality_update" in checks:
        fork = chain.digests[checks["latest_finality_update"]["fork_digest"]]
        data = _read(chain.case, checks["latest_finality_update"]["data"])
        consensus.light_client_update_proofs(preset, FORKS[fork], "LightClientFinalityUpdate",
                                             data, config)
        attested, finalized, _, _, slot = Shapes(preset, fork).split(
            data, ["header", "header", "finality_branch", "aggregate", "slot"])
        chain.check_signature_slot(chain.check_header(attested), _uint(slot))
        chain.check_header(finalized, empty_allowed=True)
    if "latest_optimistic_update" in checks:
        fork = chain.digests[checks["latest_optimistic_update"]["fork_digest"]]
        data = _read(chain.case, checks["latest_optimistic_update"]["data"])
        attested, _, slot = Shapes(preset, fork).split(data, ["header", "aggregate", "slot"])
        chain.check_signature_slot(chain.check_header(attested), _uint(slot))


def _period(preset: str) -> int:
    """The number of slots of a sync committee period."""
    parameters = consensus.preset(preset)
    return parameters["SLOTS_PER_EPOCH"] * parameters["EPOCHS_PER_SYNC_COMMITTEE_PERIOD"]


def run_data_collection_case(case: Path, preset: str) -> None:
    """Check the light client data that a case serves after each new head."""
    # Each header must be the one that EthLib derives from its block, and each proof must verify.
    # Where the state transition runs the blocks, the full node functions must also give the
    # served data from the post states, and the chosen best update must rank above the others.
    chain = Chain(case, preset)
    node = FullNode(chain) if _transition_runs(case.parts[-5], case.name) else None
    for step in _YAML.load((case / "steps.yaml").read_text()):
        (kind, body), = step.items()
        if kind == "new_block":
            chain.add_block(chain.digests[body["fork_digest"]], body["data"])
            if node is not None:
                node.add_block(chain.digests[body["fork_digest"]], body["data"])
        else:
            assert kind == "new_head"
            _check_new_head(chain, body["checks"])
            if node is not None:
                node.check_head(body["head_block_root"], body["checks"])


def _cases() -> list:
    cases = []
    for steps in sorted(FILES.rglob("light_client/data_collection/pyspec_tests/*/steps.yaml")):
        case = steps.parent
        preset, fork = case.relative_to(FILES).parts[:2]
        if runs_data_collection(fork, case.name):
            cases.append(pytest.param(preset, case, id=case.relative_to(FILES).as_posix()))
    return cases


@pytest.mark.parametrize("preset, case", _cases())
def test_data_collection_case(preset, case):
    run_data_collection_case(case, preset)
