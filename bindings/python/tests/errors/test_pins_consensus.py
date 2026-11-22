"""The code and message of the errors that the consensus exports pass to Python."""

from collections.abc import Callable

import pytest

from consensus.test_attestation_data import phase0_state
from ethlib import consensus
from ethlib.consensus import history
from ethlib.errors import (
    ConsensusError,
    DepositTreeError,
    EraError,
    EthLibError,
    ForkChoiceError,
    KeymanagerError,
    KzgError,
    LightClientError,
    ProposerError,
    RemoteSigningError,
    SlashingProtectionError,
    SszError,
    TransitionError,
    ValidatorDutyError,
    WeakSubjectivityError,
)
from raising import raises

# A phase0 state of the mainnet preset at slot 1, with 64 validators.
STATE = phase0_state(1)

# A phase0 beacon block of zero fields, as SSZ bytes: 84 bytes of fixed fields, then the body.
BLOCK = bytes(80) + (84).to_bytes(4, "little") + bytes(200) + (220).to_bytes(4, "little") * 5

# An export turns the typed error of an operation into a code and a message.
# Each case pins one way of doing so, with the code and the message that Python sees.


@pytest.mark.parametrize(
    ("error", "code", "message", "call"),
    [
        # Zero slots later is still slot 1, not after the slot of the state.
        pytest.param(
            TransitionError,
            53,
            "EthLib.Consensus.TransitionError.slotNotAfter 1 1",
            lambda: consensus.process_slots("mainnet", "phase0", STATE, 0),
            id="transition",
        ),
        # The empty input is no beacon state.
        pytest.param(
            TransitionError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 2687377 0",
            lambda: consensus.process_slots("mainnet", "phase0", b"", 1),
            id="transition-input",
        ),
        # No preset has the name nope.
        pytest.param(
            TransitionError,
            0,
            "no preset is named nope",
            lambda: consensus.process_slots("nope", "phase0", b"", 1),
            id="transition-name",
        ),
        # The state at epoch 0 knows the committees up to epoch 1.
        pytest.param(
            ValidatorDutyError,
            5,
            "epoch 100 is after 1, the last epoch whose committees are known",
            lambda: consensus.get_committee_assignment("mainnet", "phase0", STATE, 100, 0),
            id="duty",
        ),
        # The empty input is no beacon state.
        pytest.param(
            ValidatorDutyError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 2687377 0",
            lambda: consensus.get_committee_assignment("mainnet", "phase0", b"", 0, 0),
            id="duty-input",
        ),
        # 71 bytes, where the Eth1 data of a candidate block is 72.
        pytest.param(
            ProposerError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scope 72 71",
            lambda: consensus.get_eth1_vote("mainnet", "phase0", STATE, [(0, bytes(71))]),
            id="proposer-input",
        ),
        # A block timestamp is a 64-bit number.
        pytest.param(
            ProposerError,
            0,
            "expected an int below 18446744073709551616, got 18446744073709551616",
            lambda: consensus.get_eth1_vote("mainnet", "phase0", STATE, [(2**64, bytes(72))]),
            id="proposer-argument",
        ),
        # The checkpoint names root 0x01... at epoch 0, and the state holds zero.
        pytest.param(
            WeakSubjectivityError,
            4,
            (
                "expected checkpoint root "
                "0x0101010101010101010101010101010101010101010101010101010101010101, got "
                "the block root "
                "0x0000000000000000000000000000000000000000000000000000000000000000 that "
                "the state holds at that epoch"
            ),
            lambda: consensus.is_within_weak_subjectivity_period(
                "mainnet", "phase0", STATE, bytes(8) + bytes([1]) * 32, 0, 0
            ),
            id="weak-subjectivity",
        ),
        # The empty input is no beacon state.
        pytest.param(
            WeakSubjectivityError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 2687377 0",
            lambda: consensus.compute_weak_subjectivity_period("mainnet", "phase0", b""),
            id="weak-subjectivity-input",
        ),
        # An empty tree has no deposit at index 0.
        pytest.param(
            DepositTreeError,
            5,
            "EthLib.Consensus.DepositTreeError.proofBeyondCount 0 0",
            lambda: consensus.deposit_tree_get_proof(consensus.deposit_tree_new(), 0),
            id="deposit-tree",
        ),
        # An empty object is not an EIP-3076 interchange file.
        pytest.param(
            SlashingProtectionError,
            1,
            "slashing protection failed with code 1",
            lambda: consensus.read_slashing_interchange(b"{}"),
            id="slashing-protection",
        ),
        # No Keymanager API schema has the name nope.
        pytest.param(
            KeymanagerError,
            0,
            "the Keymanager API has no schema nope",
            lambda: consensus.keymanager_json("nope", {}),
            id="keymanager",
        ),
        # An empty request has no type.
        pytest.param(
            RemoteSigningError,
            2,
            (
                "request rejected: "
                'EthLib.Consensus.RemoteSigningApi.RequestError.missingField "type"'
            ),
            lambda: consensus.read_signing_request("mainnet", {}),
            id="remote-signing",
        ),
        # A trusted block root is 32 bytes.
        pytest.param(
            LightClientError,
            0,
            "expected 32 bytes, got 31",
            lambda: consensus.light_client_sync(
                "minimal", "altair", "altair", bytes(31), bytes(32), b"", []
            ),
            id="light-client-argument",
        ),
        # The empty input is no bootstrap.
        pytest.param(
            LightClientError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scope 1856 0",
            lambda: consensus.light_client_sync(
                "minimal", "altair", "altair", bytes(32), bytes(32), b"", []
            ),
            id="light-client-input",
        ),
        # A domain type is 4 bytes.
        pytest.param(
            ForkChoiceError,
            0,
            "a domain type is 4 bytes, not 3",
            lambda: consensus.is_optimistic_restricted_domain(bytes(3)),
            id="fork-choice-argument",
        ),
        # The empty input is no anchor state.
        pytest.param(
            ForkChoiceError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 7057 0",
            lambda: consensus.api_header("minimal", "phase0", b"", b"", [], b""),
            id="fork-choice-input",
        ),
        # No preset has the name nope.
        pytest.param(
            ConsensusError,
            0,
            "no preset is named nope",
            lambda: consensus.preset("nope"),
            id="consensus-name",
        ),
        # Mainnet has 128 custody groups, below 200.
        pytest.param(
            ConsensusError,
            1,
            "custody group count 200 exceeds the number of groups",
            lambda: consensus.get_custody_groups(0, 200),
            id="consensus-custody",
        ),
        # 2^40 + 1 indices, above the 2^40 that shuffling allows.
        pytest.param(
            ConsensusError,
            204,
            "the index count 1099511627777 is above 2^40",
            lambda: consensus.compute_shuffled_permutation(2**40 + 1, bytes(32)),
            id="consensus-shuffle",
        ),
        # No protocol has the name nope.
        pytest.param(
            ConsensusError,
            0,
            "nope names no protocol",
            lambda: consensus.reqresp_request_bounds("phase0", "nope"),
            id="consensus-bounds",
        ),
        # The empty URL has no authority.
        pytest.param(
            ConsensusError,
            1,
            "EthLib.Consensus.BuilderApi.AuthDataError.noAuthority",
            lambda: consensus.default_auth_data(""),
            id="consensus-auth-data",
        ),
        # 39 bytes, where a checkpoint is 40.
        pytest.param(
            SszError,
            3,
            "input rejected: EthLib.Serialization.Ssz.Err.scope 40 39",
            lambda: consensus.merkle_proof("mainnet", "phase0", "Checkpoint", bytes(39), 1),
            id="consensus-ssz",
        ),
        # A blob is 131072 bytes.
        pytest.param(
            KzgError,
            0,
            "expected 131072 bytes, got 1",
            lambda: consensus.compute_matrix([bytes(1)]),
            id="consensus-kzg",
        ),
        # An era file starts with a version entry.
        pytest.param(
            EraError,
            1,
            (
                "era file rejected: EthLib.Consensus.History.EraError.e2store "
                "(EthLib.Serialization.E2store.E2storeError.noVersion none)"
            ),
            lambda: history.decode_era("mainnet", b""),
            id="era",
        ),
        # The block of zero fields names the zero root as its state root.
        pytest.param(
            ForkChoiceError,
            1,
            (
                "fork choice: expected the anchor state root "
                "0xfcf5affb9966e5caae520dfc8c9df1b9bff9e226002ef3728ad27cca78e090fe, got the "
                "block's state root "
                "0x0000000000000000000000000000000000000000000000000000000000000000"
            ),
            lambda: consensus.fork_choice("mainnet", "phase0", STATE, BLOCK, [], False),
            id="fork-choice",
        ),
        # The store knows no block, so not the one of the zero root.
        pytest.param(
            ForkChoiceError,
            2,
            "optimistic sync failed with code 2",
            lambda: consensus.latest_verified_ancestor("mainnet", "bellatrix", [], [], bytes(32)),
            id="optimistic-sync",
        ),
        # Optimistic sync starts at Bellatrix.
        pytest.param(
            ForkChoiceError,
            0,
            "no optimistic sync at phase0",
            lambda: consensus.is_execution_block("mainnet", "phase0", b""),
            id="optimistic-sync-fork",
        ),
        # The status of a payload is 0, 1 or 2.
        pytest.param(
            ForkChoiceError,
            0,
            "unknown payload status 7",
            lambda: consensus.latest_verified_ancestor(
                "mainnet", "bellatrix", [], [], bytes(32), 7
            ),
            id="optimistic-sync-status",
        ),
        # The light client starts at Altair.
        pytest.param(
            LightClientError,
            17,
            "light client: fork phase0 has no light client",
            lambda: consensus.light_client_sync(
                "minimal", "phase0", "phase0", bytes(32), bytes(32), b"", []
            ),
            id="light-client",
        ),
        # A bootstrap of Bellatrix is later than a store of Altair.
        pytest.param(
            LightClientError,
            0,
            "data of bellatrix is later than a store of altair",
            lambda: consensus.light_client_sync(
                "minimal", "altair", "bellatrix", bytes(32), bytes(32), b"", []
            ),
            id="light-client-fork",
        ),
        # The timestamp 2^64 - 1 overflows once the follow distance is added to it.
        pytest.param(
            ProposerError,
            1,
            "arithmetic: EthLib.Base.ArithError.overflow",
            lambda: consensus.get_eth1_vote("mainnet", "phase0", STATE, [(2**64 - 1, bytes(72))]),
            id="proposer",
        ),
        # Heze has no Eth1 vote.
        pytest.param(
            ProposerError,
            0,
            "no Eth1 vote at hegota",
            lambda: consensus.get_eth1_vote("mainnet", "hegota", b"", []),
            id="proposer-fork",
        ),
        # Phase 0 has no blob sidecar topic.
        pytest.param(
            ConsensusError,
            303,
            "blob_sidecar_0 is not a topic of phase0",
            lambda: consensus.gossip_topic_bound("phase0", "blob_sidecar_0"),
            id="gossip-topic-fork",
        ),
        # Phase 0 has no blob sidecar subnet.
        pytest.param(
            ConsensusError,
            101,
            "subnet rejected: EthLib.Networking.Gossip.SubnetError.zeroSubnetCount",
            lambda: consensus.compute_subnet_for_blob_sidecar("phase0", 0),
            id="gossip-subnet-blob",
        ),
        # No gossip topic has the name nope.
        pytest.param(
            ConsensusError,
            0,
            "nope names no topic",
            lambda: consensus.gossip_topic_bound("phase0", "nope"),
            id="gossip-topic-name",
        ),
        # Status version 2 comes after Phase 0.
        pytest.param(
            ConsensusError,
            301,
            "/eth2/beacon_chain/req/status/2/ssz_snappy is not a protocol of phase0",
            lambda: consensus.reqresp_request_bounds(
                "phase0", "/eth2/beacon_chain/req/status/2/ssz_snappy"
            ),
            id="reqresp-bounds",
        ),
        # A metadata request carries no payload.
        pytest.param(
            ConsensusError,
            302,
            "/eth2/beacon_chain/req/metadata/1/ssz_snappy carries no request",
            lambda: consensus.reqresp_request_bounds(
                "phase0", "/eth2/beacon_chain/req/metadata/1/ssz_snappy"
            ),
            id="reqresp-no-request",
        ),
        # Mainnet has 128 custody groups, so no group 200.
        pytest.param(
            ConsensusError,
            2,
            "custody group 200 is not below the number of groups",
            lambda: consensus.compute_columns_for_custody_group(200),
            id="custody-group",
        ),
        # Mainnet has 128 custody groups, below 200.
        pytest.param(
            ConsensusError,
            1,
            "custody group count 200 exceeds the number of groups",
            lambda: consensus.get_custody_column_bits(0, 200),
            id="custody-bits",
        ),
        # Index 5 is not among 3 indices.
        pytest.param(
            ConsensusError,
            201,
            "index 5 is not below the index count 3",
            lambda: consensus.compute_shuffled_index(5, 3, bytes(32)),
            id="shuffle-index",
        ),
        # No operation has the name nope.
        pytest.param(
            TransitionError,
            0,
            "no operation nope",
            lambda: consensus.process_operation("mainnet", "phase0", "nope", STATE, b""),
            id="transition-operation",
        ),
        # Deposit requests start at Electra.
        pytest.param(
            TransitionError,
            0,
            "no operation deposit_request at phase0",
            lambda: consensus.process_operation("mainnet", "phase0", "deposit_request", STATE, b""),
            id="transition-operation-fork",
        ),
        # No epoch step has the name nope.
        pytest.param(
            TransitionError,
            0,
            "no epoch step nope",
            lambda: consensus.process_epoch("mainnet", "phase0", "nope", STATE),
            id="transition-epoch",
        ),
        # Inactivity updates start at Altair.
        pytest.param(
            TransitionError,
            0,
            "no epoch step inactivity_updates at phase0",
            lambda: consensus.process_epoch("mainnet", "phase0", "inactivity_updates", STATE),
            id="transition-epoch-fork",
        ),
        # No fork comes before Phase 0.
        pytest.param(
            TransitionError,
            0,
            "no upgrade to phase0",
            lambda: consensus.upgrade_state("mainnet", "phase0", STATE),
            id="transition-upgrade",
        ),
        # One fork is named for no block.
        pytest.param(
            TransitionError,
            0,
            "1 block forks for 0 blocks",
            lambda: consensus.state_transitions_across("mainnet", "phase0", STATE, ["phase0"], []),
            id="transition-across",
        ),
        # The replacements of a configuration are a dict.
        pytest.param(
            TransitionError,
            0,
            "configuration: expected a dict",
            lambda: consensus.process_slots("mainnet", "phase0", STATE, 1, 5),  # ty: ignore[invalid-argument-type]
            id="transition-config",
        ),
        # Slot 1 plus 2^64 - 1 slots is 2^64, past the largest 64-bit slot.
        pytest.param(
            TransitionError,
            1,
            (
                "EthLib.Consensus.TransitionError.accessor "
                "(EthLib.Consensus.AccessorError.arith (EthLib.Base.ArithError.overflow))"
            ),
            lambda: consensus.process_slots("mainnet", "phase0", STATE, 2**64 - 1),
            id="transition-overflow",
        ),
        # No kind of delta has the name nope.
        pytest.param(
            TransitionError,
            0,
            "no deltas nope at phase0",
            lambda: consensus.rewards_deltas("mainnet", "phase0", "nope", STATE),
            id="rewards",
        ),
        # No consensus version has the name nope.
        pytest.param(
            ConsensusError,
            0,
            "no consensus version nope",
            lambda: consensus.consensus_version_fork("nope"),
            id="consensus-version",
        ),
        # A secret key of zero is not a valid scalar.
        pytest.param(
            ValidatorDutyError,
            0,
            "the secret key is not a nonzero scalar below the group order",
            lambda: consensus.get_validator_signature(
                "mainnet", "phase0", STATE, "randao", b"", bytes(32)
            ),
            id="duty-key",
        ),
        # No duty has the name nope.
        pytest.param(
            ValidatorDutyError,
            0,
            "unknown duty nope",
            lambda: consensus.get_validator_signature(
                "mainnet", "phase0", STATE, "nope", b"", bytes(31) + bytes([1])
            ),
            id="duty-name",
        ),
        # The status of a payload is 0, 1 or 2.
        pytest.param(
            ValidatorDutyError,
            0,
            "unknown payload status 7",
            lambda: consensus.get_attestation_data("mainnet", "phase0", STATE, bytes(32), 0, 0, 7),
            id="duty-status",
        ),
        # No gossip topic has the name nope.
        pytest.param(
            ForkChoiceError,
            0,
            "gossip validation of the topic nope at phase0 is not yet specified",
            lambda: consensus.gossip_validation("mainnet", "phase0", b"", b"", "nope", []),
            id="gossip-validation",
        ),
        # Column sidecars start at Fulu.
        pytest.param(
            SszError,
            0,
            "no data column sidecar at dencun",
            lambda: consensus.verify_data_column_sidecar("mainnet", "dencun", b""),
            id="column-fork",
        ),
        # No container has the name Nope.
        pytest.param(
            SszError,
            0,
            "no container Nope at phase0",
            lambda: consensus.ssz_static("mainnet", "phase0", "Nope", b""),
            id="ssz-container",
        ),
        # Only three containers have a Gloas upgrade, and Nope is not one.
        pytest.param(
            SszError,
            0,
            "no upgrade of Nope to Gloas",
            lambda: consensus.upgrade_operation("mainnet", "Nope", b""),
            id="ssz-upgrade",
        ),
        # The empty tree holds no deposit, and its count says 1.
        pytest.param(
            DepositTreeError,
            0,
            "the tree holds 0 deposits, not 1",
            lambda: consensus.deposit_tree_get_root((consensus.deposit_tree_new()[0], 1, None)),
            id="deposit-tree-count",
        ),
        # A snapshot of 33 finalized roots is deeper than the tree.
        pytest.param(
            DepositTreeError,
            0,
            "a snapshot holds at most 32 finalized roots",
            lambda: consensus.deposit_tree_from_snapshot(
                ([bytes(32)] * 33, bytes(32), 0, bytes(32), 0)
            ),
            id="deposit-tree-snapshot",
        ),
        # A full node forwards no beacon block as a light client message.
        pytest.param(
            LightClientError,
            0,
            "no light client topic is named beacon_block",
            lambda: consensus.light_client_gossip_full_node(
                "minimal", "altair", 0, [("beacon_block", 0, b"", None)]
            ),
            id="light-client-topic",
        ),
        # The empty input is no column sidecar.
        pytest.param(
            KzgError,
            0,
            "input rejected: EthLib.Serialization.Ssz.Err.scopeTooSmall 356 0",
            lambda: consensus.verify_data_column_sidecar_kzg_proofs("minimal", "fusaka", b"", b""),
            id="column-input",
        ),
    ],
)
def test_code_and_message(
    error: type[EthLibError], code: int, message: str, call: Callable[[], object]
) -> None:
    with raises(error, message) as info:
        call()
    assert type(info.value) is error
    assert info.value.code == code
