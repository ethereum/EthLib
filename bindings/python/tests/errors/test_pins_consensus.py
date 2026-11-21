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
    ],
)
def test_code_and_message(
    error: type[EthLibError], code: int, message: str, call: Callable[[], object]
) -> None:
    with raises(error, message) as info:
        call()
    assert type(info.value) is error
    assert info.value.code == code
