"""The chain of a network of the engine tests, and the outcome that a case expects."""

from ethlib import engine

# The network of a fixture, and the case of the Lean fork type that it names.
FORK_OF_NETWORK = {
    "Paris": "paris",
    "Shanghai": "shapella",
    "Cancun": "dencun",
    "Prague": "pectra",
    "Osaka": "fusaka",
    "BPO1": "bpo1",
    "BPO2": "bpo2",
    "Amsterdam": "glamsterdam",
}

# The forks up to Paris, which the fixtures activate at block 0.
BLOCK_FORKS = [
    "frontier",
    "homestead",
    "tangerineWhistle",
    "spuriousDragon",
    "byzantium",
    "constantinople",
    "petersburg",
    "istanbul",
    "berlin",
    "london",
    "paris",
]

# The forks from Shapella, which activate by timestamp.
TIME_FORKS = ["shapella", "dencun", "pectra", "fusaka", "bpo1", "bpo2", "glamsterdam"]

# A transition network runs its second fork from this timestamp on.
TRANSITION_TIME = 15_000

# The fixtures use the deposit contract of mainnet, at the address of EIP-6110.
DEPOSIT_CONTRACT_ADDRESS = bytes.fromhex("00000000219ab540356cbb839cbe05303d7705fa")

# The exceptions that each reason of an invalid payload stands for, by the code of the reason.
EXCEPTIONS = {
    # A transaction does not decode at the fork of the payload.
    401: {
        "BlockException.RLP_STRUCTURES_ENCODING",
        "TransactionException.TYPE_3_TX_PRE_FORK",
        "TransactionException.TYPE_4_TX_PRE_FORK",
        "TransactionException.TYPE_3_TX_CONTRACT_CREATION",
        "TransactionException.TYPE_4_TX_CONTRACT_CREATION",
    },
    # The block hash is not the hash of the header.
    403: {"BlockException.INVALID_BLOCK_HASH"},
    # The expected versioned hashes are not those of the block.
    404: {"BlockException.INVALID_VERSIONED_HASHES"},
    # The block access list is not the RLP form of a block access list.
    406: {"BlockException.INVALID_BLOCK_ACCESS_LIST"},
}


def config(network: str) -> dict:
    """The chain configuration of a network, such as `CancunToPragueAtTime15k`."""
    before, _, after = network.removesuffix("AtTime15k").partition("To")
    first = FORK_OF_NETWORK[before]
    activations = [[fork, "block", 0] for fork in BLOCK_FORKS]
    if first in TIME_FORKS:
        activations += [[fork, "time", 0] for fork in TIME_FORKS[: TIME_FORKS.index(first) + 1]]
    if after:
        activations.append([FORK_OF_NETWORK[after], "time", TRANSITION_TIME])
    return {
        "chainId": 1,
        "depositContractAddress": DEPOSIT_CONTRACT_ADDRESS,
        "activations": activations,
    }


def check(network: str, method: str, params: list, error: str | None, code: str | None) -> str:
    """Run one payload and assert the outcome that the fixture expects; return its kind."""
    if code is not None:
        # The fixture expects a JSON-RPC error.
        try:
            engine.new_payload(config(network), method, params)
        except engine.EngineError as e:
            assert -e.code == int(code)
            return "error"
        raise AssertionError(f"no error {code}")
    status = engine.new_payload(config(network), method, params)
    assert status["latestValidHash"] is None
    if not error:
        # A valid payload passes every check before execution.
        assert status["status"] == "SYNCING", status
        return "valid"
    if status["status"] == "SYNCING":
        # The payload fails only when its block runs.
        return "execution"
    reason = int(status["validationError"].split(":")[0])
    assert EXCEPTIONS[reason] & set(error.split("|")), (status, error)
    block_hash = method == "engine_newPayloadV1" and reason == 403
    assert status["status"] == ("INVALID_BLOCK_HASH" if block_hash else "INVALID")
    return "invalid"
