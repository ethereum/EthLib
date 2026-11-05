"""The runners of the legacy blockchain tests of ethereum/legacytests, from Frontier to London."""

import json
import re
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import cast

import pytest

from ethlib.cryptography.keccak import keccak256
from ethlib.errors import BlockError
from ethlib.execution import blocks
from ethlib.execution.pow import validate_ommers
from ethlib.serialization import rlp
from ethlib.state import dao_fork_root, rewards_root, state_root
from state.test_dao_fork import DAO_ACCOUNTS, DAO_RECOVERY

from .catalogue import LEGACY_FORKS, Case

# The block from which a transition network runs its second fork.
TRANSITION_BLOCK = 5

# The most recent blocks that the ommer check reads: the parent of a block and six before it.
RECENT_BLOCKS = 7

# The name of each header error code, as the message of the error spells it.
HEADER_ERRORS = {
    201: "genesisNumber",
    203: "gasUsedAboveLimit",
    204: "invalidGasLimit",
    205: "wrongBaseFee",
    206: "timestampNotAfterParent",
    207: "wrongNumber",
    208: "extraDataTooLong",
    215: "wrongDifficulty",
    216: "proofOfWork",
}

# The code of an ommer that is not a valid header, and of an ommer whose number is out of range.
INVALID_OMMER_HEADER = 234
OMMER_NUMBER_OUT_OF_RANGE = 232

# The header errors that each exception names, in the header of the block or of one of its ommers.
# A zero gas limit is also below the gas used, which the header check tests first.
# A block numbered 0 has the number of a genesis block, which no parent precedes.
# From London, a difficulty of 0 is that of a proof-of-stake block, which the check refuses.
HEADER_CODES = {
    "InvalidDifficulty": {215},
    "InvalidGasLimit": {204},
    "InvalidGasLimit2": {203, 204},
    "BlockException.INVALID_GASLIMIT": {204},
    "InvalidNumber": {201, 207},
    "InvalidTimestamp": {206},
    "InvalidTimestampOlderParent": {206},
    "ExtraDataTooBig": {208},
    "TooMuchGasUsed": {203},
    "1559BlockImportImpossible_BaseFeeWrong": {205},
    "3675PoSBlockRejected": {215},
    "InvalidBlockNonce": {216},
}

# The exception of a block in the first ten blocks of the DAO Fork without its extra data.
DAO_EXTRA_DATA = "BlockException.EXTRA_DATA_INVALID_DAO"

# The code of an ommer in those blocks without that extra data.
OMMER_DAO_EXTRA_DATA = 243

# The exceptions of a block whose parent is in no test chain.
UNKNOWN_PARENT = {"UnknownParent", "UnknownParent2", "BlockException.UNKNOWN_PARENT"}

# The exceptions that a header check cannot see.
# They concern the body, the execution, the ommer rules, or the DAO Fork rule of a chain
# configuration, so a block with one of them has a valid header.
NOT_IN_HEADER = {
    "InvalidStateRoot",
    "InvalidReceiptsStateRoot",
    "InvalidLogBloom",
    "InvalidTransactionsRoot",
    "InvalidGasUsed",
    "BlockGasLimitReached",
    "BlockException.INVALID_GAS_USED",
    "InvalidUnclesHash",
    "InvalidUncleParentHash",
    "TooManyUncles",
    "UncleInChain",
    "UncleIsAncestor",
    "UncleIsBrother",
    "UncleParentIsNotAncestor",
    "UncleTooOld",
    "BlockException.UNCLE_PARENT_INCORRECT",
    DAO_EXTRA_DATA,
    # An ommer in the header form of the other side of the London transition.
    "BlockException.IMPORT_IMPOSSIBLE_LONDON_WRONG_PARENT",
    "BlockException.IMPORT_IMPOSSIBLE_LEGACY_WRONG_PARENT",
}


@dataclass(frozen=True)
class Block:
    """A block of a test chain: its fork, its header hash, and the RLP of its header and itself."""

    fork: str
    hash: str
    header: bytes
    block: bytes

    @property
    def parent_hash(self) -> str:
        """The parent hash, in the hexadecimal form of the fixtures."""
        return "0x" + rlp.decode(self.header)[0].hex()


# A file of state tests in blockchain form can hold hundreds of megabytes, so few stay in memory.
@lru_cache(maxsize=4)
def _fixtures(path: Path) -> dict:
    return json.loads(path.read_text())


def fixture(root: Path, case: Case) -> dict:
    """The blockchain test of a case."""
    # The identifier is the path, two colons and the name, which can hold colons itself.
    return _fixtures(root / case.path)[case.id.removeprefix(f"{case.path}::")]


def fork_at(network: str, number: int) -> str:
    """The fork of a network at a block number."""
    forks = LEGACY_FORKS[network]
    return forks[-1] if number >= TRANSITION_BLOCK else forks[0]


def chain_forks(network: str) -> list[tuple[str, int]]:
    """The forks of a network, each with its first block."""
    forks = LEGACY_FORKS[network]
    return [(forks[0], 0)] + [(fork, TRANSITION_BLOCK) for fork in forks[1:]]


def header_fields(fork: str) -> int:
    """The number of fields of a header at a fork from Frontier to London."""
    return 16 if fork == "london" else 15


def exception(network: str, entry: dict) -> str | None:
    """The exception that a block expects at the network, or `None` for a valid block."""
    for key in (f"expectException{network}", "expectExceptionALL", "expectException"):
        if key in entry:
            return entry[key]
    return None


def rejects_transaction(name: str) -> bool:
    """Whether an exception rejects a transaction of the block, which the header never shows."""
    return name.startswith(("TR_", "TransactionException."))


def sealed(test: dict) -> bool:
    """Whether the blocks of a test carry a proof of work."""
    return test.get("sealEngine") == "Ethash"


def recent(chain: dict[str, Block], parent: Block) -> list[bytes]:
    """The blocks that end with `parent`, at most seven, the oldest first."""
    blocks_ = [parent]
    while len(blocks_) < RECENT_BLOCKS and blocks_[-1].parent_hash in chain:
        blocks_.append(chain[blocks_[-1].parent_hash])
    return [b.block for b in reversed(blocks_)]


def _header_error(
    network: str, test: dict, chain: dict, parent: Block, block: Block, expected: str
) -> None:
    """Check that the header of the block or of one of its ommers fails as the exception says."""
    codes = HEADER_CODES[expected]
    check = blocks.validate_header if sealed(test) else blocks.check_header
    try:
        check(parent.fork, block.fork, parent.header, block.header)
    except BlockError as error:
        assert error.code in codes, (expected, str(error))
        return
    # The header of the block is valid, so the exception names an ommer.
    with pytest.raises(BlockError) as error:
        validate_ommers(chain_forks(network), recent(chain, parent), block.block, sealed(test))
    message = str(error.value)
    if error.value.code == OMMER_NUMBER_OUT_OF_RANGE:
        # An ommer numbered 0 or not below the block fails before its header is read.
        assert codes & {201, 207}, (expected, message)
        return
    assert error.value.code == INVALID_OMMER_HEADER, (expected, message)
    if any(f"BlockError.{HEADER_ERRORS[code]}" in message for code in codes):
        return
    # The ommer check takes the parent of an ommer to be the recent block one number below it.
    # An ommer with a wrong number then fails against a block that is not its parent, at the
    # first check that this block breaks.
    assert codes & {207}, message
    headers = {_number(b[0]): b[0] for b in map(rlp.decode, recent(chain, parent))}
    assert any(
        _number(ommer) - 1 in headers
        and ommer[0] != blocks.header_hash(block.fork, rlp.encode(headers[_number(ommer) - 1]))
        for ommer in rlp.decode(block.block)[2]
    ), message


def _number(header: list) -> int:
    return int.from_bytes(header[8], "big")


def run_headers(root: Path, case: Case) -> None:
    """Check each header against its parent, with the proof of work when the test seals it."""
    test = fixture(root, case)
    network = test["network"]
    check = blocks.validate_header if sealed(test) else blocks.check_header
    chain: dict[str, Block] = {}
    checked = 0
    entries = [(test["genesisRLP"], None)] + [(e["rlp"], e) for e in test["blocks"]]
    for data, entry in entries:
        data = bytes.fromhex(data.removeprefix("0x"))
        expected = exception(network, entry) if entry else None
        fields = rlp.decode(data)[0]
        fork = fork_at(network, int.from_bytes(fields[8], "big"))
        header = rlp.encode(fields)
        if len(fields) != header_fields(fork):
            # A header in the form of another fork decodes at no fork that its number runs.
            assert expected is not None
            with pytest.raises(BlockError, match="wrongFieldCount"):
                blocks.header_hash(fork, header)
            checked += 1
            continue
        block = Block(fork, "0x" + blocks.header_hash(fork, header).hex(), header, data)
        if entry is None:
            assert block.hash == test["genesisBlockHeader"]["hash"]
            chain[block.hash] = block
            continue
        parent = chain.get(block.parent_hash)
        if expected in UNKNOWN_PARENT:
            assert parent is None, block.hash
        elif expected is None or expected in NOT_IN_HEADER or rejects_transaction(expected):
            assert parent is not None, block.hash
            check(parent.fork, block.fork, parent.header, block.header)
            if expected is None:
                assert block.hash == entry["blockHeader"]["hash"]
                chain[block.hash] = block
        else:
            assert expected in HEADER_CODES, f"no header code for {expected}"
            assert parent is not None, block.hash
            _header_error(network, test, chain, parent, block, expected)
        checked += 1
    assert checked > 0


# The ommer errors that each exception names, with the codes of the ommer check.
# The fillers name a case by the client's first failed check, and EthLib checks in another order.
# A sibling of the block has the block's number, so its number is out of range first.
# An ommer of age 7 has its parent outside the seven recent blocks, so that parent is missing first.
# An ommer numbered 0 is the genesis block, out of range before it is found in the chain.
# The newer fillers name an ommer twice in the block as a brother.
OMMER_CODES = {
    "InvalidUnclesHash": {231},
    "TooManyUncles": {235},
    "UncleInChain": {236, 237, 238},
    "UncleIsAncestor": {232, 237},
    "UncleIsBrother": {232, 236},
    "UncleParentIsNotAncestor": {232, 233},
    "UncleTooOld": {233},
    "InvalidUncleParentHash": {232, 233, 234},
}

# The block reward before Byzantium, from Byzantium, and from Constantinople, in wei.
ETHER = 10**18
BLOCK_REWARDS = (("constantinople", 2 * ETHER), ("byzantium", 3 * ETHER), ("frontier", 5 * ETHER))
FORK_ORDER = (
    "frontier",
    "homestead",
    "daoFork",
    "tangerineWhistle",
    "spuriousDragon",
    "byzantium",
    "constantinople",
    "petersburg",
    "istanbul",
    "berlin",
    "london",
)


def _block_reward(fork: str) -> int:
    rank = FORK_ORDER.index(fork)
    return next(r for first, r in BLOCK_REWARDS if rank >= FORK_ORDER.index(first))


def _quantity(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _rewards(fork: str, block: list) -> Counter:
    """The rewards of a block by address, as section 11.3 of the Yellow Paper gives them."""
    header, _, ommers = block
    reward, number = _block_reward(fork), _number(header)
    paid = Counter({header[2]: reward + len(ommers) * (reward // 32)})
    for ommer in ommers:
        paid[ommer[2]] += (8 - (number - _number(ommer))) * reward // 8
    return paid


def run_ommers(root: Path, case: Case) -> None:
    """Check the ommers of each block, and the rewards of each valid block that holds some."""
    test = fixture(root, case)
    network = test["network"]
    chain: dict[str, Block] = {}
    checked = 0
    for data, entry in [(test["genesisRLP"], None)] + [(e["rlp"], e) for e in test["blocks"]]:
        data = bytes.fromhex(data.removeprefix("0x"))
        decoded = rlp.decode(data)
        fork = fork_at(network, _number(decoded[0]))
        if len(decoded[0]) != header_fields(fork):
            continue
        header = rlp.encode(decoded[0])
        block = Block(fork, "0x" + blocks.header_hash(fork, header).hex(), header, data)
        if entry is None:
            chain[block.hash] = block
            continue
        expected = exception(network, entry)
        # A block whose ommers the test checks has its parent in the chain.
        parent = chain.get(block.parent_hash)
        if expected is None:
            chain[block.hash] = block
            if decoded[2]:
                assert validate_ommers(
                    chain_forks(network), recent(chain, cast(Block, parent)), data, sealed(test)
                )
                _check_rewards(network, decoded, data)
                checked += 1
        elif expected in OMMER_CODES:
            with pytest.raises(BlockError) as error:
                validate_ommers(
                    chain_forks(network), recent(chain, cast(Block, parent)), data, sealed(test)
                )
            assert error.value.code in OMMER_CODES[expected], (expected, str(error.value))
            checked += 1
    _check_post_state(test, chain)
    assert checked > 0


def _state(balances: Counter) -> bytes:
    """A state whose accounts hold only the given balances."""
    return rlp.encode(
        [[address, b"", _quantity(value), b"", []] for address, value in balances.items()]
    )


def _check_rewards(network: str, decoded: list, data: bytes) -> None:
    # From a state with no account, the rewards create one account for each address they pay.
    fork = fork_at(network, _number(decoded[0]))
    paid = _rewards(fork, decoded)
    assert rewards_root(chain_forks(network), _state(Counter()), data) == state_root(_state(paid))


def _fee(fork: str, decoded: list) -> int | None:
    """The fees of a block's miner, or `None` when the header and transactions do not give them.

    Before London, a block whose legacy transactions share one gas price pays its gas used at
    that price.
    """
    header, transactions, _ = decoded
    if not transactions:
        return 0
    if fork == "london" or not all(isinstance(tx, list) for tx in transactions):
        return None
    prices = {tx[1] for tx in transactions}
    if len(prices) != 1:
        return None
    return int.from_bytes(header[10], "big") * int.from_bytes(prices.pop(), "big")


def _check_post_state(test: dict, chain: dict[str, Block]) -> None:
    """Check the rewards of the canonical chain against the balances of the post state.

    An address that only rewards pay holds exactly its rewards.
    A miner that no transaction pays holds its balance before, its rewards and its fees.
    """
    canonical = []
    head = test["lastblockhash"]
    while head in chain and chain[head].parent_hash in chain:
        canonical.append(chain[head])
        head = chain[head].parent_hash
    if "postState" not in test or not any(rlp.decode(b.block)[2] for b in canonical):
        return
    pre = {bytes.fromhex(a[2:]): int(v["balance"], 16) for a, v in test["pre"].items()}
    post = {bytes.fromhex(a[2:]): int(v["balance"], 16) for a, v in test["postState"].items()}
    paid, fees, recipients, miners = Counter(), Counter(), set(), set()
    fees_known = True
    for b in canonical:
        decoded = rlp.decode(b.block)
        paid += _rewards(b.fork, decoded)
        miners.add(decoded[0][2])
        recipients |= {tx[3] for tx in decoded[1] if isinstance(tx, list)}
        fee = _fee(b.fork, decoded)
        fees_known = fees_known and fee is not None
        fees[decoded[0][2]] += fee or 0
    anchored = 0
    for address, value in paid.items():
        if address in recipients:
            continue
        if address in miners:
            if fees_known:
                assert post[address] == pre.get(address, 0) + value + fees[address], address.hex()
                anchored += 1
        elif address not in pre:
            assert post[address] == value, address.hex()
            anchored += 1
    assert anchored > 0


def _pre_state(accounts: dict) -> bytes:
    """Accounts of a test in the form of a state input: address, nonce, balance, code, storage."""

    def scalar(value: str) -> bytes:
        return _quantity(int(value, 16))

    return rlp.encode(
        [
            [
                bytes.fromhex(address[2:]),
                scalar(a["nonce"]),
                scalar(a["balance"]),
                bytes.fromhex(a["code"][2:]),
                [[int(k, 16).to_bytes(32, "big"), scalar(v)] for k, v in a["storage"].items()],
            ]
            for address, a in accounts.items()
        ]
    )


def _dao_accounts(test: dict, accounts: str) -> bytes:
    """The DAO accounts and the recovery contract of a state of the test, as a state input."""
    wanted = set(DAO_ACCOUNTS) | {DAO_RECOVERY}
    return _pre_state(
        {
            address: a
            for address, a in test[accounts].items()
            if bytes.fromhex(address[2:]) in wanted
        }
    )


def run_dao(root: Path, case: Case) -> None:
    """Check the extra data of the DAO Fork in each header, and the move of the DAO's ether."""
    test = fixture(root, case)
    network = test["network"]
    chain: dict[str, Block] = {}
    checked = 0
    for data, entry in [(test["genesisRLP"], None)] + [(e["rlp"], e) for e in test["blocks"]]:
        data = bytes.fromhex(data.removeprefix("0x"))
        decoded = rlp.decode(data)
        fork = fork_at(network, _number(decoded[0]))
        header = rlp.encode(decoded[0])
        block = Block(fork, "0x" + blocks.header_hash(fork, header).hex(), header, data)
        expected = exception(network, entry) if entry else None
        if expected not in (None, DAO_EXTRA_DATA):
            continue
        if entry is not None:
            valid = blocks.dao_extra_data_valid(TRANSITION_BLOCK, fork, header)
            parent = chain.get(block.parent_hash)
            if valid and decoded[2] and parent is not None:
                # Each ommer in the first blocks of the fork carries the extra data too.
                try:
                    validate_ommers(chain_forks(network), recent(chain, parent), data, sealed(test))
                except BlockError as error:
                    assert error.code == OMMER_DAO_EXTRA_DATA, str(error)
                    valid = False
            assert valid == (expected is None), (_number(decoded[0]), expected)
            checked += 1
        if expected is None:
            chain[block.hash] = block
    assert checked > 0
    # No transaction pays a DAO account or the recovery contract, so only the fork moves their
    # ether.
    paid = {
        tx[3]
        for entry in test["blocks"]
        if "blockHeader" in entry
        for tx in rlp.decode(bytes.fromhex(entry["rlp"].removeprefix("0x")))[1]
        if isinstance(tx, list)
    }
    assert not paid & (set(DAO_ACCOUNTS) | {DAO_RECOVERY})
    pre, post = _dao_accounts(test, "pre"), _dao_accounts(test, "postState")
    # The DAO accounts hold ether, so the move changes the state.
    assert dao_fork_root(pre) != state_root(pre)
    last = next(
        entry["blockHeader"]
        for entry in test["blocks"]
        if entry.get("blockHeader", {}).get("hash") == test["lastblockhash"]
    )
    if int(last["number"], 16) >= TRANSITION_BLOCK:
        assert dao_fork_root(pre) == state_root(post)
    else:
        assert state_root(pre) == state_root(post)


# The legacy tests run on chain 1.
CHAIN_ID = 1


def chain_config(network: str) -> dict:
    """The chain configuration of a network: each fork with the block from which it runs."""
    first, *second = LEGACY_FORKS[network]
    # The DAO Fork runs only as the second fork of its transition network.
    forks = [fork for fork in FORK_ORDER if fork != "daoFork"]
    activations = [[fork, "block", 0] for fork in forks[: forks.index(first) + 1]]
    activations += [[fork, "block", TRANSITION_BLOCK] for fork in second]
    return {"chainId": CHAIN_ID, "activations": activations, "blobSchedules": []}


# The error of the state transition that each exception of the tests names, as a pattern.
# The header and ommer names follow the code sets of the header and ommer runners above,
# since the fillers name the first check of their client, and EthLib checks in another order.
EXCEPTIONS: dict[str, str] = {
    # The checks of a header against its parent.
    "InvalidDifficulty": r"wrongDifficulty",
    "InvalidGasLimit": r"invalidGasLimit",
    "InvalidGasLimit2": r"invalidGasLimit|gasUsedAboveLimit",
    "BlockException.INVALID_GASLIMIT": r"invalidGasLimit",
    # The ommer check takes the parent of an ommer to be the recent block one number below it.
    # An ommer with a wrong number then fails against a block that is not its parent.
    # An ommer numbered 0, or not below the block, is out of range before its header is read.
    "InvalidNumber": r"wrongNumber|genesisNumber|OmmerError\.(invalidHeader|numberOutOfRange)",
    "InvalidTimestamp": r"timestampNotAfterParent",
    "InvalidTimestampOlderParent": r"timestampNotAfterParent",
    "ExtraDataTooBig": r"extraDataTooLong",
    "TooMuchGasUsed": r"gasUsedAboveLimit",
    "1559BlockImportImpossible_BaseFeeWrong": r"wrongBaseFee",
    "3675PoSBlockRejected": r"wrongDifficulty",
    "InvalidBlockNonce": r"proofOfWork",
    "BlockException.EXTRA_DATA_INVALID_DAO": r"wrongDaoExtraData",
    # The checks of the ommers.
    "InvalidUnclesHash": r"wrongOmmersHash",
    "TooManyUncles": r"tooManyOmmers",
    "UncleInChain": r"duplicateOmmer|ommerInChain|ommerAlreadyIncluded",
    "UncleIsAncestor": r"numberOutOfRange|ommerInChain",
    "UncleIsBrother": r"numberOutOfRange|duplicateOmmer",
    "UncleParentIsNotAncestor": r"numberOutOfRange|parentMissing|wrongAge",
    "UncleTooOld": r"wrongAge|parentMissing",
    # An ommer of age 7, whose parent is outside the seven recent blocks.
    "BlockException.UNCLE_PARENT_INCORRECT": r"wrongAge|parentMissing",
    "InvalidUncleParentHash": r"numberOutOfRange|parentMissing|invalidHeader",
    # An ommer in the header form of the other side of the London transition does not decode.
    "BlockException.IMPORT_IMPOSSIBLE_LONDON_WRONG_PARENT": r"wrongFieldCount",
    "BlockException.IMPORT_IMPOSSIBLE_LEGACY_WRONG_PARENT": r"wrongFieldCount",
    # The checks of the block against what its body gave.
    "InvalidStateRoot": r"wrongStateRoot",
    # Before Byzantium a receipt holds the state root after its transaction.
    # A wrong state then also makes the receipts root wrong, and the state root is checked first.
    "InvalidReceiptsStateRoot": r"wrongReceiptRoot|wrongStateRoot",
    "InvalidTransactionsRoot": r"wrongTransactionsRoot",
    "InvalidLogBloom": r"wrongBloom",
    "InvalidGasUsed": r"wrongGasUsed",
    "BlockException.INVALID_GAS_USED": r"wrongGasUsed",
    "BlockGasLimitReached": r"gasAllowanceExceeded",
    # The checks of a transaction, alone and against its block and the state.
    "TR_GasLimitReached": r"gasAllowanceExceeded",
    "TR_IntrinsicGas": r"insufficientGas",
    "IntrinsicGas": r"insufficientGas",
    "TransactionException.INTRINSIC_GAS_TOO_LOW": r"insufficientGas",
    "TR_NoFunds": r"insufficientBalance",
    "TR_NoFundsX": r"insufficientBalance",
    "TransactionException.INSUFFICIENT_ACCOUNT_FUNDS": r"insufficientBalance",
    "TR_NoFundsOrGas": r"insufficientBalance|insufficientGas|gasAllowanceExceeded",
    "SenderNotEOA": r"senderNotEoa",
    "SenderNotEOAorNoCASH": r"senderNotEoa|insufficientBalance",
    "TR_TypeNotSupported": r"unsupportedType",
    "TransactionException.TYPE_NOT_SUPPORTED": r"unsupportedType",
    "TR_FeeCapLessThanBlocks": r"insufficientMaxFeePerGas",
    "TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS": r"insufficientMaxFeePerGas",
    # A transaction below its intrinsic gas fails that check before the fee and balance checks.
    "TR_FeeCapLessThanBlocksORNoFunds": (
        r"insufficientMaxFeePerGas|insufficientBalance|insufficientGas"
    ),
    "TR_FeeCapLessThanBlocksORGasLimitReached": r"insufficientMaxFeePerGas|gasAllowanceExceeded",
    "TR_TipGtFeeCap": r"priorityFeeGreaterThanMaxFee",
    "TR_NonceHasMaxValue": r"nonceOverflow",
    "TR_NonceTooLow": r"nonceTooLow",
    "TR_NonceTooHigh": r"nonceTooHigh",
    "TR_RLP_WRONGVALUE": r"does not decode",
    "TR_InitCodeLimitExceeded": r"initCodeTooLarge",
    "TransactionException.INITCODE_SIZE_EXCEEDED": r"initCodeTooLarge",
    # A block that is not a list of its parts.
    "RLP_ExpectedAsList": r"block rejected",
    "BlockException.RLP_STRUCTURES_ENCODING": r"does not decode|block rejected",
}


def names(expected: str, message: str) -> bool:
    """Whether an error of the state transition is one that an exception of a test names."""
    return any(
        re.search(EXCEPTIONS[name], message) for name in expected.split("|") if name in EXCEPTIONS
    )


def run_blockchain(root: Path, case: Case) -> None:
    """Run each block through the state transition, and follow the chain of most difficulty."""
    test = fixture(root, case)
    network = test["network"]
    config = chain_config(network)
    genesis = rlp.decode(bytes.fromhex(test["genesisRLP"].removeprefix("0x")))[0]
    # Each valid block by its hash: the state after it, the recent blocks that end with it,
    # and the total difficulty of its chain.
    chains = {
        keccak256(rlp.encode(genesis)): (
            _pre_state(test["pre"]),
            [(fork_at(network, 0), rlp.encode(genesis), [])],
            int.from_bytes(genesis[7], "big"),
        )
    }
    head = next(iter(chains))
    for entry in test["blocks"]:
        expected = exception(network, entry)
        raw = bytes.fromhex(entry["rlp"].removeprefix("0x"))
        try:
            item = rlp.decode(raw)
            header, ommers = item[0], item[2]
            number, parent = _number(header), chains.get(bytes(header[0]))
        except Exception:
            # A block that is not a list of a header, transactions and ommers is invalid.
            assert expected is not None, entry
            continue
        if parent is None:
            # The parent of the block is missing or invalid.
            assert expected is not None, entry
            continue
        state, recent_blocks, difficulty = parent
        fork = fork_at(network, number)
        if len(header) != header_fields(fork):
            # A header in the form of another fork decodes at no fork that its number runs.
            assert expected is not None, entry
            with pytest.raises(BlockError, match="wrongFieldCount"):
                blocks.state_transition(config, state, recent_blocks, fork, raw, sealed(test))
            continue
        if expected is not None:
            with pytest.raises(BlockError) as error:
                blocks.state_transition(config, state, recent_blocks, fork, raw, sealed(test))
            assert names(expected, str(error.value)), (expected, str(error.value))
            continue
        _, accounts = blocks.state_transition(config, state, recent_blocks, fork, raw, sealed(test))
        block_hash = keccak256(rlp.encode(header))
        recent_blocks = recent_blocks + [
            (fork, rlp.encode(header), [rlp.encode(o) for o in ommers])
        ]
        difficulty += int.from_bytes(header[7], "big")
        chains[block_hash] = (rlp.encode(accounts), recent_blocks[-256:], difficulty)
        # The head moves only to a chain of strictly more total difficulty.
        if difficulty > chains[head][2]:
            head = block_hash
    assert "0x" + head.hex() == test["lastblockhash"]
