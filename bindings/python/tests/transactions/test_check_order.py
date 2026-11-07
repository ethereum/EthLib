"""The order of the checks of a transaction against its block, at Prague."""

from ethlib.cryptography.keccak import keccak256
from ethlib.cryptography.secp256k1 import address, sign
from ethlib.execution import transactions
from ethlib.serialization import rlp
from raising import raises

KEY = bytes(31) + b"\x01"
OTHER = b"\x11" * 20


def _int(n: int) -> bytes:
    return n.to_bytes((n.bit_length() + 7) // 8, "big")


def _fee_market(chain_id: int, gas: int) -> bytes:
    """A signed type 2 transfer of 1 wei from the key's account, on the chain `chain_id`."""
    fields = [_int(chain_id), b"", _int(1), _int(10), _int(gas), OTHER, _int(1), b"", []]
    signature = sign(KEY, keccak256(b"\x02" + rlp.encode(fields)))
    r, s, v = signature[:32], signature[32:64], signature[64]
    return b"\x02" + rlp.encode(fields + [_int(v), r.lstrip(b"\0"), s.lstrip(b"\0")])


# The sender holds 1 ether, with nonce 0 and no code.
STATE = rlp.encode([[address(KEY), b"", _int(10**18), b"", []]])


def _check_in_block(tx: bytes, gas_limit: int) -> transactions.Included:
    return transactions.check_in_block(
        "pectra",
        1,
        tx,
        STATE,
        gas_limit=gas_limit,
        gas_used=0,
        blob_gas_used=0,
        base_fee=1,
        excess_blob_gas=0,
    )


def test_gas_before_chain() -> None:
    # Signed for chain 2 with a gas limit of 20000, below the intrinsic gas of 21000.
    tx = _fee_market(2, 20_000)
    # In a block, the gas and nonce rules come first, before the chain.
    with raises(transactions.TransactionError, "insufficientGas 21000 20000"):
        _check_in_block(tx, 30_000_000)
    # Alone, the transaction tests expect the chain first.
    with raises(transactions.TransactionError, "wrongChainId 1 2"):
        transactions.check("pectra", 1, tx)


def test_block_gas_before_chain() -> None:
    # Signed for chain 2, with a gas limit above the 10000 gas that the block has left.
    tx = _fee_market(2, 21_000)
    with raises(transactions.TransactionError, "gasAllowanceExceeded 21000 10000"):
        _check_in_block(tx, 10_000)
    # On its own chain the same block still rejects it for its gas.
    with raises(transactions.TransactionError, "gasAllowanceExceeded 21000 10000"):
        _check_in_block(_fee_market(1, 21_000), 10_000)
    # And with room in the block it passes.
    included = _check_in_block(_fee_market(1, 21_000), 30_000_000)
    assert included.sender == address(KEY)
