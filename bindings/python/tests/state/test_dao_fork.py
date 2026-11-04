"""The DAO Fork against the accounts and the recovery contract of EIP-779."""

import re
from pathlib import Path

from ethlib.state import dao_fork_root, state_root

from .test_root import rlp_encode

_EIP = (Path(__file__).resolve().parent / "dao" / "eip-779.md.txt").read_text()

# The list `L` of EIP-779, in its order, between its summary and the end of its details.
_LIST = _EIP[_EIP.index("Reference list L"):_EIP.index("</details>")]
DAO_ACCOUNTS = [bytes.fromhex(a[2:]) for a in re.findall(r"0x[0-9a-f]{40}", _LIST)]

# The contract that receives the ether, as EIP-779 names it.
DAO_RECOVERY = bytes.fromhex("bf4ed7b27f1d666546e30d74d50d173d20bca754")

# An account that the fork must leave alone.
BYSTANDER = bytes.fromhex("00000000000000000000000000000000000000ff")


def _entry(address: bytes, balance: int, nonce: int = 0) -> list:
    """An account of the state input: address, nonce, balance, code and storage."""
    return [address, nonce, balance, b"", []]


def test_list_has_116_distinct_accounts() -> None:
    assert len(DAO_ACCOUNTS) == len(set(DAO_ACCOUNTS)) == 116
    assert DAO_RECOVERY not in DAO_ACCOUNTS


def test_every_account_moves_to_the_recovery_contract() -> None:
    # Account `i` holds `i + 1` wei and nonce `i`, so a missed or a wrong address changes the root.
    pre = [_entry(a, i + 1, i) for i, a in enumerate(DAO_ACCOUNTS)]
    pre += [_entry(DAO_RECOVERY, 5), _entry(BYSTANDER, 7)]
    total = sum(range(1, 117))
    post = [_entry(a, 0, i) for i, a in enumerate(DAO_ACCOUNTS)]
    post += [_entry(DAO_RECOVERY, 5 + total), _entry(BYSTANDER, 7)]
    assert dao_fork_root(rlp_encode(pre)) == state_root(rlp_encode(post))


def test_missing_accounts_are_created_empty() -> None:
    # Before EIP-161, moving zero wei to or from an address leaves an empty account there.
    post = [_entry(a, 0) for a in DAO_ACCOUNTS] + [_entry(DAO_RECOVERY, 0)]
    assert dao_fork_root(rlp_encode([])) == state_root(rlp_encode(post))
