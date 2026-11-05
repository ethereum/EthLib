"""The addresses of contracts that CREATE and CREATE2 make, through the bindings."""

import pytest

from ethlib.execution.evm import create2_address, create_address

# The examples of EIP-1014, "Examples".
# Each case is the sender, the salt, the init code and the address.
#
# File: EIPS/eip-1014.md
# Repository: ethereum/EIPs
# Commit: 46976b2a9bf99f727fb87dc8c809e3a3cdc6b445
# Licence: CC0-1.0
EIP_1014 = [
    ("0000000000000000000000000000000000000000",
     "0000000000000000000000000000000000000000000000000000000000000000",
     "00",
     "4D1A2e2bB4F88F0250f26Ffff098B0b30B26BF38"),
    ("deadbeef00000000000000000000000000000000",
     "0000000000000000000000000000000000000000000000000000000000000000",
     "00",
     "B928f69Bb1D91Cd65274e3c79d8986362984fDA3"),
    ("deadbeef00000000000000000000000000000000",
     "000000000000000000000000feed000000000000000000000000000000000000",
     "00",
     "D04116cDd17beBE565EB2422F2497E06cC1C9833"),
    ("0000000000000000000000000000000000000000",
     "0000000000000000000000000000000000000000000000000000000000000000",
     "deadbeef",
     "70f2b2914A2a4b783FaEFb75f459A580616Fcb5e"),
    ("00000000000000000000000000000000deadbeef",
     "00000000000000000000000000000000000000000000000000000000cafebabe",
     "deadbeef",
     "60f3f640a8508fC6a86d45DF051962668E1e8AC7"),
    ("00000000000000000000000000000000deadbeef",
     "00000000000000000000000000000000000000000000000000000000cafebabe",
     "deadbeef" * 11,
     "1d8bfDC5D46DC4f61D6b6115972536eBE6A8854C"),
    ("0000000000000000000000000000000000000000",
     "0000000000000000000000000000000000000000000000000000000000000000",
     "",
     "E33C0C7F7df4809055C3ebA6c09CFe4BaF1BD9e0"),
]


@pytest.mark.parametrize(("sender", "salt", "init_code", "expected"), EIP_1014)
def test_create2_eip_1014(sender: str, salt: str, init_code: str, expected: str) -> None:
    """Each example of EIP-1014 gives its address."""
    address = create2_address(bytes.fromhex(sender), bytes.fromhex(salt), bytes.fromhex(init_code))
    assert address == bytes.fromhex(expected)


def test_create_address_is_20_bytes() -> None:
    """CREATE gives a 20-byte address, which changes with the nonce."""
    sender = bytes.fromhex("deadbeef00000000000000000000000000000000")
    addresses = {create_address(sender, nonce) for nonce in (0, 1, 2**64 - 2)}
    assert len(addresses) == 3
    assert all(len(a) == 20 for a in addresses)


@pytest.mark.parametrize("sender", [b"", bytes(19), bytes(21)])
def test_sender_must_be_20_bytes(sender: bytes) -> None:
    """A sender that is not 20 bytes is rejected before Lean runs."""
    with pytest.raises(ValueError, match="the sender must be 20 bytes"):
        create_address(sender, 0)
    with pytest.raises(ValueError, match="the sender must be 20 bytes"):
        create2_address(sender, bytes(32), b"")


def test_salt_must_be_32_bytes() -> None:
    """A salt that is not one word is rejected."""
    with pytest.raises(ValueError, match="the salt must be 32 bytes"):
        create2_address(bytes(20), bytes(31), b"")

