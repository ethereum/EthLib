"""The eth2 and nfd entries that a node writes into its record, on mainnet."""

from typing import Any

import pytest

from ethlib.consensus import (
    bootnode_fork_id,
    compute_fork_digest,
    enr_fork_id,
    enr_record,
    next_fork_digest,
)
from ethlib.networking import enr

from .test_fork_digest import (
    FAR_FUTURE_EPOCH,
    GENESIS_ARCHIVE,
    MAINNET_RECORD,
    _eth2,
    _mainnet_root,
)

# The fork epochs, versions and blob schedule of mainnet are those that test_fork_digest.py pins.
# Fulu starts at epoch 411392, with version 0x06000000.
# The blob schedule changes the digest at the BPO epochs 412672 and 419072.
# Gloas is left at the far future, so no fork follows epoch 419072.
#
# The digests are those of the fork digest export, which test_fork_digest.py checks.
# Any root works for the rules here, so most tests use the zero root.

ROOT = bytes(32)
FULU_VERSION = bytes.fromhex("06000000")


def test_before_a_bpo_epoch() -> None:
    # The next fork is the BPO epoch, which keeps the version of Fulu.
    digest = compute_fork_digest("mainnet", ROOT, 412000)
    assert enr_fork_id("mainnet", ROOT, 412000) == (digest, FULU_VERSION, 412672)
    assert next_fork_digest("mainnet", ROOT, 412000) == compute_fork_digest("mainnet", ROOT, 412672)
    assert next_fork_digest("mainnet", ROOT, 412000) != digest


def test_after_the_last_bpo_epoch() -> None:
    # No fork is planned: the far future epoch, the current version and four zero bytes.
    digest = compute_fork_digest("mainnet", ROOT, 419100)
    assert enr_fork_id("mainnet", ROOT, 419100) == (digest, FULU_VERSION, FAR_FUTURE_EPOCH)
    assert next_fork_digest("mainnet", ROOT, 419100) == bytes(4)


def test_before_fulu() -> None:
    # In Electra, the next fork is Fulu, with its own version.
    digest = compute_fork_digest("mainnet", ROOT, 400000)
    assert digest != compute_fork_digest("mainnet", ROOT, 411392)
    assert enr_fork_id("mainnet", ROOT, 400000) == (digest, FULU_VERSION, 411392)
    assert next_fork_digest("mainnet", ROOT, 400000) == compute_fork_digest("mainnet", ROOT, 411392)


def test_at_a_fork_epoch() -> None:
    # At the first epoch of Fulu, the next fork is the first BPO epoch, and one epoch earlier Fulu.
    _, version, epoch = enr_fork_id("mainnet", ROOT, 411392)
    assert (version, epoch) == (FULU_VERSION, 412672)
    _, version, epoch = enr_fork_id("mainnet", ROOT, 411391)
    assert (version, epoch) == (FULU_VERSION, 411392)


def test_at_bpo_epochs() -> None:
    _, version, epoch = enr_fork_id("mainnet", ROOT, 412672)
    assert (version, epoch) == (FULU_VERSION, 419072)
    _, version, epoch = enr_fork_id("mainnet", ROOT, 419072)
    assert (version, epoch) == (FULU_VERSION, FAR_FUTURE_EPOCH)


def test_fork_after_an_unplanned_fork() -> None:
    # A fork left at the far future is skipped, and a later planned fork is the next one.
    config: dict[str, Any] = {
        "ELECTRA_FORK_EPOCH": 10,
        "FULU_FORK_EPOCH": FAR_FUTURE_EPOCH,
        "BLOB_SCHEDULE": [],
        "GLOAS_FORK_EPOCH": 100,
        "GLOAS_FORK_VERSION": "0x07000000",
    }
    _, version, epoch = enr_fork_id("mainnet", ROOT, 20, config)
    assert (version, epoch) == (bytes.fromhex("07000000"), 100)


def test_bootnode_before_genesis() -> None:
    # The digest of the genesis epoch with a zero root, the genesis version and no fork.
    digest = compute_fork_digest("mainnet", ROOT, 0)
    assert bootnode_fork_id("mainnet") == (digest, bytes(4), FAR_FUTURE_EPOCH)


def test_phase0_next_fork_matches_a_mainnet_record() -> None:
    # The bootnode record names Altair at epoch 74240 as its next fork.
    eth2 = _eth2(MAINNET_RECORD)
    _, version, epoch = enr_fork_id("mainnet", ROOT, 0)
    assert (version, epoch) == (eth2.next_fork_version, eth2.next_fork_epoch)


@pytest.mark.archive(GENESIS_ARCHIVE)
def test_phase0_bootnode_record() -> None:
    eth2 = _eth2(MAINNET_RECORD)
    assert enr_fork_id("mainnet", _mainnet_root(), 0) == tuple(eth2)


# A private key of the test vector of EIP-778, which test_enr.py pins.
SECRET_KEY = bytes.fromhex("b71c71a67e1177ad4e901695e1b4b9ee17ae16c6668d313eac2f96dbcda3f291")
# Bitvector[64] with bit 0 set, and Bitvector[4] with bit 1 set.
ATTNETS = bytes.fromhex("0100000000000000")
SYNCNETS = bytes([0x02])


@pytest.mark.parametrize("epoch", [412000, 419100])
def test_record_carries_cgc_and_nfd(epoch: int) -> None:
    record = enr_record("mainnet", ROOT, epoch, SECRET_KEY, 1, ATTNETS, SYNCNETS, 128)
    assert enr.verify_v4(record)
    entries = enr.consensus_entries("fusaka", record)
    assert tuple(entries.eth2) == enr_fork_id("mainnet", ROOT, epoch)
    assert (entries.attnets, entries.syncnets) == (ATTNETS, SYNCNETS)
    assert entries.cgc == 128
    assert entries.nfd == next_fork_digest("mainnet", ROOT, epoch)


def test_record_before_fulu_carries_cgc_and_nfd() -> None:
    # Fulu has an epoch, so an Electra node writes the entries already.
    record = enr_record("mainnet", ROOT, 400000, SECRET_KEY, 1, ATTNETS, SYNCNETS, 0)
    entries = enr.consensus_entries("fusaka", record)
    assert entries.cgc == 0
    assert entries.nfd == compute_fork_digest("mainnet", ROOT, 411392)
    assert enr.consensus_entries("pectra", record).cgc is None


def test_phase0_record_has_no_syncnets() -> None:
    record = enr_record("mainnet", ROOT, 0, SECRET_KEY, 1, ATTNETS, SYNCNETS, 0)
    assert enr.consensus_entries("altair", record).syncnets is None
