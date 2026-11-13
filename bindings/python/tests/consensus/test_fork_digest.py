"""The fork that a fork digest names, on mainnet, Sepolia and Hoodi, read from pinned sources."""

from typing import Any

import pytest

import archives
from ethlib.consensus import (
    ConsensusError,
    compute_fork_digest,
    digest_epochs,
    digests_identify,
    fork_of_digest,
)
from ethlib.networking import enr
from raising import raises

FAR_FUTURE_EPOCH = 2**64 - 1

GENESIS_ARCHIVE = "eth-clients/mainnet@8cad4805/genesis.ssz"

# The fork epochs and the blob schedule of mainnet.
# EthLib's configuration "mainnet" holds them, so the tests pass no replacement.
#
# File: metadata/config.yaml
# Repository: eth-clients/mainnet
# Commit: 8cad4805e9cb5aa5e8e74d30e3f5029a7f133372
MAINNET_EPOCHS = [0, 74240, 144896, 194048, 269568, 364032, 411392, 412672, 419072]

# A bootnode record of mainnet whose eth2 entry holds the digest of Phase 0.
# Its next fork is Altair, at epoch 74240.
#
# File: metadata/bootstrap_nodes.yaml
# Repository: eth-clients/mainnet
# Commit: 8cad4805e9cb5aa5e8e74d30e3f5029a7f133372
MAINNET_RECORD = (
    "enr:-Le4QPUXJS2BTORXxyx2Ia-9ae4YqA_JWX3ssj4E_J-3z1A-HmFGrU8BpvpqhNabayXeOZ2Nq_sbeDgtzMJp"
    "LLnXFgAChGV0aDKQtTA_KgEAAAAAIgEAAAAAAIJpZIJ2NIJpcISsaa0Zg2lwNpAkAIkHAAAAAPA8kv_-awoTiXNl"
    "Y3AyNTZrMaEDHAD2JKYevx89W0CcFJFiskdcEzkH_Wdv9iW42qLK79ODdWRwgiMohHVkcDaCI4I"
)

# The configuration of Sepolia, as replacements of the configuration "mainnet".
# Heze is not in the file, so it keeps the far future of "mainnet".
#
# File: metadata/config.yaml
# Repository: eth-clients/sepolia
# Commit: 7b1b9d9549787b6bbf538f943304c4cf84f7e39e
SEPOLIA: dict[str, Any] = {
    "GENESIS_FORK_VERSION": "0x90000069",
    "ALTAIR_FORK_VERSION": "0x90000070",
    "ALTAIR_FORK_EPOCH": 50,
    "BELLATRIX_FORK_VERSION": "0x90000071",
    "BELLATRIX_FORK_EPOCH": 100,
    "CAPELLA_FORK_VERSION": "0x90000072",
    "CAPELLA_FORK_EPOCH": 56832,
    "DENEB_FORK_VERSION": "0x90000073",
    "DENEB_FORK_EPOCH": 132608,
    "ELECTRA_FORK_VERSION": "0x90000074",
    "ELECTRA_FORK_EPOCH": 222464,
    "FULU_FORK_VERSION": "0x90000075",
    "FULU_FORK_EPOCH": 272640,
    "GLOAS_FORK_VERSION": "0x90000076",
    "GLOAS_FORK_EPOCH": 353024,
    "BLOB_SCHEDULE": [
        {"EPOCH": 274176, "MAX_BLOBS_PER_BLOCK": 15},
        {"EPOCH": 275712, "MAX_BLOBS_PER_BLOCK": 21},
    ],
}

# File: parsed/parsedConsensusGenesis.json
# Repository: eth-clients/sepolia
# Commit: 7b1b9d9549787b6bbf538f943304c4cf84f7e39e
SEPOLIA_ROOT = bytes.fromhex("d8ea171f3c94aea21ebc42a1ed61052acf3f9209c00e4efbaaddac09ed9b8078")

# A bootnode record of Sepolia whose eth2 entry holds the digest of Bellatrix.
# With no next fork scheduled, its next fork version is that of Bellatrix, at the far future.
#
# File: metadata/bootstrap_nodes.yaml
# Repository: eth-clients/sepolia
# Commit: 7b1b9d9549787b6bbf538f943304c4cf84f7e39e
SEPOLIA_RECORD = (
    "enr:-L64QC9Hhov4DhQ7mRukTOz4_jHm4DHlGL726NWH4ojH1wFgEwSin_6H95Gs6nW2fktTWbPachHJ6rUFu0iJ"
    "NgA0SB2CARqHYXR0bmV0c4j__________4RldGgykDb6UBOQAABx__________-CaWSCdjSCaXCEA-2vzolzZWNw"
    "MjU2azGhA17lsUg60R776rauYMdrAz383UUgESoaHEzMkvm4K6k6iHN5bmNuZXRzD4N0Y3CCIyiDdWRwgiMo"
)

# The configuration of Hoodi, as replacements of the configuration "mainnet".
# Gloas and Heze are not in the file, so they keep the far future of "mainnet".
#
# File: metadata/config.yaml
# Repository: eth-clients/hoodi
# Commit: 2a7efb3c530cce7c71702cc98d0f965df2411c11
HOODI: dict[str, Any] = {
    "GENESIS_FORK_VERSION": "0x10000910",
    "ALTAIR_FORK_VERSION": "0x20000910",
    "ALTAIR_FORK_EPOCH": 0,
    "BELLATRIX_FORK_VERSION": "0x30000910",
    "BELLATRIX_FORK_EPOCH": 0,
    "CAPELLA_FORK_VERSION": "0x40000910",
    "CAPELLA_FORK_EPOCH": 0,
    "DENEB_FORK_VERSION": "0x50000910",
    "DENEB_FORK_EPOCH": 0,
    "ELECTRA_FORK_VERSION": "0x60000910",
    "ELECTRA_FORK_EPOCH": 2048,
    "FULU_FORK_VERSION": "0x70000910",
    "FULU_FORK_EPOCH": 50688,
    "BLOB_SCHEDULE": [
        {"EPOCH": 52480, "MAX_BLOBS_PER_BLOCK": 15},
        {"EPOCH": 54016, "MAX_BLOBS_PER_BLOCK": 21},
    ],
}

# File: metadata/genesis_validators_root.txt
# Repository: eth-clients/hoodi
# Commit: 2a7efb3c530cce7c71702cc98d0f965df2411c11
HOODI_ROOT = bytes.fromhex("212f13fc4df078b6cb7db228f1c8307566dcecf900867401a92023d7ba99cb5f")

# A bootnode record of Hoodi whose eth2 entry holds the digest of Deneb, named dencun.
# Its next fork is Electra, at epoch 2048.
#
# File: metadata/bootstrap_nodes.yaml
# Repository: eth-clients/hoodi
# Commit: 2a7efb3c530cce7c71702cc98d0f965df2411c11
HOODI_RECORD = (
    "enr:-LK4QDwhXMitMbC8xRiNL-XGMhRyMSOnxej-zGifjv9Nm5G8EF285phTU-CAsMHRRefZimNI7eNpAluijMQP"
    "7NDC8kEMh2F0dG5ldHOIAAAAAAAABgCEZXRoMpDS8Zl_YAAJEAAIAAAAAAAAgmlkgnY0gmlwhAOIT_SJc2VjcDI1"
    "NmsxoQMoHWNL4MAvh6YpQeM2SUjhUrLIPsAVPB8nyxbmckC6KIN0Y3CCIyiDdWRwgiMo"
)


def _eth2(text: str) -> enr.EnrForkId:
    return enr.consensus_entries("phase0", enr.from_text(text)).eth2


def _mainnet_root() -> bytes:
    # The genesis state starts with its 8-byte genesis time, then the genesis validators root.
    return archives.download(GENESIS_ARCHIVE).read_bytes()[8:40]


def _check_recovery(config: dict[str, Any] | None, root: bytes) -> None:
    """Each listed digest is found at an epoch with that digest.

    The digest just before a listed epoch is that of the previous one.
    """
    epochs = digest_epochs("mainnet", config)
    for index, start in enumerate(epochs):
        digest = compute_fork_digest("mainnet", root, start, config)
        found = fork_of_digest("mainnet", root, digest, config)
        assert found is not None
        assert compute_fork_digest("mainnet", root, found[0], config) == digest
        if index > 0:
            # The epoch before a listed epoch has the digest of the listed epoch before it.
            before = compute_fork_digest("mainnet", root, start - 1, config)
            assert before == compute_fork_digest("mainnet", root, epochs[index - 1], config)


def test_mainnet_epochs() -> None:
    assert digest_epochs("mainnet") == [*MAINNET_EPOCHS, FAR_FUTURE_EPOCH]


@pytest.mark.archive(GENESIS_ARCHIVE)
def test_mainnet_record() -> None:
    eth2 = _eth2(MAINNET_RECORD)
    assert (eth2.next_fork_version, eth2.next_fork_epoch) == (bytes.fromhex("01000000"), 74240)
    root = _mainnet_root()
    assert fork_of_digest("mainnet", root, eth2.fork_digest) == (0, "phase0")
    assert compute_fork_digest("mainnet", root, 0) == eth2.fork_digest


@pytest.mark.archive(GENESIS_ARCHIVE)
def test_mainnet_identifies() -> None:
    root = _mainnet_root()
    assert digests_identify("mainnet", root)
    _check_recovery(None, root)


def test_sepolia() -> None:
    assert digest_epochs("mainnet", SEPOLIA) == [
        0,
        50,
        100,
        56832,
        132608,
        222464,
        272640,
        274176,
        275712,
        353024,
        FAR_FUTURE_EPOCH,
    ]
    eth2 = _eth2(SEPOLIA_RECORD)
    assert (eth2.next_fork_version, eth2.next_fork_epoch) == (
        bytes.fromhex("90000071"),
        FAR_FUTURE_EPOCH,
    )
    assert fork_of_digest("mainnet", SEPOLIA_ROOT, eth2.fork_digest, SEPOLIA) == (100, "bellatrix")
    assert digests_identify("mainnet", SEPOLIA_ROOT, SEPOLIA)
    _check_recovery(SEPOLIA, SEPOLIA_ROOT)


def test_hoodi() -> None:
    # Altair to Deneb start at genesis, so epoch 0 is listed once.
    assert digest_epochs("mainnet", HOODI) == [0, 2048, 50688, 52480, 54016, FAR_FUTURE_EPOCH]
    eth2 = _eth2(HOODI_RECORD)
    assert (eth2.next_fork_version, eth2.next_fork_epoch) == (bytes.fromhex("60000910"), 2048)
    assert fork_of_digest("mainnet", HOODI_ROOT, eth2.fork_digest, HOODI) == (0, "dencun")
    assert digests_identify("mainnet", HOODI_ROOT, HOODI)
    _check_recovery(HOODI, HOODI_ROOT)


def test_blob_schedule_changes_the_digest() -> None:
    """Each blob schedule entry has a digest of its own, and reads back Fulu, named fusaka."""
    digests = [
        compute_fork_digest("mainnet", HOODI_ROOT, epoch, HOODI) for epoch in (50688, 52480, 54016)
    ]
    assert len(set(digests)) == 3
    for epoch, digest in zip((50688, 52480, 54016), digests, strict=True):
        assert fork_of_digest("mainnet", HOODI_ROOT, digest, HOODI) == (epoch, "fusaka")


def test_unknown_digest() -> None:
    """A digest of another chain, here Hoodi's Deneb digest on Sepolia, names no epoch."""
    assert fork_of_digest("mainnet", SEPOLIA_ROOT, _eth2(HOODI_RECORD).fork_digest, SEPOLIA) is None


def test_shared_version_fails_the_check() -> None:
    """With Altair given the version of genesis, the digest of Altair reads back Phase 0."""
    config = {**SEPOLIA, "ALTAIR_FORK_VERSION": SEPOLIA["GENESIS_FORK_VERSION"]}
    altair = compute_fork_digest("mainnet", SEPOLIA_ROOT, 50, config)
    assert altair == compute_fork_digest("mainnet", SEPOLIA_ROOT, 0, config)
    assert fork_of_digest("mainnet", SEPOLIA_ROOT, altair, config) == (0, "phase0")
    assert not digests_identify("mainnet", SEPOLIA_ROOT, config)


def test_unknown_configuration() -> None:
    with raises(ConsensusError, "no configuration is named nowhere"):
        digest_epochs("nowhere")
