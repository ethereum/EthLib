"""Era files, which hold the beacon blocks and states of the chain, one group per era."""

from dataclasses import dataclass
from typing import Any

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import EraError as EraError


@dataclass(frozen=True, slots=True, kw_only=True)
class EraBlock:
    """One block of a group: its slot, the fork of its slot, its SSZ bytes and its root."""

    slot: int
    # The name of the fork in EthLib, such as "shapella" for Capella.
    fork: str
    block: bytes
    root: bytes


@dataclass(frozen=True, slots=True, kw_only=True)
class EraGroup:
    """One group of an era file: its era, its blocks, and the state at the end of the era."""

    era: int
    blocks: tuple[EraBlock, ...]
    state_fork: str
    state: bytes
    # The records between the state and the indices, each as its type and its data.
    others: tuple[tuple[int, bytes], ...]


@dataclass(frozen=True, slots=True, kw_only=True)
class EraFile:
    """The groups of an era file, and the name the file should carry."""

    # None when the name cannot be computed, as when the state of the highest era has no root.
    name: str | None
    groups: tuple[EraGroup, ...]


def decode_era(name: str, data: bytes, config: dict[str, Any] | None = None) -> EraFile:
    """The name and the groups of an era file at a named preset and configuration, or EraError."""
    file_name, groups = _native.era_decode(name, config, data)
    return EraFile(
        name=file_name,
        groups=tuple(
            EraGroup(
                era=era,
                blocks=tuple(
                    EraBlock(slot=slot, fork=fork, block=block, root=root)
                    for slot, fork, block, root in blocks
                ),
                state_fork=state_fork,
                state=state,
                others=tuple(others),
            )
            for era, blocks, state_fork, state, others in groups
        ),
    )


__all__ = ["EraBlock", "EraError", "EraFile", "EraGroup", "decode_era"]
