"""Era1 files, which hold the execution blocks before the Merge."""

from dataclasses import dataclass

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native
from ethlib.errors import Era1Error as Era1Error


@dataclass(frozen=True, slots=True, kw_only=True)
class Era1Block:
    """One block of an era1 file: its header, body and receipts as RLP, and its total difficulty."""

    header: bytes
    body: bytes
    receipts: bytes
    total_difficulty: int


@dataclass(frozen=True, slots=True, kw_only=True)
class Era1File:
    """The contents of an era1 file."""

    starting_number: int
    blocks: tuple[Era1Block, ...]
    # The records between the blocks and the accumulator, each as its type and its data.
    others: tuple[tuple[int, bytes], ...]
    accumulator: bytes


def decode_era1(data: bytes) -> Era1File:
    """The contents of an era1 file; a file that does not verify raises Era1Error."""
    starting_number, blocks, others, accumulator = _native.era1_decode(data)
    return Era1File(
        starting_number=starting_number,
        blocks=tuple(
            Era1Block(header=header, body=body, receipts=receipts, total_difficulty=td)
            for header, body, receipts, td in blocks
        ),
        others=tuple(others),
        accumulator=accumulator,
    )


__all__ = ["Era1Block", "Era1Error", "Era1File", "decode_era1"]
