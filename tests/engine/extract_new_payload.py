"""Write the engine_newPayload cases of `new_payload.json` from the unpacked release archive."""

import json
import sys
from pathlib import Path
from typing import Final

# The exceptions that the checks before execution can find.
STATIC = (
    "BlockException.INVALID_BLOCK_HASH",
    "BlockException.INCORRECT_BLOCK_FORMAT",
    "BlockException.RLP_STRUCTURES_ENCODING",
    "BlockException.INVALID_VERSIONED_HASHES",
    "TransactionException.TYPE_3_TX_PRE_FORK",
    "TransactionException.TYPE_4_TX_PRE_FORK",
    "TransactionException.TYPE_3_TX_CONTRACT_CREATION",
    "TransactionException.TYPE_4_TX_CONTRACT_CREATION",
)

# The valid payloads kept for each network, and the size above which parameters are large.
VALID_PER_NETWORK = 6
MAX_PARAMS = 8_000

# The networks of Amsterdam that are kept: Amsterdam, and the move to it from BPO2.
# The networks after Amsterdam that change only the blob schedule are left out.
AMSTERDAM: Final = ("Amsterdam", "BPO2ToAmsterdamAtTime15k")


def _typed(payload: dict) -> bool:
    """Whether a payload holds a typed transaction, whose first byte is a type below 0x80."""
    return any(int(tx[2:4], 16) < 0x80 for tx in payload["params"][0].get("transactions", []))


def main(fixtures: Path, out: Path) -> None:
    """Keep each case that a check before execution decides, and a few valid payloads."""
    cases = []
    valid: dict[str, int] = {}
    # The versions of the method that a kept valid payload with a typed transaction covers.
    typed: set[int] = set()
    large: set[tuple[bool, str]] = set()
    for path in sorted(fixtures.rglob("*.json")):
        relative = path.relative_to(fixtures.parent).as_posix()
        for name, test in json.loads(path.read_text()).items():
            network = test["network"]
            if "Amsterdam" in network and network not in AMSTERDAM:
                continue
            # The files come in sorted order, and Amsterdam's come first.
            # Its large cases are counted apart, so the earlier networks keep the same cases.
            amsterdam = network in AMSTERDAM
            for index, payload in enumerate(test["engineNewPayloads"]):
                error = payload.get("validationError") or ""
                size = len(json.dumps(payload["params"]))
                if "errorCode" in payload or any(e in error.split("|") for e in STATIC):
                    # Keep one large case of each exception, such as a blob transaction with blobs.
                    keep = size <= MAX_PARAMS or (amsterdam, error) not in large
                    if size > MAX_PARAMS:
                        large.add((amsterdam, error))
                elif not error and size <= MAX_PARAMS and valid.get(network, 0) < VALID_PER_NETWORK:
                    valid[network] = valid.get(network, 0) + 1
                    keep = True
                elif not error and size <= MAX_PARAMS:
                    # Keep the first valid payload with a typed transaction of each version.
                    keep = _typed(payload) and payload["newPayloadVersion"] not in typed
                else:
                    keep = False
                if keep and not error and "errorCode" not in payload and _typed(payload):
                    typed.add(payload["newPayloadVersion"])
                if keep:
                    cases.append(
                        {
                            "file": relative,
                            "test": name,
                            "payload": index,
                            "network": network,
                            "method": f"engine_newPayloadV{payload['newPayloadVersion']}",
                            "params": payload["params"],
                            "validationError": payload.get("validationError"),
                            "errorCode": payload.get("errorCode"),
                        }
                    )
    out.write_text(json.dumps(cases, indent=1) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
