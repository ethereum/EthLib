"""Write the engine_newPayload cases of `new_payload.json` from the unpacked release archive."""

import json
import sys
from pathlib import Path

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


def main(fixtures: Path, out: Path) -> None:
    """Keep each case that a check before execution decides, and a few valid payloads."""
    cases = []
    valid = {}
    large = set()
    for path in sorted(fixtures.rglob("*.json")):
        relative = path.relative_to(fixtures.parent).as_posix()
        for name, test in json.loads(path.read_text()).items():
            network = test["network"]
            if "Amsterdam" in network:
                continue
            for index, payload in enumerate(test["engineNewPayloads"]):
                error = payload.get("validationError") or ""
                size = len(json.dumps(payload["params"]))
                if "errorCode" in payload or any(e in error.split("|") for e in STATIC):
                    # Keep one large case of each exception, such as a blob transaction with blobs.
                    keep = size <= MAX_PARAMS or error not in large
                    if size > MAX_PARAMS:
                        large.add(error)
                elif not error and size <= MAX_PARAMS and valid.get(network, 0) < VALID_PER_NETWORK:
                    valid[network] = valid.get(network, 0) + 1
                    keep = True
                else:
                    keep = False
                if keep:
                    cases.append({
                        "file": relative, "test": name, "payload": index, "network": network,
                        "method": f"engine_newPayloadV{payload['newPayloadVersion']}",
                        "params": payload["params"],
                        "validationError": payload.get("validationError"),
                        "errorCode": payload.get("errorCode"),
                    })
    out.write_text(json.dumps(cases, indent=1) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
