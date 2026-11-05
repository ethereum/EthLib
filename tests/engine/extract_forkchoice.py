"""Write the chains of `forkchoice.json` from the unpacked release archive."""

import json
import sys
from pathlib import Path

# The tests kept for each network: those with the most payloads, then in path order.
TESTS_PER_NETWORK = 3


def main(fixtures: Path, out: Path) -> None:
    """Keep the chain of payloads of a few tests of each network, with some invalid payloads."""
    chains = {}
    for path in sorted(fixtures.rglob("*.json")):
        relative = path.relative_to(fixtures.parent).as_posix()
        for name, test in json.loads(path.read_text()).items():
            network = test["network"]
            if "Amsterdam" in network:
                continue
            payloads = [
                {
                    "blockHash": p["params"][0]["blockHash"],
                    "parentHash": p["params"][0]["parentHash"],
                    "valid": not p.get("validationError") and "errorCode" not in p,
                    "forkchoiceUpdatedVersion": p["forkchoiceUpdatedVersion"],
                }
                for p in test["engineNewPayloads"]
            ]
            if all(p["valid"] for p in payloads) and len(payloads) < 3:
                continue
            chains.setdefault(network, []).append(
                {
                    "file": relative,
                    "test": name,
                    "network": network,
                    "genesisHash": test["genesisBlockHeader"]["hash"],
                    "payloads": payloads,
                    "lastblockhash": test["lastblockhash"],
                }
            )
    kept = []
    for network in sorted(chains):
        ranked = sorted(chains[network], key=lambda c: -len(c["payloads"]))
        kept += ranked[:TESTS_PER_NETWORK]
    out.write_text(json.dumps(kept, indent=1) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
