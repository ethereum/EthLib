"""Write the MODEXP calls of the EIP-198 state tests, with the outcome of each at each fork."""

import json
import sys
from pathlib import Path

root, out = Path(sys.argv[1]), Path(sys.argv[2])
cases = []
for path in sorted(root.glob("state_tests/*/byzantium/eip198_modexp_precompile/modexp/*.json")):
    if "amsterdam" in path.as_posix():
        continue
    for name, test in sorted(json.loads(path.read_text()).items()):
        tx = test["transaction"]
        (data,) = tx["data"]
        (gas_limit,) = tx["gasLimit"]
        for network, posts in sorted(test["post"].items()):
            if "Amsterdam" in network:
                continue
            (post,) = posts
            state = post["state"]
            caller = state[tx["to"]]
            success = int(caller["storage"].get("0x00", "0x00"), 16) == 1
            # The contract that the caller creates holds the output of a successful call.
            created = [
                address
                for address in state
                if address not in test["pre"] and address != tx["sender"]
            ]
            output = state[created[0]]["code"] if success else None
            cases.append(
                {
                    "file": path.relative_to(root.parent).as_posix(),
                    "test": name.split("::")[-1],
                    "network": network,
                    "input": data,
                    "gasLimit": int(gas_limit, 16),
                    "success": success,
                    "output": output,
                }
            )
lines = (json.dumps(case, sort_keys=True, separators=(",", ":")) for case in cases)
out.write_text("[\n" + ",\n".join(lines) + "\n]\n")
print(len(cases), sum(case["success"] for case in cases))
