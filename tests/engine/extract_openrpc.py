"""Write the examples of `openrpc.json` from the OpenRPC method files of the Engine API."""

import json
import sys
from pathlib import Path

import yaml


def main(methods: Path, out: Path) -> None:
    """Keep the parameters and the result of every example of every method, in file order."""
    examples = []
    for path in sorted(methods.glob("*.yaml")):
        for method in yaml.safe_load(path.read_text()):
            # Some methods have no example.
            for example in method.get("examples", []):
                examples.append(
                    {
                        "file": path.name,
                        "method": method["name"],
                        "example": example["name"],
                        "params": [param["value"] for param in example["params"]],
                        "result": example["result"]["value"],
                    }
                )
    out.write_text(json.dumps(examples, indent=1) + "\n")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
