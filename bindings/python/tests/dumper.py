"""
YAML emission and on-disk layout shared across spec test-vector
generators.

`write_case(spec, handler, case, data)` writes
`tests/cryptography/<spec>/<handler>/<case>/data.yaml`. Emission uses `ruamel.yaml`
with `default_flow_style=None` and a `0x…`-string representer forcing
single-quotes.
"""
import io
from pathlib import Path

from ruamel.yaml import YAML


def _build_data_yaml() -> YAML:
    yaml = YAML(pure=True)
    yaml.default_flow_style = None

    def _repr_none(self, _):
        return self.represent_scalar("tag:yaml.org,2002:null", "null")

    def _repr_str(self, data):
        if data.startswith("0x"):
            return self.represent_scalar("tag:yaml.org,2002:str", data, style="'")
        return self.represent_str(data)

    yaml.representer.add_representer(type(None), _repr_none)
    yaml.representer.add_representer(str, _repr_str)
    return yaml


_DATA_YAML = _build_data_yaml()


# ---- Hex encoding ---------------------------------------------------------

def hex_str(b: bytes) -> str:
    return "0x" + b.hex()


def hex_list(bs) -> list[str]:
    return [hex_str(b) for b in bs]


# ---- On-disk layout -------------------------------------------------------

# Output goes to the repo's top-level `tests/` directory.
_REPO = Path(__file__).resolve().parents[3]
ROOT  = _REPO / "tests" / "cryptography"


def _dump(yaml: YAML, data) -> str:
    sio = io.StringIO()
    yaml.dump(data, sio)
    return sio.getvalue()


def write_case(spec: str, handler: str, case: str, data: dict) -> Path:
    case_dir = ROOT / spec / handler / case
    case_dir.mkdir(parents=True, exist_ok=True)
    (case_dir / "data.yaml").write_text(_dump(_DATA_YAML, data))
    return case_dir
