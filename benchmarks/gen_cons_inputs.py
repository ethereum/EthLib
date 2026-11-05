"""Write the Snappy, SSZ and KZG inputs of the benchmarks, in the consensus-specs environment."""

# python gen_cons_inputs.py <consensus-specs checkout> <data directory> [validators]
#
# Each SSZ case holds its type and value in the tagged JSON that the EthLib binding reads,
# and the bytes that pyspec serializes it to.

import hashlib
import json
import sys
from pathlib import Path

import snappy
from eth_consensus_specs.fulu import mainnet as spec, minimal as spec_min
from ssz.bitfields import BitList, BitVector
from ssz.boolean import Boolean
from ssz.byte_arrays import ByteList, ByteVector
from ssz.collections import List, Vector
from ssz.container import Container
from ssz.uint import BaseUint

CONS = Path(sys.argv[1])
DATA = Path(sys.argv[2])
N_VALIDATORS = int(sys.argv[3]) if len(sys.argv) > 3 else 10_000


def h(b: bytes) -> bytes:
    """SHA-256 of a byte string."""
    return hashlib.sha256(b).digest()


def tdesc(T):
    """The tagged JSON of an SSZ type."""
    if issubclass(T, Boolean):
        return "bool"
    if issubclass(T, BaseUint):
        return {"uint": T.BYTE_LENGTH}
    if issubclass(T, ByteVector):
        return {"byte_vector": T.LENGTH}
    if issubclass(T, ByteList):
        return {"byte_list": T.LIMIT}
    if issubclass(T, BitVector):
        return {"bitvector": T.LENGTH}
    if issubclass(T, BitList):
        return {"bitlist": T.LIMIT}
    if issubclass(T, Vector):
        return {"vector": [tdesc(T.ELEMENT_TYPE), T.LENGTH]}
    if issubclass(T, List):
        return {"list": [tdesc(T.ELEMENT_TYPE), T.LIMIT]}
    if issubclass(T, Container):
        return {"container": [[k, tdesc(f.annotation)] for k, f in T.model_fields.items()]}
    raise TypeError(T)


def vdoc(T, v):
    """The tagged JSON of a value of type `T`."""
    if issubclass(T, Boolean):
        return {"bool": bool(v)}
    if issubclass(T, BaseUint):
        return {"uint": int(v)}
    if issubclass(T, (ByteVector, ByteList)):
        return {"bytes": "0x" + bytes(v).hex()}
    if issubclass(T, (BitVector, BitList)):
        return {"bits": [bool(b) for b in v]}
    if issubclass(T, (Vector, List)):
        return {"seq": [vdoc(T.ELEMENT_TYPE, e) for e in v]}
    if issubclass(T, Container):
        return {"seq": [vdoc(f.annotation, getattr(v, k)) for k, f in T.model_fields.items()]}
    raise TypeError(T)


def validator(i: int, spec=spec):
    """The validator number `i`."""
    return spec.Validator(
        pubkey=spec.BLSPubkey(
            h(b"pk" + i.to_bytes(4, "big")) + h(b"pk2" + i.to_bytes(4, "big"))[:16]
        ),
        withdrawal_credentials=spec.Bytes32(h(b"wc" + i.to_bytes(4, "big"))),
        effective_balance=spec.Gwei(32 * 10**9),
        slashed=False,
        activation_eligibility_epoch=spec.Epoch(i % 100),
        activation_epoch=spec.Epoch(i % 100 + 1),
        exit_epoch=spec.FAR_FUTURE_EPOCH,
        withdrawable_epoch=spec.FAR_FUTURE_EPOCH,
    )


def make_state(n: int, spec=spec):
    """A beacon state with `n` validators."""
    st = spec.BeaconState()
    st.genesis_time = spec.Uint64(1606824023)
    st.slot = spec.Slot(12_000_000)
    st.validators = spec.BeaconState.model_fields["validators"].annotation(
        data=[validator(i, spec) for i in range(n)]
    )
    st.balances = spec.BeaconState.model_fields["balances"].annotation(
        data=[spec.Gwei(32 * 10**9 + i) for i in range(n)]
    )
    part = spec.BeaconState.model_fields["previous_epoch_participation"].annotation
    st.previous_epoch_participation = part(data=[spec.ParticipationFlags(i % 8) for i in range(n)])
    st.current_epoch_participation = part(
        data=[spec.ParticipationFlags((i + 3) % 8) for i in range(n)]
    )
    st.inactivity_scores = spec.BeaconState.model_fields["inactivity_scores"].annotation(
        data=[spec.Uint64(i % 5) for i in range(n)]
    )
    st.randao_mixes = spec.BeaconState.model_fields["randao_mixes"].annotation(
        data=[
            spec.Bytes32(h(b"mix" + i.to_bytes(4, "big")))
            for i in range(spec.EPOCHS_PER_HISTORICAL_VECTOR)
        ]
    )
    st.block_roots = spec.BeaconState.model_fields["block_roots"].annotation(
        data=[
            spec.Root(h(b"br" + i.to_bytes(4, "big")))
            for i in range(spec.SLOTS_PER_HISTORICAL_ROOT)
        ]
    )
    return st


out = {}
# Snappy: 100 KB of compressible data (a repetitive JSON-like text with varying numbers).
raw = b"".join(
    b'{"slot":%d,"root":"%s"},' % (i, h(bytes([i % 7])).hex().encode()) for i in range(1300)
)[:100_000]
out["snappy_raw_sha256"] = hashlib.sha256(raw).hexdigest()
out["snappy_raw"] = raw.hex()
out["snappy_block"] = snappy.compress(raw).hex()
c = snappy.StreamCompressor()
out["snappy_framed"] = (c.add_chunk(raw)).hex()

cases = {}
st = make_state(N_VALIDATORS)
# (type, value, whether the EthLib side times the serialization of the case)
cases["beacon_state_mainnet_%dv" % N_VALIDATORS] = (spec.BeaconState, st, False)
st_min = make_state(1000, spec_min)
cases["beacon_state_minimal_1000v"] = (spec_min.BeaconState, st_min, True)
VL = spec.BeaconState.model_fields["validators"].annotation
cases["validators_1000"] = (VL, VL(data=list(st.validators)[:1000]), True)
BL = spec.BeaconState.model_fields["balances"].annotation
cases["balances_%d" % N_VALIDATORS] = (BL, st.balances, True)
ssz_out = {}
for name, (T, v, ser) in cases.items():
    ssz_out[name] = {
        "serialize": ser,
        "type": tdesc(T),
        "value": vdoc(T, v),
        "bytes": v.encode_bytes().hex(),
        "root": v.hash_tree_root().hex()
        if hasattr(v, "hash_tree_root")
        else spec.hash_tree_root(v).hex(),
    }
out["ssz"] = ssz_out
out["n_validators"] = N_VALIDATORS
(DATA / "cons_inputs.json").write_text(json.dumps(out))
print("wrote", DATA / "cons_inputs.json", {k: len(v["bytes"]) // 2 for k, v in ssz_out.items()})

# The KZG trusted setup of the pinned consensus-specs, in the text format of c-kzg-4844.
setup = json.loads((CONS / "presets/mainnet/trusted_setups/trusted_setup_4096.json").read_text())
lines = [str(len(setup["g1_lagrange"])), str(len(setup["g2_monomial"]))]
for key in ("g1_lagrange", "g2_monomial", "g1_monomial"):
    lines += [p.removeprefix("0x") for p in setup[key]]
(DATA / "trusted_setup_4096.txt").write_text("\n".join(lines) + "\n")
