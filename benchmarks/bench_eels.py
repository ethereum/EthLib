"""The execution-specs side, with the Osaka fork modules."""

# python bench_eels.py <data directory> <results file>

import hashlib
import sys
from types import SimpleNamespace

from benchlib import Runner, load
from ethereum import state_mpt as S
from ethereum.crypto.elliptic_curve import secp256k1_recover
from ethereum.crypto.hash import keccak256, keccak512
from ethereum.forks.osaka import transactions as T
from ethereum.forks.osaka.blocks import Block, Header
from ethereum.forks.osaka.fork import calculate_base_fee_per_gas
from ethereum.forks.osaka.fork_types import Address
from ethereum.forks.osaka.vm.gas import calculate_blob_gas_price, calculate_memory_gas_cost
from ethereum.forks.osaka.vm.instructions import Ops, op_implementation
from ethereum.forks.osaka.vm.precompiled_contracts.mapping import PRE_COMPILED_CONTRACTS
from ethereum.merkle_patricia_trie import Trie, root as trie_root, trie_set
from ethereum.state import Account
from ethereum_rlp import rlp
from ethereum_types.bytes import Bytes, Bytes32
from ethereum_types.numeric import U64, U256, Uint
from py_ecc.bls import G2ProofOfPossession as P

inp = load(sys.argv[1], "inputs.json")
R = Runner("eels", sys.argv[2])
x = bytes.fromhex

d32, d100k = x(inp["bytes_32"]), x(inp["bytes_100k"])
R.run("keccak256_32", lambda: keccak256(d32))
R.run("keccak256_100k", lambda: keccak256(d100k))
R.run("keccak512_32", lambda: keccak512(d32))
R.run("keccak512_100k", lambda: keccak512(d100k))
R.run("sha256_32", lambda: hashlib.sha256(d32).digest())
R.run("sha256_100k", lambda: hashlib.sha256(d100k).digest())

block = x(inp["block"])
tx = x(inp["tx"])
block_item = rlp.decode(block)
tx_item = rlp.decode(tx[1:])
R.run("rlp_decode_block", lambda: rlp.decode(block))
R.run("rlp_encode_block", lambda: rlp.encode(block_item))
R.run("rlp_decode_tx", lambda: rlp.decode(tx[1:]))
R.run("rlp_encode_tx", lambda: rlp.encode(tx_item))
R.run("block_decode_encode", lambda: rlp.encode(rlp.decode_to(Block, block)))
hdr = rlp.encode(block_item[0])
R.run("block_header_hash", lambda: keccak256(rlp.encode(rlp.decode_to(Header, hdr))))

pairs = [(Bytes(x(k)), Bytes(x(v))) for k, v in inp["trie_pairs"]]


def eels_trie_root(secured: bool):
    """The root of the trie of the 1000 pairs."""
    t = Trie(secured=secured, default=Bytes(b""))
    for k, v in pairs:
        trie_set(t, k, v)
    return trie_root(t)


R.run("trie_root_1000", lambda: eels_trie_root(False))
R.run("trie_root_1000_secured", lambda: eels_trie_root(True))


def eels_state_root():
    """The state root of the 200 accounts."""
    st = S.State()
    for a, nonce, bal, code, storage in inp["state"]:
        addr = Address(x(a))
        code_hash = S.store_code(st, Bytes(x(code)))
        S.set_account(st, addr, Account(nonce=Uint(nonce), balance=U256(bal), code_hash=code_hash))
        for k, v in storage:
            S.set_storage(st, addr, Bytes32(x(k)), U256(v))
    return S.state_root(st)


R.run("state_root_200", eels_state_root)

R.run("tx_hash", lambda: T.get_transaction_hash(Bytes(tx)))
R.run("tx_recover_sender", lambda: T.recover_sender(T.decode_transaction(Bytes(tx))))
R.run(
    "tx_intrinsic_gas",
    lambda: T.calculate_intrinsic_cost(T.decode_transaction(Bytes(tx))),
    norm=lambda r: int(r.regular),
)
R.run(
    "secp256k1_recover",
    lambda: secp256k1_recover(
        U256.from_be_bytes(x(inp["secp_sig"])[:32]),
        U256.from_be_bytes(x(inp["secp_sig"])[32:]),
        U256(inp["secp_v"]),
        Bytes32(x(inp["secp_hash"])),
    ),
)

pc = inp["precompiles"]
ADDR = {
    "ecrecover": 1,
    "sha256": 2,
    "ripemd160": 3,
    "identity": 4,
    "modexp_small": 5,
    "modexp_large": 5,
    "bn_add": 6,
    "bn_mul": 7,
    "bn_pairing2": 8,
    "blake2f": 9,
    "blake2f_10k": 9,
    "point_evaluation": 10,
    "bls_g1add": 0x0B,
    "bls_g1msm": 0x0C,
    "bls_g2add": 0x0D,
    "bls_g2msm": 0x0E,
    "bls_pairing": 0x0F,
    "bls_map_fp_to_g1": 0x10,
    "bls_map_fp2_to_g2": 0x11,
    "p256verify": 0x100,
}


def call(addr: int, data: bytes) -> bytes:
    """Run the precompile at `addr` on `data` and return its output."""
    fn = PRE_COMPILED_CONTRACTS[Address(addr.to_bytes(20, "big"))]
    evm = SimpleNamespace(
        message=SimpleNamespace(data=Bytes(data)), gas_left=Uint(10**9), output=Bytes(b"")
    )
    fn(evm)
    return bytes(evm.output)


for name, addr in ADDR.items():
    data = x(pc[name])
    R.run("pc_" + name, lambda a=addr, d=data: call(a, d))

w = inp["words"]
OPS = {
    "ADD": (0x01, 2),
    "MUL": (0x02, 2),
    "DIV": (0x04, 2),
    "SDIV": (0x05, 2),
    "ADDMOD": (0x08, 3),
    "MULMOD": (0x09, 3),
    "EXP": (0x0A, 2),
    "SIGNEXTEND": (0x0B, 2),
    "BYTE": (0x1A, 2),
    "SHL": (0x1B, 2),
    "SAR": (0x1D, 2),
    "CLZ": (0x1E, 1),
}
SMALL = {"SIGNEXTEND": 15, "BYTE": 7, "SHL": 77, "SAR": 77}


def word_op(op: int, args):
    """Run one instruction on a stack of words and return the top."""
    evm = SimpleNamespace(stack=[U256(a) for a in reversed(args)], gas_left=Uint(10**9), pc=Uint(0))
    op_implementation[Ops(op)](evm)
    return int(evm.stack[-1])


for name, (op, k) in OPS.items():
    args = list(w[:k])
    if name in SMALL:
        args[0] = SMALL[name]
    R.run("evm_" + name, lambda op=op, a=args: word_op(op, a))
R.run("evm_memory_gas_cost", lambda: int(calculate_memory_gas_cost(Uint(1 << 20))))
R.run(
    "fees_base_fee",
    lambda: int(
        calculate_base_fee_per_gas(
            Uint(45_000_000), Uint(45_000_000), Uint(30_000_000), Uint(7 * 10**8)
        )
    ),
)
R.run("fees_blob_base_fee", lambda: int(calculate_blob_gas_price(U64(50_000_000))))

# BLS signatures in pure Python (py_ecc 8), the library execution-specs uses for its curve code.
sk = int.from_bytes(x(inp["bls_sk"]), "big")
msg = x(inp["bls_msg"])
pks = [x(p) for p in inp["bls_pks"]]
sig0 = x(inp["bls_sig0"])
sigs16, msgs16 = [x(s) for s in inp["bls_sigs16"]], [x(m) for m in inp["bls_msgs16"]]
agg16, fast = x(inp["bls_aggsig16"]), x(inp["bls_fast_sig"])
R.run("bls_sign@py_ecc", lambda: P.Sign(sk, msg))
R.run("bls_verify@py_ecc", lambda: P.Verify(pks[0], msg, sig0))
R.run("bls_aggregate_16@py_ecc", lambda: P.Aggregate(sigs16))
R.run(
    "bls_aggregate_verify_16@py_ecc", lambda: P.AggregateVerify(pks[:16], msgs16, agg16), budget=0
)
R.run(
    "bls_fast_aggregate_verify_512@py_ecc", lambda: P.FastAggregateVerify(pks, msg, fast), budget=0
)
