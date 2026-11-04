"""The exceptions of the bindings carry the code and the message of the Lean error.

Each expected code is the one that the Lean type of the error defines.
"""

import pytest

from ethlib import consensus, errors
from ethlib.cryptography import bls, kdf, kzg, secp256k1, secp256r1
from ethlib.execution import blocks, transactions
from ethlib.networking import discv5, enr, reqresp, snappy, varint
from ethlib.precompiles import ecrecover, modexp, run, sha256
from ethlib.serialization import rlp
from ethlib.state import StateError, state_root


def test_kzg_error_carries_code_and_message() -> None:
    # Field element 0 of this blob is the modulus, so it is not canonical.
    blob = bytes.fromhex(
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
    ) + bytes(kzg.BYTES_PER_BLOB - 32)
    with pytest.raises(kzg.KzgError) as info:
        kzg.blob_to_kzg_commitment(blob)
    # The code of an invalid field element.
    assert info.value.code == 8
    assert info.value.message == "invalid field element at index 0"
    assert str(info.value) == info.value.message


def test_bls_error_code() -> None:
    # The secret key 0 is not in [1, r - 1].
    with pytest.raises(bls.BlsError) as info:
        bls.sign(bytes(32), b"message")
    assert info.value.code == 13


def test_secp256k1_error_code() -> None:
    # A recovery id is 0 or 1.
    with pytest.raises(secp256k1.Secp256k1Error) as info:
        secp256k1.recover(bytes(32), bytes(64), 2)
    assert info.value.code == 13


def test_secp256r1_error_code() -> None:
    # A public key of 63 bytes.
    with pytest.raises(secp256r1.Secp256r1Error) as info:
        secp256r1.verify(bytes(63), bytes(32), bytes(64))
    assert info.value.code == 1


def test_modexp_error_code() -> None:
    # Lengths 1, 1 and 1, then the base, the exponent and the modulus: the price is above 0.
    data = (1).to_bytes(32, "big") * 3 + b"\x02\x03\x05"
    with pytest.raises(modexp.ModexpError) as info:
        modexp.modexp(data, 0)
    # The code of a lack of gas.
    assert info.value.code == 2


def test_precompile_error_names_the_precompile() -> None:
    data = (1).to_bytes(32, "big") * 3 + b"\x02\x03\x05"
    with pytest.raises(errors.PrecompileError) as info:
        run(0x05, data, 0)
    # The code of MODEXP among the precompiles.
    assert info.value.code == 5
    assert "outOfGas" in info.value.message


def test_no_precompile_has_code_zero() -> None:
    with pytest.raises(errors.PrecompileError) as info:
        run(0x12, b"", 0)
    assert info.value.code == 0


def test_state_error_code() -> None:
    # The RLP list of one account, given twice: a 20-byte address, nonce 0, balance 0,
    # no code and no storage.
    account = bytes([0xD9, 0x94]) + bytes(20) + bytes([0x80, 0x80, 0x80, 0xC0])
    with pytest.raises(StateError) as info:
        state_root(bytes([0xF4]) + account + account)
    # The code of an address given twice.
    assert info.value.code == 4


def test_hkdf_error_code() -> None:
    # HKDF-SHA-256 gives at most 255 * 32 = 8160 bytes.
    with pytest.raises(kdf.HkdfError) as info:
        kdf.hkdf(b"", b"", b"", 8161)
    assert info.value.code == 2


def test_concat_kdf_error_code() -> None:
    # The Concatenation KDF refuses a length of zero.
    with pytest.raises(kdf.ConcatKdfError) as info:
        kdf.concat_kdf(b"", b"", 0)
    assert info.value.code == 1


def test_gas_error_codes() -> None:
    # Each of these precompiles fails only for lack of gas, with code 1.
    with pytest.raises(ecrecover.EcrecoverError) as info:
        ecrecover.ecrecover(b"", 0)
    assert info.value.code == 1
    with pytest.raises(sha256.Sha256PrecompileError) as info:
        sha256.sha256(b"", 0)
    assert info.value.code == 1


def test_enr_error_code() -> None:
    # The byte 0x01 is a whole RLP item, so the byte after it is left over.
    with pytest.raises(enr.EnrError) as info:
        enr.seq(b"\x01\x02")
    # The code of bytes that are not one RLP item.
    assert info.value.code == 2


def test_reqresp_error_code() -> None:
    # A lone byte 0xff starts a varint and never ends it.
    with pytest.raises(reqresp.ReqRespError) as info:
        reqresp.decode_payload(100, b"\xff")
    # The code of a bad varint prefix.
    assert info.value.code == 1


def test_block_error_codes() -> None:
    with pytest.raises(blocks.BlockError) as info:
        blocks.header_hash("nofork", b"")
    assert info.value.code == 0
    # Empty bytes are no RLP item, so the code is one of the RLP error codes.
    with pytest.raises(blocks.BlockError) as info:
        blocks.header_hash("london", b"")
    assert 1 <= info.value.code <= 14


def test_varint_error_code() -> None:
    # The byte 0x80 asks for another byte, and none follows.
    with pytest.raises(varint.VarintError) as info:
        varint.decode(b"\x80")
    # The code of an unterminated varint.
    assert info.value.code == 1


def test_snappy_error_ranges() -> None:
    # A block error has a code below 101, and a frame error a code from 101 on.
    with pytest.raises(snappy.SnappyError) as info:
        snappy.decompress(b"")
    assert 1 <= info.value.code <= 8
    with pytest.raises(snappy.SnappyError) as info:
        snappy.decode_frames(b"\x00")
    assert 101 <= info.value.code <= 109


def test_rlp_error_codes() -> None:
    # An empty input holds no item.
    with pytest.raises(rlp.RlpError) as info:
        rlp.decode(b"")
    assert 1 <= info.value.code <= 14
    with pytest.raises(rlp.RlpError) as info:
        rlp.decode_as("no such type", b"")
    assert info.value.code == 0


def test_transaction_and_discv5_codes() -> None:
    with pytest.raises(transactions.TransactionError) as info:
        transactions.tx_type("nofork", b"")
    assert info.value.code == 0
    # A node ID of 31 bytes is not one that discv5 accepts.
    with pytest.raises(discv5.Discv5Error) as info:
        discv5.log_distance(bytes(31), bytes(32))
    assert info.value.code == 0


def test_unknown_names_have_code_zero() -> None:
    # No Lean error type covers a name that the binding does not know.
    with pytest.raises(consensus.ConsensusError) as info:
        consensus.preset("nopreset")
    assert info.value.code == 0


@pytest.mark.parametrize(
    ("cls", "bases"),
    [
        (errors.KzgError, (RuntimeError,)),
        (errors.BlsError, (ValueError, RuntimeError)),
        (errors.XmssError, (ValueError, RuntimeError)),
        (errors.SphincsError, (RuntimeError,)),
        (errors.Secp256k1Error, (ValueError,)),
        (errors.Secp256r1Error, (ValueError,)),
        (errors.EnrError, (ValueError,)),
        (errors.EcrecoverError, (ValueError,)),
        (errors.ModexpError, (ValueError,)),
        (errors.Sha256PrecompileError, (ValueError,)),
        (errors.PrecompileError, (ValueError,)),
        (errors.StateError, (ValueError,)),
        (errors.KeccakError, (ValueError,)),
        (errors.ReqRespError, (ValueError,)),
        (errors.ConsensusError, (ValueError,)),
        (errors.HkdfError, (ValueError,)),
        (errors.ConcatKdfError, (ValueError,)),
        (errors.AesError, (ValueError,)),
        (errors.BlockError, (ValueError,)),
        (errors.RlpError, (ValueError,)),
        (errors.SnappyError, (ValueError,)),
        (errors.VarintError, (ValueError,)),
        (errors.Discv5Error, (ValueError,)),
        (errors.RlpxError, (ValueError,)),
        (errors.TransactionError, (ValueError,)),
        (errors.VrfError, (ValueError,)),
        (errors.TrieError, (ValueError,)),
    ],
)
def test_classes_keep_the_old_bases(cls: type, bases: tuple[type, ...]) -> None:
    # A caller that caught the old class still catches the failure.
    assert issubclass(cls, errors.EthLibError)
    for base in bases:
        assert issubclass(cls, base)
