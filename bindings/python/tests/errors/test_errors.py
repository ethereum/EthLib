"""The exceptions of the bindings carry the code and the message of the Lean error.

Each expected code is the one that the Lean type of the error defines.
"""

import pytest

from ethlib import consensus, errors
from ethlib.cryptography import bls, kdf, kzg, secp256k1, secp256r1
from ethlib.execution import blocks, transactions
from ethlib.networking import discv5, enr, reqresp, snappy, varint
from ethlib.precompiles import run
from ethlib.serialization import rlp
from ethlib.state import StateError, state_root
from raising import raises


def test_kzg_error_carries_code_and_message() -> None:
    # Field element 0 of this blob is the modulus, so it is not canonical.
    blob = bytes.fromhex(
        "73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"
    ) + bytes(kzg.BYTES_PER_BLOB - 32)
    with raises(kzg.KzgError, "invalid field element at index 0") as info:
        kzg.blob_to_kzg_commitment(blob)
    # The code of an invalid field element.
    assert info.value.code == 8
    assert info.value.message == "invalid field element at index 0"
    assert str(info.value) == info.value.message


def test_bls_error_code() -> None:
    # The secret key 0 is not in [1, r - 1].
    with raises(bls.BlsError, "invalid secret key") as info:
        bls.sign(bytes(32), b"message")
    assert info.value.code == 13


def test_secp256k1_error_code() -> None:
    # A recovery id is 0 or 1.
    with raises(secp256k1.Secp256k1Error, "bad recovery id: 2, expected 0 or 1") as info:
        secp256k1.recover(bytes(32), bytes(64), 2)
    assert info.value.code == 13


def test_secp256r1_error_code() -> None:
    # A public key of 63 bytes.
    with raises(secp256r1.Secp256r1Error, "bad public key size: 63, expected 64") as info:
        secp256r1.verify(bytes(63), bytes(32), bytes(64))
    assert info.value.code == 1


def test_precompile_error_names_the_precompile() -> None:
    data = (1).to_bytes(32, "big") * 3 + b"\x02\x03\x05"
    with raises(
        errors.PrecompileError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp\n  "
            "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.outOfGas 500 0)"
        ),
    ) as info:
        run("fusaka", 0x05, data, 0)
    # The code of MODEXP among the precompiles.
    assert info.value.code == 5
    assert "outOfGas" in info.value.message


def test_no_precompile_has_code_zero() -> None:
    with raises(errors.PrecompileError, "no precompile at address 18 at fork fusaka") as info:
        run("fusaka", 0x12, b"", 0)
    assert info.value.code == 0


def test_state_error_code() -> None:
    # The RLP list of one account, given twice: a 20-byte address, nonce 0, balance 0,
    # no code and no storage.
    account = bytes([0xD9, 0x94]) + bytes(20) + bytes([0x80, 0x80, 0x80, 0xC0])
    with raises(StateError, "an address is given twice") as info:
        state_root(bytes([0xF4]) + account + account)
    # The code of an address given twice.
    assert info.value.code == 4


def test_hkdf_error_code() -> None:
    # HKDF-SHA-256 gives at most 255 * 32 = 8160 bytes.
    with raises(
        kdf.HkdfError, "EthLib.Cryptography.Hash.Hkdf.HkdfError.outputTooLong 8161"
    ) as info:
        kdf.hkdf(b"", b"", b"", 8161)
    assert info.value.code == 2


def test_concat_kdf_error_code() -> None:
    # The Concatenation KDF refuses a length of zero.
    with raises(
        kdf.ConcatKdfError, "EthLib.Cryptography.Hash.ConcatKdf.ConcatKdfError.emptyOutput"
    ) as info:
        kdf.concat_kdf(b"", b"", 0)
    assert info.value.code == 1


@pytest.mark.parametrize(
    "address, code, error",
    [
        (
            0x01,
            1,
            (
                "ecrecover\n  "
                "(EthLib.Execution.Evm.Precompiles.Ecrecover.EcrecoverError.outOfGas 3000 0)"
            ),
        ),
        (0x02, 2, "sha256\n  (EthLib.Execution.Evm.Precompiles.Sha256.Sha256Error.outOfGas 60 0)"),
        (
            0x03,
            3,
            (
                "ripemd160\n  "
                "(EthLib.Execution.Evm.Precompiles.Ripemd160.Ripemd160Error.outOfGas 600 0)"
            ),
        ),
        (
            0x04,
            4,
            "identity\n  (EthLib.Execution.Evm.Precompiles.Identity.IdentityError.outOfGas 15 0)",
        ),
    ],
)
def test_precompile_codes_of_frontier(address: int, code: int, error: str) -> None:
    # Each of these precompiles fails only for lack of gas, and the code names the precompile.
    message = f"EthLib.Execution.Evm.Precompiles.PrecompileError.{error}"
    with raises(errors.PrecompileError, message) as info:
        run("frontier", address, b"", 0)
    assert info.value.code == code
    assert "outOfGas" in info.value.message


def test_modexp_length_too_large() -> None:
    # From Fusaka, a length above 1024 bytes fails before any gas is charged.
    data = (1025).to_bytes(32, "big") + bytes(64)
    with raises(
        errors.PrecompileError,
        (
            "EthLib.Execution.Evm.Precompiles.PrecompileError.modexp\n  "
            "(EthLib.Execution.Evm.Precompiles.Modexp.ModexpError.lengthTooLarge\n    "
            "(EthLib.Execution.Evm.Precompiles.Modexp.LengthField.base)\n    1025)"
        ),
    ) as info:
        run("fusaka", 0x05, data, 10**6)
    assert info.value.code == 5
    assert "lengthTooLarge" in info.value.message


def test_enr_error_code() -> None:
    # The byte 0x01 is a whole RLP item, so the byte after it is left over.
    with raises(enr.EnrError, "record is not one RLP item") as info:
        enr.seq(b"\x01\x02")
    # The code of bytes that are not one RLP item.
    assert info.value.code == 2


def test_reqresp_error_code() -> None:
    # A lone byte 0xff starts a varint and never ends it.
    with raises(reqresp.ReqRespError, "length prefix is not a valid varint") as info:
        reqresp.decode_payload(100, b"\xff")
    # The code of a bad varint prefix.
    assert info.value.code == 1


def test_block_error_codes() -> None:
    with raises(blocks.BlockError, "no fork named nofork") as info:
        blocks.header_hash("nofork", b"")
    assert info.value.code == 0
    # Empty bytes are no RLP item, so the code is one of the RLP error codes.
    with raises(
        blocks.BlockError, "header rejected: EthLib.Serialization.Rlp.RlpError.inputTooShort 1 0"
    ) as info:
        blocks.header_hash("london", b"")
    assert 1 <= info.value.code <= 14


def test_varint_error_code() -> None:
    # The byte 0x80 asks for another byte, and none follows.
    with raises(
        varint.VarintError,
        "varint rejected: EthLib.Networking.Encoding.Varint.VarintError.unterminated",
    ) as info:
        varint.decode(b"\x80")
    # The code of an unterminated varint.
    assert info.value.code == 1


def test_snappy_error_ranges() -> None:
    # A block error has a code below 101, and a frame error a code from 101 on.
    with raises(
        snappy.SnappyError, "block rejected: EthLib.Networking.Snappy.SnappyError.preambleTruncated"
    ) as info:
        snappy.decompress(b"")
    assert 1 <= info.value.code <= 8
    with raises(
        snappy.SnappyError,
        "stream rejected: EthLib.Networking.Snappy.FrameError.missingStreamIdentifier",
    ) as info:
        snappy.decode_frames(b"\x00")
    assert 101 <= info.value.code <= 109


def test_rlp_error_codes() -> None:
    # An empty input holds no item.
    with raises(
        rlp.RlpError, "input rejected: EthLib.Serialization.Rlp.RlpError.inputTooShort 1 0"
    ) as info:
        rlp.decode(b"")
    assert 1 <= info.value.code <= 14
    with raises(rlp.RlpError, "unknown RLP type") as info:
        rlp.decode_as("no such type", b"")
    assert info.value.code == 0


def test_transaction_and_discv5_codes() -> None:
    with raises(transactions.TransactionError, "no fork named nofork") as info:
        transactions.tx_type("nofork", b"")
    assert info.value.code == 0
    # A node ID of 31 bytes is not one that discv5 accepts.
    with raises(discv5.Discv5Error, "node ID has 31 bytes, not 32") as info:
        discv5.log_distance(bytes(31), bytes(32))
    assert info.value.code == 0


def test_unknown_names_have_code_zero() -> None:
    # No Lean error type covers a name that the binding does not know.
    with raises(consensus.ConsensusError, "no preset is named nopreset") as info:
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
