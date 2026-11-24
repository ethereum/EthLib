"""The code and message of the errors that the cryptography exports pass to Python."""

from collections.abc import Callable

import pytest

from ethlib.cryptography import (
    aes,
    bls,
    crc32,
    ethash,
    kdf,
    keystore,
    kzg,
    secp256k1,
    secp256r1,
)
from ethlib.cryptography.chacha20_poly1305 import (
    chacha20_crypt,
    chacha20_poly1305_decrypt,
    chacha20_poly1305_encrypt,
    chacha20_quarter_round_state,
)
from ethlib.cryptography.x25519 import x25519
from ethlib.errors import (
    AesError,
    BindingError,
    BlsError,
    ChaCha20Poly1305Error,
    ConcatKdfError,
    EthashError,
    EthLibError,
    HkdfError,
    KeyDerivationError,
    KeystoreError,
    KzgError,
    Pbkdf2Error,
    ScryptError,
    Secp256k1Error,
    Secp256r1Error,
    Tls13Error,
    X25519Error,
)
from raising import raises

# Keccak-f, the VRF, XMSS and SPHINCS have no case.
# The bindings check the sizes of their inputs before Lean runs.
# So a wrong size raises ValueError, without a code, and never reaches Lean.
# The one other error, of XMSS and SPHINCS, needs a one-time key that never reaches a codeword.

# An export turns the typed error of an operation into a code and a message.
# Each case pins one way of doing so, with the code and the message that Python sees.


@pytest.mark.parametrize(
    ("error", "code", "message", "call"),
    [
        # The secret key 0 is not in [1, r - 1].
        pytest.param(
            BlsError,
            13,
            "invalid secret key",
            lambda: bls.sign(bytes(32), b"message"),
            id="bls",
        ),
        # The 47 zero bytes are not a compressed G1 point.
        pytest.param(
            BlsError,
            4,
            "invalid G1 point",
            lambda: bls.decode_g1(bytes(47)),
            id="bls-g1",
        ),
        # The child index is a 32-bit number.
        pytest.param(
            BlsError,
            0,
            "expected an int below 4294967296, got 4294967296",
            lambda: bls.derive_child_sk(bytes(32), 2**32),
            id="bls-argument",
        ),
        # A path starts with m.
        pytest.param(
            KeyDerivationError,
            101,
            'path must start with m, not "x"',
            lambda: bls.derive_path(bytes(32), "x"),
            id="key-derivation-path",
        ),
        # A seed of 31 bytes, below the 32 bytes that key generation needs.
        pytest.param(
            KeyDerivationError,
            14,
            "input keying material too short: 31 bytes",
            lambda: bls.derive_path(bytes(31), "m/12381/3600/0/0"),
            id="key-derivation-bls",
        ),
        # The validator index is a 32-bit number.
        pytest.param(
            KeyDerivationError,
            0,
            "expected an int below 4294967296, got 4294967296",
            lambda: bls.withdrawal_path(2**32),
            id="key-derivation-argument",
        ),
        # Field element 0 of this blob is the modulus, so it is not canonical.
        pytest.param(
            KzgError,
            8,
            "invalid field element at index 0",
            lambda: kzg.blob_to_kzg_commitment(
                bytes.fromhex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001")
                + bytes(kzg.BYTES_PER_BLOB - 32)
            ),
            id="kzg",
        ),
        # A recovery id is 0 or 1.
        pytest.param(
            Secp256k1Error,
            13,
            "bad recovery id: 2, expected 0 or 1",
            lambda: secp256k1.recover(bytes(32), bytes(64), 2),
            id="secp256k1",
        ),
        # A public key is 64 bytes.
        pytest.param(
            Secp256r1Error,
            1,
            "bad public key size: 63, expected 64",
            lambda: secp256r1.verify(bytes(63), bytes(32), bytes(64)),
            id="secp256r1",
        ),
        # A tag of 12 bytes, where the tag length is 16.
        pytest.param(
            AesError,
            1,
            "EthLib.Cryptography.Aes.Gcm.Error.tagLength 16 12",
            lambda: aes.gcm_decrypt(bytes(16), bytes(12), b"", b"", bytes(12), 16),
            id="aes-gcm",
        ),
        # An AES key is 16 or 32 bytes.
        pytest.param(
            AesError,
            0,
            "bad key size: 15, expected 16 or 32",
            lambda: aes.encrypt_block(bytes(15), bytes(16)),
            id="aes-key",
        ),
        # The zero tag does not authenticate the empty message.
        pytest.param(
            ChaCha20Poly1305Error,
            3,
            "EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.authenticationFailed",
            lambda: chacha20_poly1305_decrypt(bytes(32), bytes(12), b"", b"", bytes(16)),
            id="chacha20-poly1305",
        ),
        # Two blocks from the last counter value run past 2^32.
        pytest.param(
            ChaCha20Poly1305Error,
            1,
            (
                "EthLib.Cryptography.ChaCha20Poly1305.ChaCha20Poly1305Error.counterExhausted "
                "4294967295 128"
            ),
            lambda: chacha20_crypt(bytes(32), 2**32 - 1, bytes(12), bytes(128)),
            id="chacha20-counter",
        ),
        # A nonce is 12 bytes.
        pytest.param(
            ChaCha20Poly1305Error,
            0,
            "expected 12 bytes, got 11",
            lambda: chacha20_poly1305_encrypt(bytes(32), bytes(11), b"", b""),
            id="chacha20-argument",
        ),
        # An empty object has no version field.
        pytest.param(
            KeystoreError,
            2,
            (
                "EthLib.Cryptography.Keystore.KeystoreError.invalidField "
                '"keystore.version" "property not found: version"'
            ),
            lambda: keystore.decrypt("{}", "password"),
            id="keystore",
        ),
        # The cost n is a power of two.
        pytest.param(
            ScryptError,
            1,
            "EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidCost 3",
            lambda: kdf.scrypt(b"password", b"salt", 3, 1, 1, 32),
            id="scrypt",
        ),
        # A Salsa20/8 block is 64 bytes.
        pytest.param(
            ScryptError,
            6,
            "EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidInputSize 64 63",
            lambda: kdf.salsa208(bytes(63)),
            id="scrypt-block",
        ),
        # PBKDF2 takes at least one iteration.
        pytest.param(
            Pbkdf2Error,
            1,
            "EthLib.Cryptography.Hash.Pbkdf2.Pbkdf2Error.zeroIterations",
            lambda: kdf.pbkdf2(b"password", b"salt", 0, 32),
            id="pbkdf2",
        ),
        # HKDF-SHA-256 gives at most 255 * 32 = 8160 bytes.
        pytest.param(
            HkdfError,
            2,
            "EthLib.Cryptography.Hash.Hkdf.HkdfError.outputTooLong 8161",
            lambda: kdf.hkdf(b"", b"", b"", 8161),
            id="hkdf",
        ),
        # The Concatenation KDF refuses a length of zero.
        pytest.param(
            ConcatKdfError,
            1,
            "EthLib.Cryptography.Hash.ConcatKdf.ConcatKdfError.emptyOutput",
            lambda: kdf.concat_kdf(b"", b"", 0),
            id="concat-kdf",
        ),
        # A label without its tls13 prefix is at most 249 bytes.
        pytest.param(
            Tls13Error,
            1,
            "EthLib.Cryptography.Hash.Tls13.Error.labelLength 300",
            lambda: kdf.tls13_hkdf_label(bytes(300), b"", 32),
            id="tls13",
        ),
        # A scalar is 32 bytes.
        pytest.param(
            X25519Error,
            0,
            "expected 32 bytes, got 31",
            lambda: x25519(bytes(31), bytes(32)),
            id="x25519",
        ),
        # A block number is an int, not a bool.
        pytest.param(
            EthashError,
            0,
            "expected an int",
            lambda: ethash.cache_size(True),
            id="ethash-argument",
        ),
        # A cache is a positive multiple of 64 bytes.
        pytest.param(
            EthashError,
            0,
            "Ethash: a cache is a positive multiple of 64 bytes, got 63",
            lambda: ethash.dataset_item(bytes(63), 0),
            id="ethash-cache",
        ),
        # The input must be bytes, not a str.
        pytest.param(
            BindingError,
            0,
            "expected bytes",
            lambda: crc32.digest("abc"),  # ty: ignore[invalid-argument-type]
            id="crc32",
        ),
        # The text is not JSON.
        pytest.param(
            KeystoreError,
            1,
            ('EthLib.Cryptography.Keystore.KeystoreError.invalidJson "the text is not JSON"'),
            lambda: keystore.decrypt("not json", "password"),
            id="keystore-json",
        ),
        # An empty object names no key derivation function.
        pytest.param(
            KeystoreError,
            2,
            (
                'EthLib.Cryptography.Keystore.KeystoreError.invalidField "kdf.function" '
                '"property not found: function"'
            ),
            lambda: keystore.encrypt("{}", "{}", bytes(16), "password", b""),
            id="keystore-encrypt",
        ),
        # A state has 16 words, so index 16 is past its end.
        pytest.param(
            ChaCha20Poly1305Error,
            0,
            "quarter-round index must be below 16",
            lambda: chacha20_quarter_round_state(bytes(64), 16, 0, 0, 0),
            id="chacha20-quarter-round",
        ),
        # A header hash is 32 bytes.
        pytest.param(
            EthashError,
            0,
            "Ethash: a header hash is 32 bytes, got 31",
            lambda: ethash.hashimoto_light(1024, bytes(64), bytes(31), bytes(8)),
            id="ethash-header",
        ),
        # The block size r is at least 1.
        pytest.param(
            ScryptError,
            2,
            "EthLib.Cryptography.Hash.Scrypt.ScryptError.invalidBlockSize 0",
            lambda: kdf.scrypt_block_mix(bytes(64), 0),
            id="scrypt-mix",
        ),
    ],
)
def test_code_and_message(
    error: type[EthLibError], code: int, message: str, call: Callable[[], object]
) -> None:
    with raises(error, message) as info:
        call()
    assert type(info.value) is error
    assert info.value.code == code
