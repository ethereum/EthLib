"""Native codec call sites retain their structural Python types."""

from typing import TYPE_CHECKING

from ethlib.cryptography import _native
from ethlib.networking import quic
from ethlib.networking.quic import tls

# Python 3.10 runs the codecs too; assert_type is available to the type checker on Python 3.12.
if TYPE_CHECKING:
    from typing import assert_type

    def check_native_codec_signatures(
        header: quic.Header,
        frame: quic.Frame,
        packet: quic.PacketType,
        handshake: tls.Message,
        payload: tls.Payload,
        form: tls.PayloadForm,
        extension: tls.Extension,
    ) -> None:
        assert_type(_native.quic_header_encode(header), bytes)
        assert_type(_native.quic_header_decode(0, b""), tuple[quic.Header, bytes])
        assert_type(_native.quic_frame_encode(frame), bytes)
        assert_type(_native.quic_frame_decode(packet, b""), tuple[quic.Frame, bytes])
        assert_type(_native.quic_tls_message_encode(32, handshake), bytes)
        assert_type(_native.quic_tls_message_decode(32, b""), tuple[tls.Message, bytes])
        assert_type(_native.quic_tls_payload_encode(payload), tls.Extension)
        assert_type(_native.quic_tls_payload_decode(form, extension), tls.Payload)

        # These malformed tags or fields must remain type errors at the native boundary.
        _native.quic_header_encode(("initial", [], [], [], 0, 0))  # ty: ignore[invalid-argument-type]
        _native.quic_frame_encode(("crypto", 0, b""))  # ty: ignore[invalid-argument-type]
        _native.quic_frame_decode("retry", b"")  # ty: ignore[invalid-argument-type]
        _native.quic_tls_message_encode(32, ("finished", b""))  # ty: ignore[invalid-argument-type]
        _native.quic_tls_payload_encode(("key_share", []))  # ty: ignore[invalid-argument-type]
        _native.quic_tls_payload_decode("alpn", b"")  # ty: ignore[invalid-argument-type]
        _native.quic_tls_payload_decode("unknown", extension)  # ty: ignore[invalid-argument-type]
