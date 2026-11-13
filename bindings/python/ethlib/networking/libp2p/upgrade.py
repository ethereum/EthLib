"""The upgrade of a TCP connection between consensus nodes: Noise, then a multiplexer."""

# Every domain links into one extension module.
# That module lives in the `cryptography` package.
from ethlib.cryptography import _native


def tcp(dialer_yamux: bool, listener_yamux: bool) -> tuple[bytes, bytes]:
    """The security protocol and multiplexer that a dialer and a listener agree on."""
    return _native.libp2p_upgrade(dialer_yamux, listener_yamux)


__all__ = ["tcp"]
