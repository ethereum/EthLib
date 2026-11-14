"""Pure libp2p QUIC certificate handshakes with explicit algorithm policies and private inputs."""

from typing import Literal, TypeAlias, TypedDict, cast

from ethlib.cryptography import _native
from ethlib.errors import TlsStepError as TlsStepError
from ethlib.networking.libp2p.tls import Policy as CertificatePolicy
from ethlib.networking.quic.tls import CertificateRequest, ClientHello, Extension

Level: TypeAlias = Literal["initial", "handshake", "application"]
Phase: TypeAlias = Literal[
    "server_hello",
    "encrypted_extensions",
    "certificate_request",
    "server_certificate",
    "server_certificate_verify",
    "server_finished",
    "client_hello",
    "client_certificate",
    "client_certificate_verify",
    "client_finished",
    "complete",
]


class FlightMessage(TypedDict):
    """One complete handshake message and its QUIC CRYPTO encryption level."""

    level: Level
    data: bytes


class Policy(TypedDict):
    """Accepted algorithms and certificate checks, without a default application profile."""

    cipher_suites: list[int]
    groups: list[int]
    signature_schemes: list[int]
    certificates: CertificatePolicy
    reject_legacy_session_id: bool


class EphemeralKey(TypedDict):
    """A named group and its 32-byte private input for one handshake."""

    group: int
    secret: bytes


class Config(TypedDict):
    """One endpoint's policy, credentials and fresh ephemeral keys, for one handshake only."""

    policy: Policy
    now: int
    certificates: list[bytes]
    signing_key: bytes
    random: bytes
    ephemeral_keys: list[EphemeralKey]
    initial_shares: list[int]
    transport_parameters: bytes


class Transcript(TypedDict):
    """The exact sent and received handshake bytes, and whether a retry occurred."""

    bytes: list[int]
    retried: bool


class Retry(TypedDict):
    """The suite, optional requested group and optional cookie fixed by a retry."""

    suite: int
    group: int | None
    cookie: Extension | None


class TrafficSecrets(TypedDict):
    """The no-PSK SHA-256 schedule through the first application traffic generation."""

    early: bytes
    handshake: bytes
    master: bytes
    client_handshake: bytes
    server_handshake: bytes
    client_application: bytes
    server_application: bytes


class Negotiated(TypedDict):
    """Negotiated algorithms, ECDHE output, transcript boundaries and traffic secrets."""

    suite: int
    group: int
    shared_secret: bytes
    hello_transcript: bytes
    server_transcript: bytes
    secrets: TrafficSecrets


class State(TypedDict):
    """Saved inputs returned by initialization and successful handshake steps."""

    phase: Phase
    transcript: Transcript
    hello: ClientHello | None
    retry: Retry | None
    negotiated: Negotiated | None
    peer_chain: list[bytes]
    request: CertificateRequest | None


class Completion(TypedDict):
    """The certificate-derived peer identity, its chain and the negotiated key schedule."""

    peer_id: bytes
    peer_chain: list[bytes]
    negotiated: Negotiated


class Step(TypedDict):
    """The next state, outgoing messages and an optional completion."""

    state: State
    output: list[FlightMessage]
    completion: Completion | None


def client_start(config: Config) -> Step:
    """Return the ClientHello flight and the state that awaits ServerHello."""
    return cast("Step", _native.quic_tls_client_start(cast("dict[str, object]", config)))


def server_start(config: Config) -> State:
    """Validate local inputs and wait for ClientHello under an explicit policy."""
    return cast("State", _native.quic_tls_server_start(cast("dict[str, object]", config)))


def client_step(
    config: Config, expected_peer_id: bytes, state: State, message: FlightMessage
) -> Step:
    """Process a server message and check the dialled peer ID."""
    return cast(
        "Step",
        _native.quic_tls_client_step(
            cast("dict[str, object]", config),
            expected_peer_id,
            cast("dict[str, object]", state),
            cast("dict[str, object]", message),
        ),
    )


def server_step(config: Config, state: State, message: FlightMessage) -> Step:
    """Process a client message and require the libp2p client certificate."""
    return cast(
        "Step",
        _native.quic_tls_server_step(
            cast("dict[str, object]", config),
            cast("dict[str, object]", state),
            cast("dict[str, object]", message),
        ),
    )


__all__ = [
    "Completion",
    "Config",
    "EphemeralKey",
    "FlightMessage",
    "Level",
    "Negotiated",
    "Phase",
    "Policy",
    "Retry",
    "State",
    "Step",
    "TlsStepError",
    "TrafficSecrets",
    "Transcript",
    "client_start",
    "client_step",
    "server_start",
    "server_step",
]
