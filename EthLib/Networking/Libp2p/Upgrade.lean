module

public import EthLib.Networking.Libp2p.Mplex
public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Libp2p.Yamux

/-!
# The upgrade of a TCP connection between consensus nodes

The upgrade follows the section Upgrading Connections of [libp2p connections][up].

On TCP, the consensus layer uses Noise for security, named as in [noise-libp2p][noise].

The consensus layer requires mplex, allows yamux, and puts yamux first when a node supports it.

The Noise handshake runs between the two negotiations, and is not run here.

The multiplexer always has its own negotiation, since inlining it in the handshake is optional.

The consensus layer names only Noise, and whether a node may propose another first is open.

[up]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/connections/README.md#upgrading-connections
[noise]: https://github.com/libp2p/specs/blob/4facaf9876da1eb7d6e066982010c81495ebb965/noise/README.md#negotiation
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Upgrade

/-- The name of noise-libp2p in multistream-select. -/
def noiseId : ByteArray :=
  -- noise-libp2p is identified by the protocol ID string /noise.
  "/noise".toUTF8

/-- What a consensus node on TCP supports for the upgrade: mplex always, yamux maybe. -/
structure TcpProfile where
  /-- Whether the node supports yamux. -/
  supportsYamux : Bool
  deriving DecidableEq, Repr

/-- The security protocols that a node proposes, and also those it supports: Noise only. -/
def securityProposals : List ByteArray :=
  -- The consensus layer names only Noise.
  [noiseId]

/-- The multiplexers that a node proposes in order, and also those it supports.

yamux comes first when the node supports it. -/
def TcpProfile.muxers (profile : TcpProfile) : List ByteArray :=
  -- mplex is required and yamux allowed; with both, yamux takes precedence in the negotiation.
  if profile.supportsYamux then [Yamux.protocolId, Mplex.protocolId] else [Mplex.protocolId]

/-- The security protocol, then the multiplexer, that a dialer and a listener agree on. -/
def upgrade (dialer listener : TcpProfile) : Option (ByteArray × ByteArray) := do
  -- Security is always established first, by one multistream-select negotiation.
  --
  -- The dialer proposes and the listener echoes a protocol it supports, or answers na.
  let security ← Multistream.negotiate securityProposals securityProposals
  -- Then the Noise handshake secures the channel.
  --
  -- The stream multiplexer is negotiated over the encrypted channel, in the same manner.
  let muxer ← Multistream.negotiate dialer.muxers listener.muxers
  -- With security and stream multiplexing established, the upgrade is complete.
  return (security, muxer)

end EthLib.Networking.Libp2p.Upgrade
