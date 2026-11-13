module

public import EthLib.Networking.Libp2p.Mplex
public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Libp2p.Yamux

/-!
# The upgrade of a TCP connection between consensus nodes

A raw TCP connection gets security first, then a stream multiplexer over the secured channel.

Each is chosen by one multistream-select negotiation, as [libp2p connections][up] says.

On TCP, the consensus layer uses Noise for security, named as in [noise-libp2p][noise].

The consensus layer requires mplex, allows yamux, and puts yamux first when a node supports it.

The Noise handshake runs between the two negotiations, and is not run here.

The multiplexer always has its own negotiation, since inlining it in the handshake is optional.

The consensus layer names only Noise, and whether a node may propose another first is open.

[up]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md#upgrading-connections
[noise]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/noise/README.md#negotiation
-/

@[expose] public section

namespace EthLib.Networking.Libp2p.Upgrade

/-- The name of noise-libp2p in multistream-select. -/
def noiseId : ByteArray := "/noise".toUTF8

/-- What a consensus node on TCP supports for the upgrade: mplex always, yamux maybe. -/
structure TcpProfile where
  /-- Whether the node supports yamux. -/
  supportsYamux : Bool
  deriving DecidableEq, Repr

/-- The security protocols that a node proposes, and also those it supports: Noise only. -/
def securityProposals : List ByteArray := [noiseId]

/-- The multiplexers that a node proposes in order, and also those it supports.

yamux comes first when the node supports it. -/
def TcpProfile.muxers (profile : TcpProfile) : List ByteArray :=
  if profile.supportsYamux then [Yamux.protocolId, Mplex.protocolId] else [Mplex.protocolId]

/-- The security protocol, then the multiplexer, that a dialer and a listener agree on. -/
def upgrade (dialer listener : TcpProfile) : Option (ByteArray × ByteArray) := do
  let security ← Multistream.negotiate securityProposals securityProposals
  let muxer ← Multistream.negotiate dialer.muxers listener.muxers
  return (security, muxer)

end EthLib.Networking.Libp2p.Upgrade
