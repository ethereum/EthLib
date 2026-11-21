module

public import EthLib.Networking.Enr.Record

/-!
# `Networking.Enr.Address`

The addresses and ports of a node record, which say where the node listens.

Six keys of the key table of [EIP-778] give the addresses and ports.

- `ip` and `ip6`: an IPv4 address of 4 bytes, and an IPv6 address of 16 bytes.
- `tcp` and `udp`: the TCP and UDP ports of the IPv4 address.
- `tcp6` and `udp6`: the TCP and UDP ports of the IPv6 address.

The consensus layer adds `quic` and `quic6`: the UDP ports of libp2p over QUIC, for IPv4 and IPv6.

Provenance: the [ENR structure] of the consensus networking text states these two keys.

A port is a "big endian integer" with no stated size.

Here it is an RLP scalar below `2^16`: no leading zero byte, and zero is the empty string.

When `tcp6` or `udp6` is absent, the `tcp` or `udp` port "applies to both IP addresses".

No source gives `quic` that rule, so an IPv6 endpoint without `quic6` has no QUIC port.

[EIP-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md#L50-L67
[ENR structure]: https://github.com/ethereum/consensus-specs/blob/aa16bb4c156184e9548a997d53efaf2a228a6304/specs/phase0/p2p-interface.md#L1712-L1731
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Serialization.Rlp

/-- The key `ip`, in ASCII. -/
def KEY_IP : ByteArray := ⟨#[0x69, 0x70]⟩

/-- The key `ip6`, in ASCII. -/
def KEY_IP6 : ByteArray := ⟨#[0x69, 0x70, 0x36]⟩

/-- The key `tcp`, in ASCII. -/
def KEY_TCP : ByteArray := ⟨#[0x74, 0x63, 0x70]⟩

/-- The key `tcp6`, in ASCII. -/
def KEY_TCP6 : ByteArray := ⟨#[0x74, 0x63, 0x70, 0x36]⟩

/-- The key `udp`, in ASCII. -/
def KEY_UDP : ByteArray := ⟨#[0x75, 0x64, 0x70]⟩

/-- The key `udp6`, in ASCII. -/
def KEY_UDP6 : ByteArray := ⟨#[0x75, 0x64, 0x70, 0x36]⟩

/-- The key `quic`, in ASCII. -/
def KEY_QUIC : ByteArray := ⟨#[0x71, 0x75, 0x69, 0x63]⟩

/-- The key `quic6`, in ASCII. -/
def KEY_QUIC6 : ByteArray := ⟨#[0x71, 0x75, 0x69, 0x63, 0x36]⟩

/-- An address of `size` bytes and the ports that a node listens on there.

The size is 4 for IPv4 and 16 for IPv6. -/
structure Endpoint (size : Nat) where
  /-- The address, in network byte order. -/
  ip : Vector UInt8 size
  /-- The TCP port, if any. -/
  tcp : Option UInt16
  /-- The UDP port, if any. -/
  udp : Option UInt16
  /-- The UDP port of libp2p over QUIC, if any. -/
  quic : Option UInt16
  deriving DecidableEq, Repr

/-- The address under a key, if the record has the key.

The value must be a byte string of exactly `size` bytes. -/
def readAddress (r : Enr) (key : ByteArray) (size : Nat) :
    Except EnrError (Option (Vector UInt8 size)) :=
  match r.get key with
  | none => return none
  | some value => some <$> (Codec.ofItem value).mapError fun _ => .invalidAddress key value

/-- The port under a key, if the record has the key.

The value must be an RLP scalar below `2^16`. -/
def readPort (r : Enr) (key : ByteArray) : Except EnrError (Option UInt16) :=
  match r.get key with
  | none => return none
  | some value => some <$> (Codec.ofItem value).mapError fun _ => .invalidPort key value

/-- The IPv4 and IPv6 endpoints of a record, each absent when its address is.

It reads all eight keys first, so a malformed value fails even when its address is absent.

The IPv6 endpoint takes the `tcp` and `udp` ports when `tcp6` and `udp6` are absent.

It does not check the signature. -/
def Enr.endpoints (r : Enr) : Except EnrError (Option (Endpoint 4) × Option (Endpoint 16)) := do
  let ip ← readAddress r KEY_IP 4
  let ip6 ← readAddress r KEY_IP6 16
  let tcp ← readPort r KEY_TCP
  let tcp6 ← readPort r KEY_TCP6
  let udp ← readPort r KEY_UDP
  let udp6 ← readPort r KEY_UDP6
  let quic ← readPort r KEY_QUIC
  let quic6 ← readPort r KEY_QUIC6
  return (ip.map (⟨·, tcp, udp, quic⟩), ip6.map (⟨·, tcp6 <|> tcp, udp6 <|> udp, quic6⟩))

/-- The IPv6 endpoint as a reader sees it, next to an IPv4 endpoint.

A TCP or UDP port that it lacks is the one of the IPv4 endpoint. -/
def Endpoint.inherit (e6 : Endpoint 16) (e4 : Option (Endpoint 4)) : Endpoint 16 :=
  { e6 with tcp := e6.tcp <|> e4.bind (·.tcp), udp := e6.udp <|> e4.bind (·.udp) }

/-- An IPv6 port to write: none when it equals the IPv4 port, which then applies to both.

[EIP-778] says that declaring one port in both keys "should be avoided".

[EIP-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md#L64-L66
-/
def ipv6Port (port6 port : Option UInt16) : Option UInt16 :=
  if port6 = port then none else port6

/-- The pairs of an IPv4 and an IPv6 endpoint, in key order, to put in a new record.

An absent value writes no pair.

An IPv6 TCP or UDP port equal to the IPv4 one is not written again.

Other entries fall between these keys, so a caller merges them in key order. -/
def endpointPairs (e4 : Option (Endpoint 4)) (e6 : Option (Endpoint 16)) :
    List (ByteArray × Item) :=
  let tcp := e4.bind (·.tcp)
  let udp := e4.bind (·.udp)
  [(KEY_IP, (e4.map (·.ip)).map Codec.toItem),
    (KEY_IP6, (e6.map (·.ip)).map Codec.toItem),
    (KEY_QUIC, (e4.bind (·.quic)).map Codec.toItem),
    (KEY_QUIC6, (e6.bind (·.quic)).map Codec.toItem),
    (KEY_TCP, tcp.map Codec.toItem),
    (KEY_TCP6, (ipv6Port (e6.bind (·.tcp)) tcp).map Codec.toItem),
    (KEY_UDP, udp.map Codec.toItem),
    (KEY_UDP6, (ipv6Port (e6.bind (·.udp)) udp).map Codec.toItem)].filterMap
    fun (key, value) => value.map (key, ·)

end EthLib.Networking.Enr
