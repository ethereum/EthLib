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

[EIP-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md#L50-L67
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

/-- The address under a key, if the record has the key. -/
def readAddress (r : Enr) (key : ByteArray) (size : Nat) :
    Except EnrError (Option (Vector UInt8 size)) :=
  match r.get key with
  -- All keys except `id` are optional, including IP addresses.
  | none => return none
  -- `ip`: IPv4 address, 4 bytes; `ip6`: IPv6 address, 16 bytes.
  --
  -- The value is a byte string of exactly `size` bytes, and any other value fails.
  | some value => some <$> (Codec.ofItem value).mapError fun _ => .invalidAddress key value

/-- The port under a key, if the record has the key. -/
def readPort (r : Enr) (key : ByteArray) : Except EnrError (Option UInt16) :=
  match r.get key with
  -- All keys except `id` are optional, including ports.
  | none => return none
  -- A port is a big endian integer, and EIP-778 states no size.
  --
  -- EthLib reads an RLP scalar below 2^16: no leading zero byte, and zero is the empty string.
  | some value => some <$> (Codec.ofItem value).mapError fun _ => .invalidPort key value

/-- The IPv4 and IPv6 endpoints of a record, each absent when its address is.

It does not check the signature. -/
def Enr.endpoints (r : Enr) : Except EnrError (Option (Endpoint 4) × Option (Endpoint 16)) := do
  -- EthLib reads all eight keys first.
  --
  -- So a malformed value fails even when its address is absent.
  let ip ← readAddress r KEY_IP 4
  let ip6 ← readAddress r KEY_IP6 16
  let tcp ← readPort r KEY_TCP
  let tcp6 ← readPort r KEY_TCP6
  let udp ← readPort r KEY_UDP
  let udp6 ← readPort r KEY_UDP6
  let quic ← readPort r KEY_QUIC
  let quic6 ← readPort r KEY_QUIC6
  -- If no `tcp6` / `udp6` port is provided, the `tcp` / `udp` port applies to both IP addresses.
  --
  -- No source gives `quic` that rule, so an IPv6 endpoint without `quic6` has no QUIC port.
  return (ip.map (⟨·, tcp, udp, quic⟩), ip6.map (⟨·, tcp6 <|> tcp, udp6 <|> udp, quic6⟩))

/-- The IPv6 endpoint as a reader sees it, next to an IPv4 endpoint.

A TCP or UDP port that it lacks is the one of the IPv4 endpoint. -/
def Endpoint.inherit (e6 : Endpoint 16) (e4 : Option (Endpoint 4)) : Endpoint 16 :=
  -- If no `tcp6` / `udp6` port is provided, the `tcp` / `udp` port applies to both IP addresses.
  --
  -- The QUIC port is not inherited, as no source gives `quic` that rule.
  { e6 with tcp := e6.tcp <|> e4.bind (·.tcp), udp := e6.udp <|> e4.bind (·.udp) }

/-- An IPv6 port to write: none when it equals the IPv4 port, which then applies to both.

The source is the paragraph after the key table of [EIP-778].

[EIP-778]: https://github.com/ethereum/EIPs/blob/46976b2a9bf99f727fb87dc8c809e3a3cdc6b445/EIPS/eip-778.md#L64-L66
-/
def ipv6Port (port6 port : Option UInt16) : Option UInt16 :=
  -- Declaring the same port number in both `tcp`, `tcp6` or `udp`, `udp6` should be avoided.
  --
  -- The IPv4 port applies to both addresses when the IPv6 key is absent, so none is written.
  if port6 = port then none else port6

/-- The pairs of an IPv4 and an IPv6 endpoint, in key order, to put in a new record.

Other entries fall between these keys, so a caller merges them in key order. -/
def endpointPairs (e4 : Option (Endpoint 4)) (e6 : Option (Endpoint 16)) :
    List (ByteArray × Item) :=
  let tcp := e4.bind (·.tcp)
  let udp := e4.bind (·.udp)
  -- The pairs must be sorted by key: `ip < ip6 < quic < quic6 < tcp < tcp6 < udp < udp6`.
  --
  -- An IPv6 TCP or UDP port equal to the IPv4 one is not written again.
  [(KEY_IP, (e4.map (·.ip)).map Codec.toItem),
    (KEY_IP6, (e6.map (·.ip)).map Codec.toItem),
    (KEY_QUIC, (e4.bind (·.quic)).map Codec.toItem),
    (KEY_QUIC6, (e6.bind (·.quic)).map Codec.toItem),
    (KEY_TCP, tcp.map Codec.toItem),
    (KEY_TCP6, (ipv6Port (e6.bind (·.tcp)) tcp).map Codec.toItem),
    (KEY_UDP, udp.map Codec.toItem),
    (KEY_UDP6, (ipv6Port (e6.bind (·.udp)) udp).map Codec.toItem)].filterMap
    -- All keys except `id` are optional, so an absent value writes no pair.
    fun (key, value) => value.map (key, ·)

end EthLib.Networking.Enr
