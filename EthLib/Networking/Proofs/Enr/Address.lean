module

public import EthLib.Networking.Enr.Address
public import EthLib.Networking.Proofs.Enr.V4
public import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the addresses and ports of a node record

A record built from the pairs of two endpoints reads them back.

The IPv6 endpoint reads back with the TCP and UDP ports that it inherits from the IPv4 one.

The format cannot say that only the IPv4 address has a port, so that is the most it can give.

When `tcp6` or `udp6` is absent, the IPv6 port is the value of `tcp` or `udp`.

When `quic6` is absent, the IPv6 endpoint has no QUIC port, whatever `quic` holds.
-/

@[expose] public section

namespace EthLib.Networking.Enr

open EthLib.Cryptography.Secp256k1
open EthLib.Serialization.Rlp

/-! ## Reading one entry -/

/-- The address of a key is the value that the record holds there, written as an address. -/
theorem readAddress_of_get {r : Enr} {key : ByteArray} {size : Nat}
    {v : Option (Vector UInt8 size)} (h : r.get key = v.map Codec.toItem) :
    readAddress r key size = .ok v := by
  cases v <;> simp [readAddress, h, LawfulCodec.ofItem_toItem, Except.mapError, pure,
    Except.pure, Functor.map, Except.map]

/-- The port of a key is the value that the record holds there, written as a port. -/
theorem readPort_of_get {r : Enr} {key : ByteArray} {v : Option UInt16}
    (h : r.get key = v.map Codec.toItem) : readPort r key = .ok v := by
  cases v <;> simp [readPort, h, LawfulCodec.ofItem_toItem, Except.mapError, pure,
    Except.pure, Functor.map, Except.map]

/-! ## The pairs of two endpoints -/

/-- The pair of a key and an optional value, or no pair. -/
theorem filterMap_cons {key : ByteArray} {v : Option Item}
    (rest : List (ByteArray × Option Item)) :
    ((key, v) :: rest).filterMap (fun (k, w) => w.map (k, ·)) =
      v.toList.map (key, ·) ++ rest.filterMap (fun (k, w) => w.map (k, ·)) := by
  cases v <;> rfl

/-- The first value of a key among the pairs that an optional value writes, if any. -/
theorem find?_optional {key k : ByteArray} {v : Option Item} :
    ((v.toList.map (k, ·)).find? (·.1 = key)).map (·.2) = if k = key then v else none := by
  cases v <;> by_cases h : k = key <;> simp [h]

/-- The value that the pairs of two endpoints hold under a key, one candidate per address key. -/
theorem find?_endpointPairs (e4 : Option (Endpoint 4)) (e6 : Option (Endpoint 16))
    (key : ByteArray) :
    ((endpointPairs e4 e6).find? (·.1 = key)).map (·.2) =
      (if KEY_IP = key then (e4.map (·.ip)).map Codec.toItem else none).or
      ((if KEY_IP6 = key then (e6.map (·.ip)).map Codec.toItem else none).or
      ((if KEY_QUIC = key then (e4.bind (·.quic)).map Codec.toItem else none).or
      ((if KEY_QUIC6 = key then (e6.bind (·.quic)).map Codec.toItem else none).or
      ((if KEY_TCP = key then (e4.bind (·.tcp)).map Codec.toItem else none).or
      ((if KEY_TCP6 = key then
        (ipv6Port (e6.bind (·.tcp)) (e4.bind (·.tcp))).map Codec.toItem else none).or
      ((if KEY_UDP = key then (e4.bind (·.udp)).map Codec.toItem else none).or
      (if KEY_UDP6 = key then
        (ipv6Port (e6.bind (·.udp)) (e4.bind (·.udp))).map Codec.toItem else none))))))) := by
  simp only [endpointPairs, filterMap_cons, List.filterMap_nil, List.append_nil,
    List.find?_append, Option.map_or, find?_optional]

/-- Leaving out an IPv6 port equal to the IPv4 one changes nothing for a reader. -/
theorem ipv6Port_orElse (port6 port : Option UInt16) :
    (ipv6Port port6 port <|> port) = (port6 <|> port) := by
  unfold ipv6Port
  split
  · subst port6
    cases port <;> rfl
  · rfl

/-- A record built from the pairs of two endpoints reads them back.

The IPv6 endpoint comes back with the TCP and UDP ports of the IPv4 endpoint where it has none. -/
theorem endpoints_endpointPairs {sk : Fn} {seq : UInt64} {e4 : Option (Endpoint 4)}
    {e6 : Option (Endpoint 16)} {r : Enr} (h : makeRecordV4 sk seq (endpointPairs e4 e6) = .ok r) :
    r.endpoints = .ok (e4, e6.map (·.inherit e4)) := by
  -- Each address key reads its value from the pairs, since the builder's keys are other keys.
  have get (key : ByteArray) (hid : KEY_ID ≠ key) (hsk : KEY_SECP256K1 ≠ key) :=
    (get_of_makeRecordV4 h hid hsk).trans (find?_endpointPairs e4 e6 key)
  -- The key comparisons are between byte literals, which `decide` settles.
  have gip := get KEY_IP (by decide) (by decide)
  have gip6 := get KEY_IP6 (by decide) (by decide)
  have gtcp := get KEY_TCP (by decide) (by decide)
  have gtcp6 := get KEY_TCP6 (by decide) (by decide)
  have gudp := get KEY_UDP (by decide) (by decide)
  have gudp6 := get KEY_UDP6 (by decide) (by decide)
  have gquic := get KEY_QUIC (by decide) (by decide)
  have gquic6 := get KEY_QUIC6 (by decide) (by decide)
  simp +decide only [↓reduceIte, Option.or_none, Option.none_or] at gip gip6 gtcp gtcp6
  simp +decide only [↓reduceIte, Option.or_none, Option.none_or] at gudp gudp6 gquic gquic6
  have hip := readAddress_of_get gip
  have hip6 := readAddress_of_get gip6
  have htcp := readPort_of_get gtcp
  have htcp6 := readPort_of_get gtcp6
  have hudp := readPort_of_get gudp
  have hudp6 := readPort_of_get gudp6
  have hquic := readPort_of_get gquic
  have hquic6 := readPort_of_get gquic6
  simp only [Enr.endpoints, hip, hip6, htcp, htcp6, hudp, hudp6, hquic, hquic6, bind,
    Except.bind, pure, Except.pure, Except.ok.injEq, ipv6Port_orElse]
  cases e4 <;> cases e6 <;> rfl

/-! ## The fallback to the IPv4 ports -/

/-- The endpoints of a record are built from the values of its eight keys. -/
theorem endpoints_eq_ok {r : Enr} {e4 : Option (Endpoint 4)} {e6 : Option (Endpoint 16)}
    (h : r.endpoints = .ok (e4, e6)) :
    ∃ ip ip6 tcp tcp6 udp udp6 quic quic6,
      readAddress r KEY_IP 4 = .ok ip ∧ readAddress r KEY_IP6 16 = .ok ip6 ∧
      readPort r KEY_TCP = .ok tcp ∧ readPort r KEY_TCP6 = .ok tcp6 ∧
      readPort r KEY_UDP = .ok udp ∧ readPort r KEY_UDP6 = .ok udp6 ∧
      readPort r KEY_QUIC = .ok quic ∧ readPort r KEY_QUIC6 = .ok quic6 ∧
      e4 = ip.map (⟨·, tcp, udp, quic⟩) ∧
      e6 = ip6.map (⟨·, tcp6 <|> tcp, udp6 <|> udp, quic6⟩) := by
  simp only [Enr.endpoints, EthLib.Base.bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  obtain ⟨ip, hip, ip6, hip6, tcp, htcp, tcp6, htcp6, udp, hudp, udp6, hudp6, quic, hquic,
    quic6, hquic6, h4, h6⟩ := h
  exact ⟨ip, ip6, tcp, tcp6, udp, udp6, quic, quic6, hip, hip6, htcp, htcp6, hudp, hudp6, hquic,
    hquic6, h4.symm, h6.symm⟩

/-- A key that the record does not hold reads as no port. -/
theorem readPort_of_get_none {r : Enr} {key : ByteArray} (h : r.get key = none) :
    readPort r key = .ok none :=
  readPort_of_get (v := none) h

/-- Without `tcp6`, the TCP port of the IPv6 endpoint is what `tcp` holds. -/
theorem readPort_tcp_of_endpoints {r : Enr} {e4 : Option (Endpoint 4)} {e6 : Endpoint 16}
    (h : r.endpoints = .ok (e4, some e6)) (h6 : r.get KEY_TCP6 = none) :
    readPort r KEY_TCP = .ok e6.tcp := by
  obtain ⟨_, ip6, tcp, tcp6, _, _, _, _, _, _, htcp, htcp6, _, _, _, _, _, he6⟩ :=
    endpoints_eq_ok h
  rw [readPort_of_get_none h6, Except.ok.injEq] at htcp6
  subst htcp6
  cases ip6 with
  | none => cases he6
  | some _ =>
    cases he6
    exact htcp

/-- Without `udp6`, the UDP port of the IPv6 endpoint is what `udp` holds. -/
theorem readPort_udp_of_endpoints {r : Enr} {e4 : Option (Endpoint 4)} {e6 : Endpoint 16}
    (h : r.endpoints = .ok (e4, some e6)) (h6 : r.get KEY_UDP6 = none) :
    readPort r KEY_UDP = .ok e6.udp := by
  obtain ⟨_, ip6, _, _, udp, udp6, _, _, _, _, _, _, hudp, hudp6, _, _, _, he6⟩ :=
    endpoints_eq_ok h
  rw [readPort_of_get_none h6, Except.ok.injEq] at hudp6
  subst hudp6
  cases ip6 with
  | none => cases he6
  | some _ =>
    cases he6
    exact hudp

/-- Without `quic6`, the IPv6 endpoint has no QUIC port, whatever `quic` holds. -/
theorem quic_of_endpoints {r : Enr} {e4 : Option (Endpoint 4)} {e6 : Endpoint 16}
    (h : r.endpoints = .ok (e4, some e6)) (h6 : r.get KEY_QUIC6 = none) : e6.quic = none := by
  obtain ⟨_, ip6, _, _, _, _, _, quic6, _, _, _, _, _, _, _, hquic6, _, he6⟩ :=
    endpoints_eq_ok h
  rw [readPort_of_get_none h6, Except.ok.injEq] at hquic6
  subst hquic6
  cases ip6 with
  | none => cases he6
  | some _ =>
    cases he6
    rfl

end EthLib.Networking.Enr
