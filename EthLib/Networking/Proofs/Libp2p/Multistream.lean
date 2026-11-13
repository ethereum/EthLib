module

public import EthLib.Networking.Libp2p.Multistream
public import EthLib.Networking.Proofs.Encoding.Uvarint

/-!
# Proofs: multistream-select messages

- Decoding reads back a message from its encoding, whatever bytes follow it.
- The decoder accepts only these encodings, so each message has exactly one.
- A peer echoes a proposal it supports, and answers `na` to any other.
- Two peers agree on the first proposal that the listener supports, and on nothing if there is none.
- That needs `na` outside the proposals, since the dialer could not tell it from a refusal.
- Two errors with one code come from one constructor.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Libp2p.Multistream

open EthLib.Networking.Encoding
open EthLib.Networking.Libp2p.Multistream

/-- Decoding the encoding of a message, then any bytes, returns the message and those bytes.

The message and its newline must be shorter than `2^63` bytes. -/
theorem decode_encode (message : ByteArray) (h : message.size + 1 < Uvarint.bound)
    (rest : List UInt8) : decode (encode message ++ rest) = .ok (message, rest) := by
  obtain ⟨⟨bs⟩⟩ := message
  have hlen : (ByteArray.mk ⟨bs⟩).size = bs.length := by simp [ByteArray.size]
  have hass : encode ⟨⟨bs⟩⟩ ++ rest =
      Uvarint.encode (bs.length + 1) ++ (bs ++ newline :: rest) := by
    simp [encode, hlen]
  rw [hass]
  rw [hlen] at h
  simp only [decode]
  rw [EthLib.Networking.Proofs.Encoding.Uvarint.decode_encode h]
  have h1 : (bs ++ newline :: rest).take (bs.length + 1) = bs ++ [newline] := by
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have h2 : (bs ++ newline :: rest).drop (bs.length + 1) = rest := by
    rw [List.drop_append]
    simp
  simp [h1, h2, bind, Except.bind, Except.mapError]
  rfl

/-- A decoded message and its newline are shorter than `2^63` bytes.

The input is the encoding of that message, then the rest. -/
theorem encode_decode {bytes rest : List UInt8} {message : ByteArray}
    (h : decode bytes = .ok (message, rest)) :
    message.size + 1 < Uvarint.bound ∧ encode message ++ rest = bytes := by
  simp only [decode] at h
  cases hd : Uvarint.decode bytes with
  | error e => simp [hd, bind, Except.bind, Except.mapError] at h
  | ok p =>
      obtain ⟨L, r0⟩ := p
      obtain ⟨hL, hb⟩ := EthLib.Networking.Proofs.Encoding.Uvarint.encode_decode hd
      simp only [hd, bind, Except.bind, Except.mapError] at h
      generalize hbody : r0.take L = body at h
      by_cases h0 : L = 0
      · simp [h0, throw, throwThe, MonadExceptOf.throw] at h
      by_cases h1 : body.length < L
      · simp [h0, h1, throw, throwThe, MonadExceptOf.throw] at h
      by_cases h2 : body[L - 1]? = some newline
      · simp only [h0, h1, h2, ne_eq, not_true_eq_false, ite_false] at h
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hlen : body.length = L := by
          have : body.length ≤ L := by rw [← hbody]; simp; omega
          omega
        have hsz : (⟨(body.take (L - 1)).toArray⟩ : ByteArray).size = L - 1 := by
          simp [ByteArray.size]; omega
        have hi : L - 1 < body.length := by omega
        have hg : body[L - 1] = newline := by simpa [hi] using h2
        have hdrop : body.drop (L - 1) = [newline] := by
          rw [List.drop_eq_getElem_cons hi, hg, List.drop_of_length_le (by omega)]
        have hr0 : body.take (L - 1) ++ newline :: r0.drop L = r0 := by
          calc body.take (L - 1) ++ newline :: r0.drop L
              = body.take (L - 1) ++ body.drop (L - 1) ++ r0.drop L := by
                rw [hdrop]; simp
            _ = r0 := by rw [List.take_append_drop, ← hbody, List.take_append_drop]
        refine ⟨by omega, ?_⟩
        rw [← hb]
        have hL' : L - 1 + 1 = L := by omega
        simp only [encode, hsz, hL', List.append_assoc, List.singleton_append]
        rw [hr0]
      · simp [h0, h1, h2, throw, throwThe, MonadExceptOf.throw] at h

/-- The decoder accepts exactly the encodings of messages that fit, then any bytes. -/
theorem decode_eq_ok_iff {bytes rest : List UInt8} {message : ByteArray} :
    decode bytes = .ok (message, rest) ↔
      message.size + 1 < Uvarint.bound ∧ encode message ++ rest = bytes :=
  ⟨encode_decode, fun ⟨hn, he⟩ => he ▸ decode_encode message hn rest⟩

/-- A peer echoes a proposal it supports. -/
theorem respond_of_mem {supported : List ByteArray} {proposal : ByteArray}
    (h : proposal ∈ supported) : respond supported proposal = proposal := by
  simp only [respond, List.mem_map]
  exact ite_eq_left ⟨proposal, h, rfl⟩

/-- A peer answers `na` to a proposal it does not support. -/
theorem respond_of_not_mem {supported : List ByteArray} {proposal : ByteArray}
    (h : proposal ∉ supported) : respond supported proposal = notAvailable := by
  simp only [respond, List.mem_map]
  refine ite_eq_right ?_
  rintro ⟨p, hp, he⟩
  exact h (ByteArray.ext he ▸ hp)

/-- A protocol is supported exactly when it is in the list. -/
theorem supports_iff {supported : List ByteArray} {protocol : ByteArray} :
    supports supported protocol = true ↔ protocol ∈ supported := by
  simp only [supports, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, he⟩
    exact ByteArray.ext he ▸ hp
  · intro h
    exact ⟨protocol, h, rfl⟩

/-- A listener that waits for a proposal agrees on one it supports, and echoes it. -/
theorem listen_of_mem {supported : List ByteArray} {proposal : ByteArray}
    (h : proposal ∈ supported) :
    listen (.awaitProposal supported) proposal = (.agreed proposal, [proposal]) := by
  simp [listen, supports_iff.2 h]

/-- A listener that waits for a proposal answers `na` to one it does not support, and waits on. -/
theorem listen_of_not_mem {supported : List ByteArray} {proposal : ByteArray}
    (h : proposal ∉ supported) :
    listen (.awaitProposal supported) proposal =
      (.awaitProposal supported, [notAvailable]) := by
  have : supports supported proposal = false := by
    cases hs : supports supported proposal
    · rfl
    · exact absurd (supports_iff.1 hs) h
  simp [listen, this]

/-- The exchange after the listener read a proposal, by induction over the proposals left. -/
private theorem exchange_aux (S : List ByteArray) :
    ∀ (rest : List ByteArray) (p : ByteArray) (fuel : Nat),
      notAvailable ∉ p :: rest → 2 * rest.length + 1 ≤ fuel →
      exchange fuel (.awaitAnswer p rest) (listen (.awaitProposal S) p).1 []
          (listen (.awaitProposal S) p).2 =
        match (p :: rest).find? (supports S) with
        | some q => (.agreed q, .agreed q)
        | none => (.failed, .awaitProposal S) := by
  intro rest
  induction rest with
  | nil =>
    intro p fuel hna hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    by_cases h : p ∈ S
    · rw [listen_of_mem h]
      have hs := supports_iff.2 h
      cases k <;> simp [exchange, dial, hs]
    · rw [listen_of_not_mem h]
      have hs : supports S p = false := by
        cases hs : supports S p
        · rfl
        · exact absurd (supports_iff.1 hs) h
      have hp : p ≠ notAvailable := fun e => hna (by simp [e])
      cases k <;> simp [exchange, dial, hs, hp.symm]
  | cons r rs ih =>
    intro p fuel hna hf
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    have hp : p ≠ notAvailable := fun e => hna (by simp [e])
    by_cases h : p ∈ S
    · rw [listen_of_mem h]
      have hs := supports_iff.2 h
      cases k <;> simp [exchange, dial, hs]
    · rw [listen_of_not_mem h]
      have hs : supports S p = false := by
        cases hs : supports S p
        · rfl
        · exact absurd (supports_iff.1 hs) h
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hf; omega⟩
      have hna' : notAvailable ∉ r :: rs := fun e => hna (List.mem_cons_of_mem _ e)
      have := ih r k' hna' (by simp at hf; omega)
      simp only [exchange, dial, hp.symm, ↓reduceIte, List.nil_append] at this ⊢
      simp [hs, List.find?_cons, this]

/-- The run with at least one proposal, in terms of the first proposal the listener supports. -/
private theorem run_cons (p : ByteArray) (rest supported : List ByteArray)
    (hna : notAvailable ∉ p :: rest) :
    run (p :: rest) supported =
      match (p :: rest).find? (supports supported) with
      | some q => (.agreed q, .agreed q)
      | none => (.failed, .awaitProposal supported) := by
  rw [← exchange_aux supported rest p (2 * rest.length + 1) hna (Nat.le_refl _)]
  have hf : 2 * (p :: rest).length + 2 = (2 * rest.length + 1) + 1 + 1 + 1 := by
    simp; omega
  simp only [run, Dialer.start, Listener.start, hf, exchange, listen, dial,
    List.append_nil, List.nil_append, List.cons_append, ↓reduceIte]

/-- A listener that waits for a proposal sends the answer of a peer to it, once. -/
theorem listen_awaitProposal_reply (supported : List ByteArray) (proposal : ByteArray) :
    (listen (.awaitProposal supported) proposal).2 = [respond supported proposal] := by
  by_cases h : proposal ∈ supported
  · rw [listen_of_mem h, respond_of_mem h]
  · rw [listen_of_not_mem h, respond_of_not_mem h]

/-- When the listener supports some proposal, both peers agree on the first one.

No proposal may be `na`. -/
theorem run_of_find_some {proposals supported : List ByteArray} {protocol : ByteArray}
    (hna : notAvailable ∉ proposals)
    (h : proposals.find? (supports supported) = some protocol) :
    run proposals supported = (.agreed protocol, .agreed protocol) := by
  cases proposals with
  | nil => simp at h
  | cons p rest => rw [run_cons p rest supported hna]; simp [h]

/-- When the listener supports no proposal, the dialer fails and the listener waits on.

There is at least one proposal, and none is `na`. -/
theorem run_of_find_none {proposals supported : List ByteArray}
    (hne : proposals ≠ []) (hna : notAvailable ∉ proposals)
    (h : proposals.find? (supports supported) = none) :
    run proposals supported = (.failed, .awaitProposal supported) := by
  cases proposals with
  | nil => exact absurd rfl hne
  | cons p rest => rw [run_cons p rest supported hna]; simp [h]

/-- The agreed protocol is the first proposal that the listener supports.

No proposal may be `na`. -/
theorem negotiate_eq_find {proposals supported : List ByteArray}
    (hna : notAvailable ∉ proposals) :
    negotiate proposals supported = proposals.find? (supports supported) := by
  cases proposals with
  | nil => simp [negotiate, run, Dialer.start, Listener.start, exchange, dial]
  | cons p rest =>
    simp only [negotiate, run_cons p rest supported hna]
    cases (p :: rest).find? (supports supported) <;> rfl

/-- When the dialer agrees on a protocol, the listener agrees on it too.

No proposal may be `na`. -/
theorem negotiate_agree {proposals supported : List ByteArray} {protocol : ByteArray}
    (hna : notAvailable ∉ proposals) (h : negotiate proposals supported = some protocol) :
    run proposals supported = (.agreed protocol, .agreed protocol) := by
  rw [negotiate_eq_find hna] at h
  exact run_of_find_some hna h

/-- The peers agree on nothing exactly when the listener supports no proposal.

No proposal may be `na`. -/
theorem negotiate_eq_none_iff {proposals supported : List ByteArray}
    (hna : notAvailable ∉ proposals) :
    negotiate proposals supported = none ↔ ∀ p ∈ proposals, p ∉ supported := by
  rw [negotiate_eq_find hna, List.find?_eq_none]
  simp [supports_iff]

/-- Two errors with one code come from one constructor. -/
theorem _root_.EthLib.Networking.Libp2p.Multistream.MultistreamError.code_injective
    (e₁ e₂ : MultistreamError) (h : e₁.code = e₂.code) : e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [MultistreamError.code] at h; exact absurd h (by decide))

end EthLib.Networking.Proofs.Libp2p.Multistream
