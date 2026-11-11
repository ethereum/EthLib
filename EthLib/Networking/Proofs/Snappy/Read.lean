module

public import EthLib.Networking.Proofs.Snappy.Frame
public import EthLib.Networking.Proofs.Snappy.FrameEncode

/-!
# `Networking.Proofs.Snappy.Read`

Properties of the reader that stops a framed stream once it holds a given number of bytes.

The chunks it reads form a stream on their own, and that stream decodes to its output.

When those chunks hold the bytes it needs, bytes after them are left unread.

The encoders write a stream that the reader reads whole, with no bytes left after it.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Snappy.Read

open EthLib.Networking.Snappy
open EthLib.Networking.Proofs.Snappy.Frame
open EthLib.Base (bytesToUint uintToBytes)

/-! ## One chunk -/

/-- A chunk that decodes stops the reader when its output holds the bytes still needed.

Otherwise the reader goes on after it, for the bytes that remain. -/
theorem readChunks_chunk_ok {type : UInt8} {body out : List UInt8} (need : Nat)
    (rest : List UInt8) (fuel : Nat) (h : body.length < 2 ^ 24)
    (hc : decodeChunk type body = .ok out) :
    readChunks need (type :: (uintToBytes 3 body.length).toList ++ body ++ rest) (fuel + 1) =
      if need ≤ out.length then .ok (out, rest)
      else (readChunks (need - out.length) rest fuel).map
        fun read => (out ++ read.1, read.2) := by
  obtain ⟨a, b, c, habc, hv⟩ := uintToBytes_three h
  rw [habc]
  simp [readChunks, hv, hc, show ¬ body.length + rest.length < body.length by omega]

/-- A reader that succeeds with some fuel succeeds the same with more. -/
theorem readChunks_of_le {need f g : Nat} {bs : List UInt8} {r : List UInt8 × List UInt8}
    (h : readChunks need bs f = .ok r) (hfg : f ≤ g) : readChunks need bs g = .ok r := by
  induction f generalizing need bs r g with
  | zero =>
    match bs with
    | [] => cases g <;> simpa [readChunks] using h
    | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ => simp [readChunks] at h
  | succ f ih =>
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    match bs with
    | [] => simpa [readChunks] using h
    | [_] | [_, _] | [_, _, _] => simp [readChunks] at h
    | type :: l0 :: l1 :: l2 :: body =>
      by_cases hl : body.length < bytesToUint #v[l0, l1, l2]
      · simp [readChunks, hl] at h
      · cases hc : decodeChunk type (body.take (bytesToUint #v[l0, l1, l2])) with
        | error e => simp [readChunks, hl, hc] at h
        | ok o =>
          by_cases hn : need ≤ o.length
          · simpa [readChunks, hl, hc, hn] using h
          · cases hr : readChunks (need - o.length) (body.drop (bytesToUint #v[l0, l1, l2]))
                f with
            | error e => simp [readChunks, hl, hc, hn, hr, Except.map] at h
            | ok v =>
              simp only [readChunks, hl, hc, hn, hr, ite_false] at h ⊢
              rw [ih hr (by omega)]
              exact h

/-! ## The chunks read form a stream -/

/-- The reader reads a run of whole chunks, which decodes to its output, and leaves the rest. -/
theorem readChunks_sound {need fuel : Nat} {bs out rest : List UInt8}
    (h : readChunks need bs fuel = .ok (out, rest)) :
    ∃ read, bs = read ++ rest ∧ decodeChunks read fuel = .ok out := by
  induction fuel generalizing need bs out rest with
  | zero =>
    match bs with
    | [] =>
      simp only [readChunks, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, by simp [decodeChunks]⟩
    | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ => simp [readChunks] at h
  | succ fuel ih =>
    match bs with
    | [] =>
      simp only [readChunks, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], rfl, by simp [decodeChunks]⟩
    | [_] | [_, _] | [_, _, _] => simp [readChunks] at h
    | type :: l0 :: l1 :: l2 :: body =>
      by_cases hl : body.length < bytesToUint #v[l0, l1, l2]
      · simp [readChunks, hl] at h
      · cases hc : decodeChunk type (body.take (bytesToUint #v[l0, l1, l2])) with
        | error e => simp [readChunks, hl, hc] at h
        | ok o =>
          by_cases hn : need ≤ o.length
          · simp only [readChunks, hl, hc, hn, ite_false, ite_true, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨type :: l0 :: l1 :: l2 :: body.take (bytesToUint #v[l0, l1, l2]), ?_, ?_⟩
            · simp
            · have hlen : (body.take (bytesToUint #v[l0, l1, l2])).length =
                  bytesToUint #v[l0, l1, l2] := List.length_take_of_le (by omega)
              simp [decodeChunks, hlen, hc, List.take_of_length_le, Except.map]
          · cases hr : readChunks (need - o.length) (body.drop (bytesToUint #v[l0, l1, l2]))
                fuel with
            | error e => simp [readChunks, hl, hc, hn, hr, Except.map] at h
            | ok r =>
              simp only [readChunks, hl, hc, hn, hr, ite_false, Except.map, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨read, hread, hdec⟩ := ih hr
              refine ⟨type :: l0 :: l1 :: l2 ::
                (body.take (bytesToUint #v[l0, l1, l2]) ++ read), ?_, ?_⟩
              · have hb : body = body.take (bytesToUint #v[l0, l1, l2]) ++ (read ++ r.2) := by
                  rw [← hread, List.take_append_drop]
                simp only [List.cons_append, List.append_assoc]
                rw [← hb]
              · have hlen : (body.take (bytesToUint #v[l0, l1, l2])).length =
                    bytesToUint #v[l0, l1, l2] := List.length_take_of_le (by omega)
                have htake : (body.take (bytesToUint #v[l0, l1, l2]) ++ read).take
                    (bytesToUint #v[l0, l1, l2]) = body.take (bytesToUint #v[l0, l1, l2]) :=
                  List.take_left' hlen
                have hdrop : (body.take (bytesToUint #v[l0, l1, l2]) ++ read).drop
                    (bytesToUint #v[l0, l1, l2]) = read := List.drop_left' hlen
                have hl' : ¬ (body.take (bytesToUint #v[l0, l1, l2]) ++ read).length <
                    bytesToUint #v[l0, l1, l2] := by
                  simp only [List.length_append, hlen]
                  omega
                simp only [decodeChunks, hl', ite_false, htake, hc, hdrop, hdec, Except.map]

/-- A stream that the reader reads whole decodes to the reader's output. -/
theorem decodeFramesList_of_readFrames {n : Nat} {bs out : List UInt8}
    (h : readFrames n bs = .ok (out, [])) : decodeFramesList bs = .ok out := by
  match bs with
  | [] => simp [readFrames] at h
  | type :: tail =>
    simp only [readFrames] at h
    split at h
    · rename_i htype
      obtain ⟨read, hread, hdec⟩ := readChunks_sound h
      rw [List.append_nil] at hread
      subst hread
      simp only [decodeFramesList, htype, ite_true]
      exact hdec
    · simp at h

/-! ## Bytes after the chunks -/

/-- Chunks that hold the bytes the reader needs stop it, so bytes after them are left unread. -/
theorem readChunks_append {need fuel : Nat} {a b out : List UInt8} (ha : a ≠ [])
    (h : readChunks need a fuel = .ok (out, [])) (hn : need ≤ out.length) :
    readChunks need (a ++ b) fuel = .ok (out, b) := by
  induction fuel generalizing need a out with
  | zero =>
    match a with
    | [] => contradiction
    | [_] | [_, _] | [_, _, _] | _ :: _ :: _ :: _ :: _ => simp [readChunks] at h
  | succ fuel ih =>
    match a with
    | [] => contradiction
    | [_] | [_, _] | [_, _, _] => simp [readChunks] at h
    | type :: l0 :: l1 :: l2 :: body =>
      by_cases hl : body.length < bytesToUint #v[l0, l1, l2]
      · simp [readChunks, hl] at h
      · have hl' : ¬ (body ++ b).length < bytesToUint #v[l0, l1, l2] := by
          simp only [List.length_append]
          omega
        have htake : (body ++ b).take (bytesToUint #v[l0, l1, l2]) =
            body.take (bytesToUint #v[l0, l1, l2]) := List.take_append_of_le_length (by omega)
        have hdrop : (body ++ b).drop (bytesToUint #v[l0, l1, l2]) =
            body.drop (bytesToUint #v[l0, l1, l2]) ++ b :=
          List.drop_append_of_le_length (by omega)
        cases hc : decodeChunk type (body.take (bytesToUint #v[l0, l1, l2])) with
        | error e => simp [readChunks, hl, hc] at h
        | ok o =>
          by_cases hno : need ≤ o.length
          · simp only [readChunks, hl, hc, hno, ite_false, ite_true, Except.ok.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, hrest⟩ := h
            simp only [List.cons_append, readChunks, hl', ite_false, htake, hc, hno, ite_true,
              hdrop, hrest, List.nil_append]
          · cases hr : readChunks (need - o.length) (body.drop (bytesToUint #v[l0, l1, l2]))
                fuel with
            | error e => simp [readChunks, hl, hc, hno, hr, Except.map] at h
            | ok r =>
              obtain ⟨o', r'⟩ := r
              simp only [readChunks, hl, hc, hno, hr, ite_false, Except.map, Except.ok.injEq,
                Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              simp only [List.length_append] at hn
              -- The chunks after the first one hold the bytes still needed, so there are some.
              have hne : body.drop (bytesToUint #v[l0, l1, l2]) ≠ [] := by
                intro hnil
                rw [hnil] at hr
                cases fuel <;>
                · simp only [readChunks, Except.ok.injEq, Prod.mk.injEq] at hr
                  obtain ⟨rfl, -⟩ := hr
                  simp only [List.length_nil, Nat.add_zero] at hn
                  omega
              have := ih hne hr (by omega)
              simp only [List.cons_append, readChunks, hl', ite_false, htake, hc, hno, hdrop,
                this, Except.map]

/-- A stream that the reader reads whole, with the bytes it needs, leaves the bytes after it. -/
theorem readFrames_append {n : Nat} {a b out : List UInt8}
    (h : readFrames n a = .ok (out, [])) (hn : n ≤ out.length) :
    readFrames n (a ++ b) = .ok (out, b) := by
  match a with
  | [] => simp [readFrames] at h
  | type :: tail =>
    simp only [readFrames] at h
    split at h
    · rename_i htype
      have happ := readChunks_append (b := b) (List.cons_ne_nil _ _) h hn
      simp only [List.cons_append, readFrames, htype, ite_true]
      -- The longer stream gives the reader more fuel than it needs.
      exact readChunks_of_le happ (by simp)
    · simp at h

/-! ## The encoders -/

/-- The encoder writes no chunk for no data. -/
theorem encodeChunks_nil (chunk : List UInt8 → List UInt8) (n : Nat) :
    encodeChunks chunk [] n = [] := by
  cases n <;> rfl

/-- The reader reads the chunks of the encoder whole, when both fuels are large enough.

The encoder needs at least the data length, and the reader at least the length it writes.

The chunk of each piece of at most 65536 bytes must be a header and a body that decodes to it. -/
theorem readChunks_encodeChunks {chunk : List UInt8 → List UInt8}
    (hchunk : ∀ piece : List UInt8, piece.length ≤ maxChunkLength →
      ∃ (type : UInt8) (body : List UInt8), body.length < 2 ^ 24 ∧
        chunk piece = type :: (uintToBytes 3 body.length).toList ++ body ∧
        decodeChunk type body = .ok piece)
    (data : List UInt8) {n fuel : Nat}
    (hn : data.length ≤ n) (hfuel : (encodeChunks chunk data n).length ≤ fuel) :
    readChunks data.length (encodeChunks chunk data n) fuel = .ok (data, []) := by
  induction n generalizing data fuel with
  | zero =>
      cases data with
      | nil => cases fuel <;> rfl
      | cons _ _ => simp at hn
  | succ n ih =>
      cases data with
      | nil => cases fuel <;> rfl
      | cons b bs =>
          -- One chunk of the first 65536 bytes, then the rest.
          let piece := (b :: bs).take maxChunkLength
          let tail := encodeChunks chunk ((b :: bs).drop maxChunkLength) n
          have henc : encodeChunks chunk (b :: bs) (n + 1) = chunk piece ++ tail := rfl
          obtain ⟨type, body, hbl, hdc, hdec⟩ := hchunk piece (List.length_take_le _ _)
          rw [henc, hdc] at hfuel ⊢
          simp only [List.length_append, List.length_cons, Vector.length_toList] at hfuel
          obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          rw [readChunks_chunk_ok _ tail fuel hbl hdec]
          have hpl : piece.length = min maxChunkLength (bs.length + 1) := by
            simp [piece, List.length_take]
          by_cases hle : (b :: bs).length ≤ piece.length
          · -- The first chunk holds all the data, and no chunk follows it.
            have hshort : (b :: bs).length ≤ maxChunkLength := by
              simp only [List.length_cons] at hle ⊢
              omega
            have hpiece : piece = b :: bs := List.take_of_length_le hshort
            have htail : tail = [] := by
              simp only [tail, List.drop_eq_nil_of_le hshort, encodeChunks_nil]
            rw [hpiece, htail]
            simp
          · -- The first chunk holds 65536 bytes, and the reader goes on for the rest.
            simp only [hle, ↓reduceIte]
            have hrest : (b :: bs).length - piece.length =
                ((b :: bs).drop maxChunkLength).length := by
              simp only [List.length_drop, List.length_cons] at hpl hle ⊢
              omega
            have hdrop : ((b :: bs).drop maxChunkLength).length ≤ n := by
              simp only [List.length_drop, List.length_cons, maxChunkLength] at hn ⊢
              omega
            rw [hrest, ih _ hdrop (show tail.length ≤ fuel by omega)]
            simp [Except.map, piece]

/-- The reader reads a stream of the encoder whole: the identifier, then the chunks of the data.
-/
theorem readFrames_streamIdentifier_encodeChunks {chunk : List UInt8 → List UInt8}
    (hchunk : ∀ piece : List UInt8, piece.length ≤ maxChunkLength →
      ∃ (type : UInt8) (body : List UInt8), body.length < 2 ^ 24 ∧
        chunk piece = type :: (uintToBytes 3 body.length).toList ++ body ∧
        decodeChunk type body = .ok piece)
    (data : List UInt8) {n : Nat} (hn : data.length ≤ n) :
    readFrames data.length (streamIdentifier ++ encodeChunks chunk data n) =
      .ok (data, []) := by
  have hid : streamIdentifier ++ encodeChunks chunk data n =
      streamIdentifierType :: (uintToBytes 3 (streamIdentifier.drop 4).length).toList ++
        streamIdentifier.drop 4 ++ encodeChunks chunk data n := rfl
  have hc : decodeChunk streamIdentifierType (streamIdentifier.drop 4) = .ok [] := rfl
  -- The stream starts with the identifier, so the reader reads chunks, with its length as fuel.
  have hstart : readFrames data.length (streamIdentifier ++ encodeChunks chunk data n) =
      readChunks data.length (streamIdentifier ++ encodeChunks chunk data n)
        ((encodeChunks chunk data n).length + 9 + 1) := by
    have hcons : streamIdentifier ++ encodeChunks chunk data n =
        streamIdentifierType :: (streamIdentifier.drop 1 ++ encodeChunks chunk data n) := rfl
    rw [hcons]
    simp [readFrames, streamIdentifier]
  rw [hstart, hid, readChunks_chunk_ok _ _ _ (by decide) hc]
  by_cases h0 : data.length ≤ ([] : List UInt8).length
  · -- No data: the stream is the identifier alone.
    have hnil : data = [] := List.eq_nil_of_length_eq_zero (by simpa using h0)
    subst hnil
    simp [encodeChunks_nil]
  · have hread := readChunks_encodeChunks hchunk data hn
      (Nat.le_add_right (encodeChunks chunk data n).length 9)
    simp only [List.length_nil] at h0
    simp only [List.length_nil, Nat.sub_zero, h0, ↓reduceIte, hread]
    rfl

/-- The reader reads a stream of the literal encoder whole. -/
theorem readFrames_encodeFramesLiteral (d : ByteArray) :
    readFrames d.size (encodeFramesLiteral d).data.toList = .ok (d.data.toList, []) := by
  have hs : d.size = d.data.toList.length := Array.length_toList.symm
  simp only [encodeFramesLiteral, List.toList_toArray]
  rw [hs]
  exact readFrames_streamIdentifier_encodeChunks (fun _ h => uncompressedChunk_spec h) _
    (Nat.le_of_eq hs.symm)

/-- The reader reads a stream of the encoder that compresses whole. -/
theorem readFrames_encodeFrames (d : ByteArray) :
    readFrames d.size (encodeFrames d).data.toList = .ok (d.data.toList, []) := by
  have hs : d.size = d.data.toList.length := Array.length_toList.symm
  simp only [encodeFrames, List.toList_toArray]
  rw [hs]
  exact readFrames_streamIdentifier_encodeChunks
    (fun _ h => Proofs.Snappy.FrameEncode.dataChunk_spec h) _ (Nat.le_of_eq hs.symm)

end EthLib.Networking.Proofs.Snappy.Read
