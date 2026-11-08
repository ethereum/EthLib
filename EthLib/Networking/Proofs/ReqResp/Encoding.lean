module

public import EthLib.Networking.ReqResp.Encoding
public import EthLib.Networking.Proofs.Encoding.Varint
public import EthLib.Networking.Proofs.Snappy.Frame
public import EthLib.Networking.Proofs.Snappy.FrameEncode

/-!
# `Networking.Proofs.ReqResp.Encoding`

Properties of the `ssz_snappy` encoding of requests and responses.

A payload that decodes has its declared length, within both bounds.

The decoder accepts exactly the encoding of that length, then compressed bytes.

Those bytes are within the bound for that length, and they decompress to the payload.

More compressed bytes than the bound for the declared length reject the payload.

The literal encoder writes payloads and response chunks that decode back.

The encoder that compresses writes payloads that decode back.

Two errors with one code come from one constructor, and no error has code 0.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.ReqResp.Encoding

open EthLib.Networking.ReqResp
open EthLib.Networking.Encoding.Varint
open EthLib.Networking.Proofs.Encoding.Varint
open EthLib.Networking.Proofs

/-! ## The varint prefix -/

/-- The split finds the last byte of an encoding, whatever follows it. -/
theorem findIdx_encodeAux {n fuel m : Nat} (rest : List UInt8) (hf : 0 < fuel)
    (hn : n < groupSize ^ fuel) (hm : (encodeAux n fuel).length ≤ m) :
    ((encodeAux n fuel ++ rest).take m).findIdx (·.toNat < continuation) + 1 =
      (encodeAux n fuel).length := by
  induction fuel generalizing n m with
  | zero => omega
  | succ fuel ih =>
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by
      have := encodeAux_ne_nil (n := n) hf
      cases h : encodeAux n (fuel + 1) <;> simp_all; omega⟩
    by_cases hlt : n < groupSize
    · -- One byte, below 128.
      simp [encodeAux, hlt, toNat_terminator_byte hlt, List.findIdx_cons]
      rw [groupSize_eq, continuation_eq] at *
      omega
    · -- A continued byte, then the encoding of the rest.
      have hf' : 0 < fuel := by
        rcases fuel with _ | _
        · simp at hn; omega
        · omega
      have hn' : n / groupSize < groupSize ^ fuel := by
        rw [Nat.pow_succ] at hn
        exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      simp only [encodeAux, hlt, ite_false, List.cons_append, List.take_succ_cons,
        List.length_cons] at hm ⊢
      rw [List.findIdx_cons]
      have hc : ¬ (UInt8.ofNat (n % groupSize + continuation)).toNat < continuation := by
        rw [toNat_continued_byte]; omega
      have := ih hf' hn' (m := m) (by omega)
      simp only [hc, decide_false, Bool.false_eq_true, ite_false]
      omega

/-- The split of an encoded length followed by any bytes returns the encoding and those bytes. -/
theorem splitVarint_encode (v : UInt64) (rest : List UInt8) :
    splitVarint (encode v ++ rest) = (encode v, rest) := by
  have hlt : v.toNat < groupSize ^ maxLength := by
    have := v.toNat_lt_size
    simp only [UInt64.size, groupSize, payloadBits, maxLength] at *
    omega
  have h := findIdx_encodeAux rest (by decide) hlt (encode_length_le v)
  simp only [splitVarint]
  rw [show encodeAux v.toNat maxLength = encode v from rfl] at h
  rw [h]
  simp


/-! ## The bound on the compressed size -/

/-- Below 2^63, the bound `32 + n + n / 6` does not overflow. -/
theorem maxCompressedLen_eq {n : UInt64} (h : n.toNat < 2 ^ 63) :
    ∃ b, maxCompressedLen n = .ok b ∧ b.toNat = 32 + n.toNat + n.toNat / 6 := by
  have hadd : (32 + n).toNat = 32 + n.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hsum : (32 + n + n / 6).toNat = 32 + n.toNat + n.toNat / 6 := by
    rw [UInt64.toNat_add, hadd, UInt64.toNat_div]; simp; omega
  refine ⟨32 + n + n / 6, ?_, hsum⟩
  simp only [maxCompressedLen, Base.Uint64.addChecked, Base.Uint64.divChecked, bind,
    Except.bind]
  rw [ite_eq_left (by simp; omega)]
  dsimp only
  rw [ite_eq_right (by decide)]
  dsimp only
  rw [ite_eq_left (by rw [hadd, UInt64.toNat_div]; simp; omega)]

/-! ## What a decoded payload satisfies -/

/-- A payload that decodes has its declared length, and that length is within both bounds.

It is also at least the smallest encoding of the type.

The compressed bytes after the prefix are within the bound for that length.

They decompress to the payload. -/
theorem decodePayload_ok {typeMin typeBound : UInt64} {bs d : ByteArray}
    (h : decodePayload typeMin typeBound bs = .ok d) :
    ∃ declared b, decode (splitVarint bs.data.toList).1 = .ok declared ∧
      d.size = declared.toNat ∧ declared ≤ typeBound ∧ declared ≤ MAX_PAYLOAD_SIZE ∧
      typeMin ≤ declared ∧ maxCompressedLen declared = .ok b ∧
      (splitVarint bs.data.toList).2.length ≤ b.toNat ∧
      Snappy.decodeFrames ⟨(splitVarint bs.data.toList).2.toArray⟩ = .ok d := by
  simp only [decodePayload] at h
  generalize splitVarint bs.data.toList = sp at h ⊢
  obtain ⟨header, rest⟩ := sp
  cases hv : decode header with
  | error e => simp [hv, bind, Except.bind, Except.mapError] at h
  | ok declared =>
    cases hm : maxCompressedLen declared with
    | error e =>
      simp [hv, hm, bind, Except.bind, Except.mapError] at h
      split at h <;> (try split at h) <;> simp_all
    | ok b =>
      simp only [hv, hm, bind, Except.bind, Except.mapError] at h
      split at h
      · simp_all
      · rename_i hlt
        split at h
        · simp_all
        · rename_i hmin
          split at h
          · simp_all
          · rename_i hc
            cases hf : Snappy.decodeFrames ⟨rest.toArray⟩ with
            | error e => simp [hf] at h
            | ok data =>
              simp only [hf] at h
              split at h
              · simp_all
              · rename_i hsz
                simp only [pure, Except.pure, Except.ok.injEq] at h
                subst h
                have hle : declared.toNat ≤ typeBound.toNat ∧
                    declared.toNat ≤ MAX_PAYLOAD_SIZE.toNat := by
                  rw [UInt64.min_def] at hlt
                  split at hlt <;> rename_i hcond <;>
                    simp only [UInt64.not_lt, UInt64.le_iff_toNat_le] at hlt hcond <;> omega
                exact ⟨declared, b, by simp, by simpa using hsz,
                  UInt64.le_iff_toNat_le.mpr hle.1, UInt64.le_iff_toNat_le.mpr hle.2,
                  UInt64.not_lt.mp hmin, by simp [hm], by simpa using hc, by simp⟩

/-- The payload cap is 10 MiB. -/
theorem toNat_MAX_PAYLOAD_SIZE : MAX_PAYLOAD_SIZE.toNat = 10485760 := rfl

/-- The decoder accepts exactly the encoding of a length within the bounds, then compressed bytes.

The length is at most the smaller of the largest encoding and the cap, and at least the smallest.

The compressed bytes are within the bound for that length, and they decompress to the payload.
-/
theorem decodePayload_eq_ok_iff {typeMin typeBound : UInt64} {bs d : ByteArray} :
    decodePayload typeMin typeBound bs = .ok d ↔
      d.size ≤ (min typeBound MAX_PAYLOAD_SIZE).toNat ∧ typeMin.toNat ≤ d.size ∧
      ∃ rest, bs.data.toList = encode (UInt64.ofNat d.size) ++ rest ∧
        rest.length ≤ 32 + d.size + d.size / 6 ∧
        Snappy.decodeFrames ⟨rest.toArray⟩ = .ok d := by
  have hmax := toNat_MAX_PAYLOAD_SIZE
  constructor
  · intro h
    obtain ⟨declared, b, hv, hs, hty, hcap, hmin, hb, hlen, hf⟩ := decodePayload_ok h
    have hdeclared : UInt64.ofNat d.size = declared := by rw [hs, UInt64.ofNat_toNat]
    -- The declared length is within the cap, so the compressed bound does not overflow.
    have hcap' := UInt64.le_iff_toNat_le.mp hcap
    obtain ⟨b', hb', hbv⟩ := maxCompressedLen_eq (n := declared) (by omega)
    obtain rfl : b = b' := Except.ok.inj (hb.symm.trans hb')
    refine ⟨?_, ?_, (splitVarint bs.data.toList).2, ?_, ?_, hf⟩
    · rw [hs, UInt64.min_def]
      split
      · exact UInt64.le_iff_toNat_le.mp hty
      · exact hcap'
    · rw [hs]
      exact UInt64.le_iff_toNat_le.mp hmin
    · -- The prefix decodes to the declared length, so it is the encoding of that length.
      rw [hdeclared, encode_decode hv]
      exact (List.take_append_drop _ _).symm
    · rw [hs]
      omega
  · rintro ⟨hbound, hmin, rest, hbs, hlen, hf⟩
    -- The length is within the cap, so 64 bits hold it and its bound on the compressed bytes.
    have hle : (min typeBound MAX_PAYLOAD_SIZE).toNat ≤ MAX_PAYLOAD_SIZE.toNat := by
      rw [UInt64.min_def]
      split
      · rename_i hle
        exact UInt64.le_iff_toNat_le.mp hle
      · exact Nat.le_refl _
    have hs : (UInt64.ofNat d.size).toNat = d.size :=
      UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
    obtain ⟨b, hb, hbv⟩ := maxCompressedLen_eq (n := UInt64.ofNat d.size) (by omega)
    rw [hs] at hbv
    have hgt : ¬ min typeBound MAX_PAYLOAD_SIZE < UInt64.ofNat d.size := by
      rw [UInt64.lt_iff_toNat_lt, hs]
      omega
    have hlt : ¬ UInt64.ofNat d.size < typeMin := by
      rw [UInt64.lt_iff_toNat_lt, hs]
      omega
    have hc : ¬ b.toNat < rest.length := by omega
    have hsize : ¬ d.size ≠ (UInt64.ofNat d.size).toNat := by omega
    simp only [decodePayload, hbs, splitVarint_encode, decode_encode, hb, hf, bind, Except.bind,
      Except.mapError, hgt, hlt, hc, hsize, ite_false, pure, Except.pure]

/-- A payload with more compressed bytes than the bound for its declared length is rejected. -/
theorem decodePayload_compressedTooLong {typeMin typeBound declared b : UInt64}
    {bs : ByteArray} (hv : decode (splitVarint bs.data.toList).1 = .ok declared)
    (hle : declared ≤ min typeBound MAX_PAYLOAD_SIZE) (hmin : typeMin ≤ declared)
    (hb : maxCompressedLen declared = .ok b)
    (hlong : b.toNat < (splitVarint bs.data.toList).2.length) :
    decodePayload typeMin typeBound bs =
      .error (.compressedTooLong (splitVarint bs.data.toList).2.length b.toNat) := by
  simp only [decodePayload]
  generalize splitVarint bs.data.toList = sp at hv hlong ⊢
  obtain ⟨header, rest⟩ := sp
  simp [hv, hb, bind, Except.bind, Except.mapError, UInt64.not_lt.mpr hle,
    UInt64.not_lt.mpr hmin, hlong, throw, throwThe, MonadExceptOf.throw]

/-- A payload whose declared length is above either bound is rejected. -/
theorem decodePayload_lengthOutOfBounds {typeMin typeBound declared : UInt64}
    {bs : ByteArray} (hv : decode (splitVarint bs.data.toList).1 = .ok declared)
    (hgt : min typeBound MAX_PAYLOAD_SIZE < declared) :
    decodePayload typeMin typeBound bs =
      .error (.lengthOutOfBounds declared (min typeBound MAX_PAYLOAD_SIZE)) := by
  simp only [decodePayload]
  generalize splitVarint bs.data.toList = sp at hv ⊢
  obtain ⟨header, rest⟩ := sp
  simp [hv, bind, Except.bind, Except.mapError, hgt, throw, throwThe, MonadExceptOf.throw]

/-- A payload whose declared length is below the smallest encoding of its type is rejected.

The decoder checks the upper bounds first, so the length must pass them. -/
theorem decodePayload_lengthBelowMinimum {typeMin typeBound declared : UInt64}
    {bs : ByteArray} (hv : decode (splitVarint bs.data.toList).1 = .ok declared)
    (hle : declared ≤ min typeBound MAX_PAYLOAD_SIZE) (hlt : declared < typeMin) :
    decodePayload typeMin typeBound bs = .error (.lengthBelowMinimum declared typeMin) := by
  simp only [decodePayload]
  generalize splitVarint bs.data.toList = sp at hv ⊢
  obtain ⟨header, rest⟩ := sp
  simp [hv, bind, Except.bind, Except.mapError, UInt64.not_lt.mpr hle, hlt, throw, throwThe,
    MonadExceptOf.throw]

/-! ## The literal encoder -/

/-- Uncompressed chunks add eight bytes to each block of up to 65536 bytes. -/
theorem length_encodeChunks_uncompressedChunk_le (data : List UInt8) (fuel : Nat) :
    (Snappy.encodeChunks Snappy.uncompressedChunk data fuel).length ≤
      data.length + 8 * ((data.length + 65535) / 65536) := by
  induction fuel generalizing data with
  | zero => cases data <;> simp [Snappy.encodeChunks]
  | succ fuel ih =>
    cases data with
    | nil => simp [Snappy.encodeChunks]
    | cons b bs =>
      have := ih ((b :: bs).drop Snappy.maxChunkLength)
      simp only [Snappy.encodeChunks, Snappy.uncompressedChunk, List.length_append,
        List.length_cons, Vector.length_toList, List.length_take, List.length_drop,
        Snappy.maxChunkLength] at this ⊢
      omega

/-- The literal frames of `n` bytes fit in the bound `32 + n + n / 6`. -/
theorem size_encodeFramesLiteral_le (d : ByteArray) :
    (Snappy.encodeFramesLiteral d).size ≤ 32 + d.size + d.size / 6 := by
  have := length_encodeChunks_uncompressedChunk_le d.data.toList d.data.size
  simp only [Array.length_toList] at this
  simp only [Snappy.encodeFramesLiteral, ByteArray.size, List.size_toArray, List.length_append,
    Snappy.streamIdentifier, List.length_cons, List.length_nil]
  omega

/-- A payload of the literal encoder decodes back, when it fits the bounds. -/
theorem decodePayload_encodePayloadLiteral {typeMin typeBound : UInt64} {d : ByteArray}
    (hp : d.size ≤ MAX_PAYLOAD_SIZE.toNat) (ht : d.size ≤ typeBound.toNat)
    (hm : typeMin.toNat ≤ d.size) :
    decodePayload typeMin typeBound (encodePayloadLiteral d) = .ok d := by
  refine decodePayload_eq_ok_iff.mpr
    ⟨?_, hm, (Snappy.encodeFramesLiteral d).data.toList, ?_, ?_, ?_⟩
  · rw [UInt64.min_def]
    split <;> omega
  · simp [encodePayloadLiteral]
  · rw [Array.length_toList]
    exact size_encodeFramesLiteral_le d
  · simpa using Snappy.Frame.decodeFrames_encodeFramesLiteral d

/-- A payload of the encoder that compresses decodes back, when it fits the bounds. -/
theorem decodePayload_encodePayload {typeMin typeBound : UInt64} {d : ByteArray}
    (hp : d.size ≤ MAX_PAYLOAD_SIZE.toNat) (ht : d.size ≤ typeBound.toNat)
    (hm : typeMin.toNat ≤ d.size) :
    decodePayload typeMin typeBound (encodePayload d) = .ok d := by
  refine decodePayload_eq_ok_iff.mpr
    ⟨?_, hm, (Snappy.encodeFrames d).data.toList, ?_, ?_, ?_⟩
  · rw [UInt64.min_def]
    split <;> omega
  · simp [encodePayload]
  · rw [Array.length_toList]
    exact Nat.le_trans (Snappy.FrameEncode.size_encodeFrames_le d) (size_encodeFramesLiteral_le d)
  · simpa using Snappy.FrameEncode.decodeFrames_encodeFrames d

/-! ## Response codes and chunks -/

/-- A byte array rebuilt from the list of its bytes is itself. -/
theorem mk_toList (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  simp

/-- Every byte reads back as itself through its response code. -/
theorem toByte_ofByte (b : UInt8) : (ResponseCode.ofByte b).toByte = b := by
  by_cases h0 : b = 0 <;> by_cases h1 : b = 1 <;> by_cases h2 : b = 2 <;>
    by_cases h3 : b = 3 <;> by_cases h4 : b < 128 <;>
    simp [ResponseCode.ofByte, ResponseCode.toByte, h0, h1, h2, h3, h4]

/-- Two bytes with one response code are one byte. -/
theorem ofByte_injective : Function.Injective ResponseCode.ofByte := fun a b h => by
  rw [← toByte_ofByte a, ← toByte_ofByte b, h]

/-- A response code reads back from its own byte exactly when its byte is in its range.

A reserved code needs a byte from 4 to 127, and a request-specific code a byte from 128.

The four named codes always read back. -/
theorem ofByte_toByte_eq_iff (c : ResponseCode) :
    ResponseCode.ofByte c.toByte = c ↔
      (∀ k, c = .reserved k → 4 ≤ k.toNat ∧ k.toNat < 128) ∧
        (∀ k, c = .requestSpecific k → 128 ≤ k.toNat) := by
  cases c with
  | reserved k | requestSpecific k =>
    have h0 : k = 0 ↔ k.toNat = 0 := by rw [← UInt8.toNat_inj]; rfl
    have h1 : k = 1 ↔ k.toNat = 1 := by rw [← UInt8.toNat_inj]; rfl
    have h2 : k = 2 ↔ k.toNat = 2 := by rw [← UInt8.toNat_inj]; rfl
    have h3 : k = 3 ↔ k.toNat = 3 := by rw [← UInt8.toNat_inj]; rfl
    simp only [ResponseCode.ofByte, ResponseCode.toByte, h0, h1, h2, h3, UInt8.lt_iff_toNat_lt]
    by_cases a : k.toNat = 0 <;> by_cases b : k.toNat = 1 <;> by_cases c : k.toNat = 2 <;>
      by_cases d : k.toNat = 3 <;> by_cases e : k.toNat < 128 <;> simp [a, b, c, d, e] <;> omega
  | _ => simp [ResponseCode.ofByte, ResponseCode.toByte]

/-- A code byte, the context bytes and payload bytes that decode back make a chunk that decodes.

The payload decodes at the bounds of its code.

On a success those are the bounds of the message type, and otherwise those of an error message. -/
private theorem decodeResponseChunk_append {contextBytes : Nat} {typeMin typeBound : UInt64}
    {c : ResponseChunk} {p : ByteArray}
    (hc : ResponseCode.ofByte c.code.toByte = c.code)
    (hctx : c.context.size = if c.code = .success then contextBytes else 0)
    (hd : decodePayload (if c.code = .success then typeMin else 0)
      (if c.code = .success then typeBound else MAX_ERROR_MESSAGE_SIZE) p = .ok c.payload) :
    decodeResponseChunk contextBytes typeMin typeBound (⟨#[c.code.toByte]⟩ ++ c.context ++ p) =
      .ok c := by
  obtain ⟨code, context, payload⟩ := c
  simp only at hc hctx hd
  have hbytes : (⟨#[code.toByte]⟩ ++ context ++ p : ByteArray).data.toList =
      code.toByte :: (context.data.toList ++ p.data.toList) := by
    simp [ByteArray.data_append]
  simp only [decodeResponseChunk, hbytes, hc]
  by_cases hs : code = .success
  · subst hs
    simp only [ite_true] at hctx hd
    subst hctx
    have hlen : context.data.toList.length = context.size := Array.length_toList
    rw [List.drop_left' hlen, List.take_left' hlen, mk_toList, mk_toList]
    simp [hlen, hd, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp only [hs, ite_false] at hctx hd
    have hctx' : context = ByteArray.empty := by
      obtain ⟨⟨l⟩⟩ := context
      cases l with
      | nil => rfl
      | cons _ _ => simp [ByteArray.size] at hctx
    subst hctx'
    rw [show ByteArray.empty.data.toList = [] from rfl, List.nil_append, mk_toList]
    cases code with
    | success => contradiction
    | _ => simp [hd, bind, Except.bind, pure, Except.pure]

/-- A response chunk of the literal encoder decodes back.

Its code must be the code of its own byte, which excludes a reserved code outside 4 to 127.

A success carries the context bytes of the method, and an error carries none.

The payload fits the bounds of its code. -/
theorem decodeResponseChunk_encodeResponseChunkLiteral {contextBytes : Nat}
    {typeMin typeBound : UInt64} {c : ResponseChunk}
    (hc : ResponseCode.ofByte c.code.toByte = c.code)
    (hctx : c.context.size = if c.code = .success then contextBytes else 0)
    (hp : c.payload.size ≤ MAX_PAYLOAD_SIZE.toNat)
    (ht : c.payload.size ≤
      (if c.code = .success then typeBound else MAX_ERROR_MESSAGE_SIZE).toNat)
    (hm : c.code = .success → typeMin.toNat ≤ c.payload.size) :
    decodeResponseChunk contextBytes typeMin typeBound (encodeResponseChunkLiteral c) =
      .ok c := by
  refine decodeResponseChunk_append hc hctx (decodePayload_encodePayloadLiteral hp ht ?_)
  split
  · exact hm ‹_›
  · exact Nat.zero_le _

/-- A response chunk of the encoder that compresses decodes back.

Its code must be the code of its own byte, which excludes a reserved code outside 4 to 127.

A success carries the context bytes of the method, and an error carries none.

The payload fits the bounds of its code. -/
theorem decodeResponseChunk_encodeResponseChunk {contextBytes : Nat}
    {typeMin typeBound : UInt64} {c : ResponseChunk}
    (hc : ResponseCode.ofByte c.code.toByte = c.code)
    (hctx : c.context.size = if c.code = .success then contextBytes else 0)
    (hp : c.payload.size ≤ MAX_PAYLOAD_SIZE.toNat)
    (ht : c.payload.size ≤
      (if c.code = .success then typeBound else MAX_ERROR_MESSAGE_SIZE).toNat)
    (hm : c.code = .success → typeMin.toNat ≤ c.payload.size) :
    decodeResponseChunk contextBytes typeMin typeBound (encodeResponseChunk c) = .ok c := by
  refine decodeResponseChunk_append hc hctx (decodePayload_encodePayload hp ht ?_)
  split
  · exact hm ‹_›
  · exact Nat.zero_le _

/-- The bytes that decode to a chunk are its code byte, its context bytes and a payload.

The code is the code of its own byte, which excludes a reserved code outside 4 to 127.

A success carries the context bytes of the method, and an error carries none.

The payload decodes at the bounds of the code.

On a success those are the bounds of the message type, and otherwise those of an error message. -/
theorem decodeResponseChunk_eq_ok_iff {contextBytes : Nat} {typeMin typeBound : UInt64}
    {bs : ByteArray} {c : ResponseChunk} :
    decodeResponseChunk contextBytes typeMin typeBound bs = .ok c ↔
      ResponseCode.ofByte c.code.toByte = c.code ∧
        c.context.size = (if c.code = .success then contextBytes else 0) ∧
        ∃ p : ByteArray, bs = ⟨#[c.code.toByte]⟩ ++ c.context ++ p ∧
          decodePayload (if c.code = .success then typeMin else 0)
            (if c.code = .success then typeBound else MAX_ERROR_MESSAGE_SIZE) p =
            .ok c.payload := by
  constructor
  · intro h
    obtain ⟨⟨l⟩⟩ := bs
    unfold decodeResponseChunk at h
    cases l with
    | nil => simp [throw, throwThe, MonadExceptOf.throw] at h
    | cons b rest =>
      have hb : (ResponseCode.ofByte b).toByte = b := toByte_ofByte b
      simp only at h
      split at h
      · rename_i hcode
        rw [hcode] at hb
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        · rename_i long
          cases hp : decodePayload typeMin typeBound ⟨(rest.drop contextBytes).toArray⟩ with
          | error e => simp [hp, bind, Except.bind] at h
          | ok payload =>
            simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
            subst h
            refine ⟨rfl, ?_, ⟨(rest.drop contextBytes).toArray⟩, ?_, by simpa using hp⟩
            · simp only [ite_true, ByteArray.size, List.size_toArray, List.length_take]
              omega
            · subst hb
              apply ByteArray.ext
              simp [ByteArray.data_append]
      · rename_i _ hne
        cases hp : decodePayload 0 MAX_ERROR_MESSAGE_SIZE ⟨rest.toArray⟩ with
        | error e => simp [hp, bind, Except.bind] at h
        | ok payload =>
          simp only [hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hs : ResponseCode.ofByte b ≠ .success := hne
          refine ⟨by rw [hb], by simp [hs], ⟨rest.toArray⟩, ?_, by simpa [hs] using hp⟩
          apply ByteArray.ext
          simp [ByteArray.data_append, hb]
  · rintro ⟨hc, hctx, p, rfl, hd⟩
    exact decodeResponseChunk_append hc hctx hd

/-! ## Error codes -/

/-- Two errors with one code come from one constructor. -/
theorem code_injective (e₁ e₂ : ReqRespError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [ReqRespError.code] at h; exact absurd h (by decide))

/-- No error has code 0, which the bindings keep for a failure with no error code. -/
theorem code_ne_zero (e : ReqRespError) : e.code ≠ 0 := by
  cases e <;> simp only [ReqRespError.code] <;> decide

end EthLib.Networking.Proofs.ReqResp.Encoding
