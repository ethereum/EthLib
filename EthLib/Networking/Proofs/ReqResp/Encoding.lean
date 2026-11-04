module

public import EthLib.Networking.ReqResp.Encoding
public import EthLib.Networking.Proofs.Encoding.Varint
public import EthLib.Networking.Proofs.Snappy.Frame

/-!
# `Networking.Proofs.ReqResp.Encoding`

Properties of the `ssz_snappy` encoding of requests and responses.

A payload that decodes has its declared length, within both bounds.

More compressed bytes than the bound for the declared length reject the payload.

The literal encoder writes payloads and response chunks that decode back.

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

/-! ## The literal encoder -/

/-- Uncompressed chunks add eight bytes to each block of up to 65536 bytes. -/
theorem length_encodeChunksLiteral_le (data : List UInt8) (fuel : Nat) :
    (Snappy.encodeChunksLiteral data fuel).length ≤
      data.length + 8 * ((data.length + 65535) / 65536) := by
  induction fuel generalizing data with
  | zero => cases data <;> simp [Snappy.encodeChunksLiteral]
  | succ fuel ih =>
    cases data with
    | nil => simp [Snappy.encodeChunksLiteral]
    | cons b bs =>
      have := ih ((b :: bs).drop Snappy.maxChunkLength)
      simp only [Snappy.encodeChunksLiteral, Snappy.uncompressedChunk, List.length_append,
        List.length_cons, Vector.length_toList, List.length_take, List.length_drop,
        Snappy.maxChunkLength] at this ⊢
      omega

/-- The literal frames of `n` bytes fit in the bound `32 + n + n / 6`. -/
theorem size_encodeFramesLiteral_le (d : ByteArray) :
    (Snappy.encodeFramesLiteral d).size ≤ 32 + d.size + d.size / 6 := by
  have := length_encodeChunksLiteral_le d.data.toList d.data.size
  simp only [Array.length_toList] at this
  simp only [Snappy.encodeFramesLiteral, ByteArray.size, List.size_toArray, List.length_append,
    Snappy.streamIdentifier, List.length_cons, List.length_nil]
  omega

/-- A payload of the literal encoder decodes back, when it fits both bounds. -/
theorem decodePayload_encodePayloadLiteral {typeBound : UInt64} {d : ByteArray}
    (hp : d.size ≤ MAX_PAYLOAD_SIZE.toNat) (ht : d.size ≤ typeBound.toNat) :
    decodePayload typeBound (encodePayloadLiteral d) = .ok d := by
  have h : d.size < 2 ^ 63 := by have : MAX_PAYLOAD_SIZE.toNat = 10485760 := rfl; omega
  have hs : (UInt64.ofNat d.size).toNat = d.size :=
    UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)
  obtain ⟨b, hb, hbv⟩ := maxCompressedLen_eq (n := UInt64.ofNat d.size) (by omega)
  rw [hs] at hbv
  have hframes := size_encodeFramesLiteral_le d
  have hbound : ¬ min typeBound MAX_PAYLOAD_SIZE < UInt64.ofNat d.size := by
    rw [UInt64.min_def]; split <;> rw [UInt64.lt_iff_toNat_lt, hs] <;> omega
  have hlen : ¬ b.toNat < (Snappy.encodeFramesLiteral d).data.toList.length := by
    have : (Snappy.encodeFramesLiteral d).data.toList.length =
        (Snappy.encodeFramesLiteral d).size :=
      Array.length_toList
    omega
  have hsize : ¬ d.size ≠ (UInt64.ofNat d.size).toNat := by omega
  simp only [decodePayload, encodePayloadLiteral, ByteArray.data_append, Array.toList_append,
    splitVarint_encode, decode_encode, hb, bind, Except.bind, Except.mapError, hbound, hlen,
    ite_false, Array.toArray_toList]
  rw [show ({ data := (Snappy.encodeFramesLiteral d).data } : ByteArray) =
    Snappy.encodeFramesLiteral d from rfl, Snappy.Frame.decodeFrames_encodeFramesLiteral]
  simp [pure, Except.pure]
  omega

/-! ## What a decoded payload satisfies -/

/-- A payload that decodes has its declared length, and that length is within both bounds.

The compressed bytes after the prefix are within the bound for that length. -/
theorem decodePayload_ok {typeBound : UInt64} {bs d : ByteArray}
    (h : decodePayload typeBound bs = .ok d) :
    ∃ declared b, decode (splitVarint bs.data.toList).1 = .ok declared ∧
      d.size = declared.toNat ∧ declared ≤ typeBound ∧ declared ≤ MAX_PAYLOAD_SIZE ∧
      maxCompressedLen declared = .ok b ∧ (splitVarint bs.data.toList).2.length ≤ b.toNat := by
  simp only [decodePayload] at h
  generalize splitVarint bs.data.toList = sp at h ⊢
  obtain ⟨header, rest⟩ := sp
  cases hv : decode header with
  | error e => simp [hv, bind, Except.bind, Except.mapError] at h
  | ok declared =>
    cases hm : maxCompressedLen declared with
    | error e =>
      simp [hv, hm, bind, Except.bind, Except.mapError] at h
      split at h <;> simp_all
    | ok b =>
      simp only [hv, hm, bind, Except.bind, Except.mapError] at h
      split at h
      · simp_all
      · rename_i hlt
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
                UInt64.le_iff_toNat_le.mpr hle.1, UInt64.le_iff_toNat_le.mpr hle.2, by simp [hm],
                by simpa using hc⟩

/-- A payload with more compressed bytes than the bound for its declared length is rejected. -/
theorem decodePayload_compressedTooLong {typeBound declared b : UInt64}
    {bs : ByteArray} (hv : decode (splitVarint bs.data.toList).1 = .ok declared)
    (hle : declared ≤ min typeBound MAX_PAYLOAD_SIZE)
    (hb : maxCompressedLen declared = .ok b)
    (hlong : b.toNat < (splitVarint bs.data.toList).2.length) :
    decodePayload typeBound bs =
      .error (.compressedTooLong (splitVarint bs.data.toList).2.length b.toNat) := by
  simp only [decodePayload]
  generalize splitVarint bs.data.toList = sp at hv hlong ⊢
  obtain ⟨header, rest⟩ := sp
  simp [hv, hb, bind, Except.bind, Except.mapError, UInt64.not_lt.mpr hle, hlong, throw,
    throwThe, MonadExceptOf.throw]

/-- A payload whose declared length is above either bound is rejected. -/
theorem decodePayload_lengthOutOfBounds {typeBound declared : UInt64}
    {bs : ByteArray} (hv : decode (splitVarint bs.data.toList).1 = .ok declared)
    (hgt : min typeBound MAX_PAYLOAD_SIZE < declared) :
    decodePayload typeBound bs =
      .error (.lengthOutOfBounds declared (min typeBound MAX_PAYLOAD_SIZE)) := by
  simp only [decodePayload]
  generalize splitVarint bs.data.toList = sp at hv ⊢
  obtain ⟨header, rest⟩ := sp
  simp [hv, bind, Except.bind, Except.mapError, hgt, throw, throwThe, MonadExceptOf.throw]

/-! ## Response codes and chunks -/

/-- A byte array rebuilt from the list of its bytes is itself. -/
theorem mk_toList (b : ByteArray) : (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  simp

/-- Every byte reads back as itself through its response code. -/
theorem toByte_ofByte (b : UInt8) : (ResponseCode.ofByte b).toByte = b := by
  by_cases h0 : b = 0 <;> by_cases h1 : b = 1 <;> by_cases h2 : b = 2 <;>
    by_cases h3 : b = 3 <;> by_cases h4 : b < 128 <;>
    simp [ResponseCode.ofByte, ResponseCode.toByte, h0, h1, h2, h3, h4]

/-- A response chunk of the literal encoder decodes back.

Its code must be the code of its own byte, which excludes a reserved code outside 4 to 127.

A success carries the context bytes of the method, and an error carries none.

The payload fits the bound of its code. -/
theorem decodeResponseChunk_encodeResponseChunkLiteral {contextBytes : Nat}
    {typeBound : UInt64} {c : ResponseChunk}
    (hc : ResponseCode.ofByte c.code.toByte = c.code)
    (hctx : c.context.size = if c.code = .success then contextBytes else 0)
    (hp : c.payload.size ≤ MAX_PAYLOAD_SIZE.toNat)
    (ht : c.payload.size ≤
      (if c.code = .success then typeBound else MAX_ERROR_MESSAGE_SIZE).toNat) :
    decodeResponseChunk contextBytes typeBound (encodeResponseChunkLiteral c) =
      .ok c := by
  obtain ⟨code, context, payload⟩ := c
  simp only at hc hctx hp ht
  have hbytes : (encodeResponseChunkLiteral ⟨code, context, payload⟩).data.toList =
      code.toByte :: (context.data.toList ++ (encodePayloadLiteral payload).data.toList) := by
    simp [encodeResponseChunkLiteral, ByteArray.data_append]
  simp only [decodeResponseChunk, hbytes, hc]
  by_cases hs : code = .success
  · subst hs
    simp only [ite_true] at hctx ht
    subst hctx
    have hlen : context.data.toList.length = context.size := Array.length_toList
    rw [List.drop_left' hlen, List.take_left' hlen, mk_toList]
    simp [hlen, decodePayload_encodePayloadLiteral hp ht, bind, Except.bind, pure,
      Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp only [hs, ite_false] at hctx ht
    have hctx' : context = ByteArray.empty := by
      obtain ⟨⟨l⟩⟩ := context
      cases l with
      | nil => rfl
      | cons _ _ => simp [ByteArray.size] at hctx
    subst hctx'
    rw [show ByteArray.empty.data.toList = [] from rfl, List.nil_append, mk_toList]
    cases code with
    | success => contradiction
    | _ =>
      simp [decodePayload_encodePayloadLiteral hp ht, bind, Except.bind, pure, Except.pure]

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
