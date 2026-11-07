module

public import EthLib.Engine.Json
public import EthLib.Base.Hex
public import EthLib.Base.Except

/-!
# Proofs: the JSON decoders

The decoders read the value of a hex digit from its ASCII byte.

They read back each digit that the hex encoder writes.

Those digits are lowercase, so this holds whether or not the decoders accept uppercase.

The byte string decoders read back the bytes of their hex encoding.

That holds for byte strings of any length and of a given size.

Whether the decoder accepts uppercase digits does not matter there.

The proofs rest on two facts about the encoding.

Its characters are ASCII.

It writes two digits for each byte.

A number that the decoder checks against `2^bits` is below `2^bits`.

So the 64-bit decoder returns the decoded number itself, without wrapping.

A byte string decoded with a limit on its size has at most that many bytes.

A field of an object decodes to the value that the object holds under its name.

A withdrawal decodes exactly when its object holds exactly its four fields, each of its type.

The 64-bit decoder returns a number exactly when the decoder with the bound `2^64` returns it.

The bounded byte decoder succeeds exactly when the byte decoder succeeds within the limit.

A decoded payload has version 1, 2 or 3 of the structure.

It holds the withdrawals exactly from version 2.

It holds the two blob gas fields exactly in version 3.
-/

public section

namespace EthLib.Engine.Json

open EthLib.Base

/-- The decoders read the value of each digit that the hex encoder writes. -/
theorem hexValue_hexDigitChar (upper : Bool) (n : Fin 16) :
    hexValue upper (hexDigitChar n).toUInt8 = some n.val.toUInt8 := by
  decide +revert

/-- A decoded number is below the bound that the decoder checks. -/
theorem lt_of_quantity {what : String} {bits : Nat} {j : Lean.Json} {value : Nat}
    (h : quantity what bits j = .ok value) : value < 2 ^ bits := by
  unfold quantity at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  -- The checks for no digits and for a leading zero fail, so neither branch returns a value.
  split at h
  · cases h
  split at h
  · cases h
  -- Whatever the digit loop returns, the last step compares it with the bound.
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  dsimp only at h
  split at h
  · cases h
    assumption
  · cases h

/-- A decoded 64-bit number is the number read with the bound `2^64`, so it does not wrap. -/
theorem quantity_of_uint64 {what : String} {j : Lean.Json} {x : UInt64}
    (h : uint64 what j = .ok x) : quantity what 64 j = .ok x.toNat := by
  unfold uint64 at h
  obtain ⟨value, hq, hx⟩ := bind_ok_iff.mp h
  cases hx
  -- The value is below `2^64`, so its conversion keeps it.
  rw [hq, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (lt_of_quantity hq)]

/-- A byte string decoded with a limit has at most that many bytes. -/
theorem size_le_of_bytesMax {what : String} {n : Nat} {j : Lean.Json} {b : ByteArray}
    (h : bytesMax what n j = .ok b) : b.size ≤ n := by
  unfold bytesMax at h
  obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
  split at h
  · cases h
    assumption
  · cases h

/-- A 64-bit number decodes to `x` exactly when the number read with the bound `2^64` is `x`. -/
theorem uint64_eq_ok_iff {what : String} {j : Lean.Json} {x : UInt64} :
    uint64 what j = .ok x ↔ quantity what 64 j = .ok x.toNat := by
  refine ⟨quantity_of_uint64, fun h => ?_⟩
  unfold uint64
  rw [h]
  simp [bind, Except.bind, pure, Except.pure]

/-- A byte string decodes within a limit exactly when it decodes and fits the limit. -/
theorem bytesMax_eq_ok_iff {what : String} {n : Nat} {j : Lean.Json} {b : ByteArray} :
    bytesMax what n j = .ok b ↔ bytes what j = .ok b ∧ b.size ≤ n := by
  unfold bytesMax
  constructor
  · intro h
    obtain ⟨c, hc, h⟩ := bind_ok_iff.mp h
    split at h
    · cases h
      exact ⟨hc, by assumption⟩
    · cases h
  · rintro ⟨h, hn⟩
    rw [h]
    simp [bind, Except.bind, hn, pure, Except.pure]

/-- The version and the optional fields of a decoded payload, in one walk of the decoder. -/
private theorem anyPayload_walk {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    (p.version = 1 ∨ p.version = 2 ∨ p.version = 3) ∧ (p.withdrawals.isSome ↔ 2 ≤ p.version) ∧
      (p.blobGasUsed.isSome ↔ 3 ≤ p.version) ∧ (p.excessBlobGas.isSome ↔ 3 ≤ p.version) := by
  unfold anyPayload at h
  -- Inline the steps that the decoder shares between its branches.
  dsimp only at h
  -- Split each step of the decoder: a failing step contradicts the success, and a read value stays.
  repeat' (first
    | (simp only [invalid, throw, throwThe, MonadExceptOf.throw] at h; cases h; done)
    | (obtain ⟨_, step, h⟩ := bind_ok_iff.mp h
       first | cases step | obtain ⟨_, -, rfl⟩ := map_ok_iff.mp step | skip)
    | split at h)
  -- Each success fixes the version and the fields.
  all_goals (cases h; simp)

/-- A decoded payload has version 1, 2 or 3. -/
theorem version_of_anyPayload {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    p.version = 1 ∨ p.version = 2 ∨ p.version = 3 :=
  (anyPayload_walk h).1

/-- A decoded payload holds the withdrawals exactly from version 2. -/
theorem withdrawals_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.withdrawals.isSome ↔ 2 ≤ p.version :=
  (anyPayload_walk h).2.1

/-- A decoded payload holds the blob gas used exactly in version 3. -/
theorem blobGasUsed_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.blobGasUsed.isSome ↔ 3 ≤ p.version :=
  (anyPayload_walk h).2.2.1

/-- A decoded payload holds the excess blob gas exactly in version 3. -/
theorem excessBlobGas_isSome_iff_of_anyPayload {j : Lean.Json} {p : AnyPayload}
    (h : anyPayload j = .ok p) : p.excessBlobGas.isSome ↔ 3 ≤ p.version :=
  (anyPayload_walk h).2.2.2

/-- A decoded payload has version 1, 2 or 3, and its optional fields match that version. -/
theorem shape_of_anyPayload {j : Lean.Json} {p : AnyPayload} (h : anyPayload j = .ok p) :
    (p.version = 1 ∨ p.version = 2 ∨ p.version = 3) ∧ (p.withdrawals.isSome ↔ 2 ≤ p.version) ∧
      (p.blobGasUsed.isSome ↔ 3 ≤ p.version) ∧ (p.excessBlobGas.isSome ↔ 3 ≤ p.version) :=
  ⟨version_of_anyPayload h, withdrawals_isSome_iff_of_anyPayload h,
    blobGasUsed_isSome_iff_of_anyPayload h, excessBlobGas_isSome_iff_of_anyPayload h⟩

/-- ASCII characters encode to their own bytes. -/
private theorem ascii_utf8Encode (l : List Char) (h : ∀ c ∈ l, c.val ≤ 0x7F) :
    l.utf8Encode = (l.map fun c => c.val.toUInt8).toByteArray := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : c.utf8Size = 1 := by simp [Char.utf8Size, h c (by simp)]
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, ih (fun d hd => h d (by simp [hd])),
      String.utf8EncodeChar_eq_singleton hc, List.map_cons]
    exact (List.toByteArray_append (l := [c.val.toUInt8])).symm

/-- Entry `2 * i` and `2 * i + 1` of a list that holds two entries per element. -/
private theorem flatMap_pair_getElem? {α β : Type} (x y : α → β) (l : List α) (i : Nat) :
    (l.flatMap fun a => [x a, y a])[2 * i]? = l[i]?.map x ∧
    (l.flatMap fun a => [x a, y a])[2 * i + 1]? = l[i]?.map y := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    cases i with
    | zero => simp
    | succ i =>
      have := ih i
      simp only [List.flatMap_cons, List.cons_append]
      constructor
      · rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega]; simpa using this.1
      · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 by omega]; simpa using this.2

/-- A loop that pushes one byte per index returns the bytes it pushed. -/
private theorem forIn_range'_push {s k : Nat}
    {f : Nat → ByteArray → Except EngineError (ForInStep ByteArray)}
    (g : Nat → UInt8) (h : ∀ i out, i ∈ List.range' s k → f i out = .ok (.yield (out.push (g i))))
    (out : ByteArray) :
    forIn (List.range' s k) out f = .ok (out ++ ((List.range' s k).map g).toByteArray) := by
  induction k generalizing s out with
  | zero => simp [List.range'_zero]; rfl
  | succ k ih =>
    rw [List.range'_succ, List.forIn_cons, h s out (by simp [List.range'_succ])]
    simp only [bind, Except.bind]
    rw [ih (fun i o hi => h i o (by simp [List.range'_succ, hi]))]
    congr 1
    apply ByteArray.ext
    simp [List.map_cons]

/-- The hex digits are ASCII. -/
private theorem hexDigitChar_ascii (n : Fin 16) : (hexDigitChar n).val ≤ 0x7F := by
  revert n; decide +revert

/-- The digits after the marker `0x` of a hex encoding are the ASCII codes of its characters. -/
theorem hexDigits_hexString (what : String) (data : List UInt8) :
    hexDigits what (.str (hexString data)) =
      .ok ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8).toByteArray := by
  unfold hexDigits
  have hascii : ∀ c ∈ '0' :: 'x' :: data.flatMap byteHexDigits, c.val ≤ 0x7F := by
    intro c hc
    simp only [List.mem_cons, List.mem_flatMap, byteHexDigits, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | ⟨b, -, rfl | rfl⟩
    · decide
    · decide
    · exact hexDigitChar_ascii _
    · exact hexDigitChar_ascii _
  have hs : (hexString data).toUTF8 =
      ('0'.val.toUInt8 :: 'x'.val.toUInt8 ::
        (data.flatMap byteHexDigits).map fun c => c.val.toUInt8).toByteArray := by
    rw [String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := hexString data),
      toList_hexString, String.toByteArray_ofList, ascii_utf8Encode _ hascii]
    rfl
  simp only [hs]
  generalize (data.flatMap byteHexDigits).map (fun c => c.val.toUInt8) = ds
  have h0 : '0'.val.toUInt8 = 48 := by decide
  have hx : 'x'.val.toUInt8 = 120 := by decide
  rw [h0, hx]
  have h1 : (48 :: 120 :: ds).toByteArray[0]? = some 48 := by simp
  have h2 : (48 :: 120 :: ds).toByteArray[1]? = some 120 := by simp
  simp only [h1, h2, and_self, ↓reduceIte]
  congr 1
  apply ByteArray.ext
  simp [ByteArray.data_extract]

/-- A byte is sixteen times its high digit plus its low digit. -/
private theorem byte_split (b : UInt8) :
    16 * (b.toNat / 16).toUInt8 + (b.toNat % 16).toUInt8 = b := by
  have h := b.toNat_lt
  apply UInt8.toNat_inj.mp
  simp only [UInt8.toNat_add, UInt8.toNat_mul, Nat.toUInt8_eq, UInt8.toNat_ofNat,
    UInt8.toNat_ofNat']
  omega

/-- The sum of a list of twos is twice its length. -/
private theorem sum_two (l : List UInt8) : (l.map fun _ => 2).sum = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; omega

/-- The high digit of a byte. -/
private def highDigit (b : UInt8) : Fin 16 := ⟨b.toNat / 16, by have := b.toNat_lt; omega⟩

/-- The low digit of a byte. -/
private def lowDigit (b : UInt8) : Fin 16 := ⟨b.toNat % 16, by omega⟩

/-- The decoder reads back the bytes of their hex encoding.

This holds whether or not it accepts uppercase digits. -/
theorem bytesOf_hexString (what : String) (upper : Bool) (data : List UInt8) :
    bytesOf what upper (.str (hexString data)) = .ok data.toByteArray := by
  unfold bytesOf
  rw [hexDigits_hexString]
  simp only [bind, Except.bind, pure, Except.pure]
  have hflat : data.flatMap byteHexDigits =
      data.flatMap fun b => [hexDigitChar (highDigit b), hexDigitChar (lowDigit b)] := rfl
  have hidx : ∀ i, ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8)[2 * i]? =
        data[i]?.map (fun b => (hexDigitChar (highDigit b)).val.toUInt8) ∧
      ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8)[2 * i + 1]? =
        data[i]?.map (fun b => (hexDigitChar (lowDigit b)).val.toUInt8) := by
    intro i
    rw [hflat, List.getElem?_map, List.getElem?_map]
    obtain ⟨h1, h2⟩ := flatMap_pair_getElem? (fun b => hexDigitChar (highDigit b))
      (fun b => hexDigitChar (lowDigit b)) data i
    rw [h1, h2]
    simp only [Option.map_map]
    exact ⟨rfl, rfl⟩
  have hlen : ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8).length =
      2 * data.length := by
    rw [List.length_map, hflat, List.length_flatMap]
    simp
    exact sum_two data
  generalize hds : (data.flatMap byteHexDigits).map (fun c => c.val.toUInt8) = ds at hidx hlen ⊢
  have hsz : ds.toByteArray.size = 2 * data.length := by simpa using hlen
  have hne : ¬ (ds.toByteArray.size % 2 ≠ 0) := by omega
  simp only [hne, ↓reduceIte]
  rw [show ds.toByteArray.size / 2 = data.length by omega]
  have hr : List.range' [:data.length].start [:data.length].size [:data.length].step =
      List.range' 0 data.length 1 := by
    rw [show [:data.length].size = data.length by simp [Std.Legacy.Range.size]]
  rw [Std.Legacy.Range.forIn_eq_forIn_range', hr,
    forIn_range'_push (fun i => data.getD i 0) ?_]
  · show Except.ok _ = Except.ok _
    congr 1
    apply ByteArray.ext
    simp only [ByteArray.data_append, List.data_toByteArray]
    have hm : (List.range' 0 data.length).map (fun i => data.getD i 0) = data := by
      apply List.ext_getElem (by simp)
      intro n h1 h2
      simp [List.getD_eq_getElem?_getD, h2]
    rw [hm]
    simp [ByteArray.emptyWithCapacity]
    rfl
  · intro i out hi
    rw [List.mem_range'_1] at hi
    have hi' : i < data.length := by omega
    have e : ∀ j : Nat, ds.toByteArray[j]? = ds[j]? := by
      intro j
      rw [getElem?_def, getElem?_def]
      simp
    obtain ⟨h0, h1⟩ := hidx i
    rw [e, e, h0, h1, List.getElem?_eq_getElem hi']
    simp only [Option.map_some]
    have hv1 := hexValue_hexDigitChar upper (highDigit data[i])
    have hv2 := hexValue_hexDigitChar upper (lowDigit data[i])
    simp only [Char.toUInt8] at hv1 hv2
    rw [hv1, hv2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    exact congrArg (fun x => Except.ok (ForInStep.yield (out.push x))) (byte_split data[i])

/-- The decoder of byte strings reads back the bytes of their hex encoding. -/
theorem bytes_hexString (what : String) (data : List UInt8) :
    bytes what (.str (hexString data)) = .ok data.toByteArray :=
  bytesOf_hexString what false data

/-- The decoder of byte strings of a size reads back the bytes of their hex encoding. -/
theorem fixed_hexString (what : String) (n : Nat) (v : Vector UInt8 n) (upper : Bool) :
    fixed what n (.str (hexString v.toList)) upper = .ok v := by
  unfold fixed
  rw [bytesOf_hexString]
  simp only [bind, Except.bind]
  have h : (v.toList.toByteArray).data.size = n := by simp
  simp only [h, ↓reduceDIte]
  simp only [pure, Except.pure]
  congr 1
  exact Vector.toArray_inj.mp (by
    simp only [List.data_toByteArray]
    rw [← Vector.toArray_toList])

/-- A field of an object decodes to a value exactly when the object holds it under that name. -/
theorem field_eq_ok_iff {what name : String} {fs : List (String × Lean.Json)} {v : Lean.Json} :
    field what fs name = .ok v ↔ fs.lookup name = some v := by
  unfold field
  cases h : fs.lookup name <;>
    simp [pure, Except.pure, invalid, throw, throwThe, MonadExceptOf.throw]

/-- A withdrawal decodes exactly when its object holds exactly its four fields.

Its index, validator index and amount must decode as 64-bit numbers, and its address as 20 bytes.

Each becomes that field of the withdrawal. -/
theorem withdrawal_eq_ok_iff {j : Lean.Json} {w : Execution.Blocks.Withdrawal} :
    withdrawal j = .ok w ↔
      ∃ fs, fields "withdrawal" j = .ok fs ∧
        hasExactly fs ["index", "validatorIndex", "address", "amount"] = true ∧
        ∃ index validator recipient amount, fs.lookup "index" = some index ∧
          fs.lookup "validatorIndex" = some validator ∧ fs.lookup "address" = some recipient ∧
          fs.lookup "amount" = some amount ∧
          uint64 "index" index = .ok w.index ∧
          uint64 "validatorIndex" validator = .ok w.validatorIndex ∧
          address "address" recipient = .ok w.address ∧
          uint64 "amount" amount = .ok w.amount := by
  unfold withdrawal
  simp only [bind_ok_iff]
  constructor
  · rintro ⟨fs, hfs, h⟩
    by_cases hc : hasExactly fs ["index", "validatorIndex", "address", "amount"] = true
    · rw [ite_eq_left hc] at h
      simp only [bind_ok_iff, field_eq_ok_iff] at h
      obtain ⟨i, hl1, i', hf1, v, hl2, v', hf2, a, hl3, a', hf3, m, hl4, m', hf4, hw⟩ := h
      cases hw
      exact ⟨fs, hfs, hc, i, v, a, m, hl1, hl2, hl3, hl4, hf1, hf2, hf3, hf4⟩
    -- An object with other fields fails with an invalid parameter, never with a withdrawal.
    · rw [ite_eq_right hc, bind_ok_iff] at h
      obtain ⟨_, hInvalid, -⟩ := h
      cases hInvalid
  · rintro ⟨fs, hfs, hc, i, v, a, m, hl1, hl2, hl3, hl4, hf1, hf2, hf3, hf4⟩
    refine ⟨fs, hfs, ?_⟩
    rw [ite_eq_left hc]
    simp only [bind_ok_iff, field_eq_ok_iff]
    exact ⟨i, hl1, _, hf1, v, hl2, _, hf2, a, hl3, _, hf3, m, hl4, _, hf4, rfl⟩

end EthLib.Engine.Json
