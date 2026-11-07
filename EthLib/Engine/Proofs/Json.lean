module

public import EthLib.Engine.Json
public import EthLib.Base.Hex
public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Bytes
-- The digits of `Nat.toDigits` must unfold for `decide` to read them.
import all Init.Data.Repr

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

A list decodes exactly when the value is an array whose items each decode, in order.

A byte string of a fixed size, such as an address, decodes exactly to the vector of its bytes.

A number below the bound, written in lowercase hex without leading zeros, decodes to itself.

No other text decodes to a number.

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

/-- The digits after the marker `0x` of an ASCII text are the codes of its characters. -/
private theorem hexDigits_ascii (what : String) (l : List Char) (h : ∀ c ∈ l, c.val ≤ 0x7F) :
    hexDigits what (.str ("0x" ++ String.ofList l)) =
      .ok (l.map fun c => c.val.toUInt8).toByteArray := by
  unfold hexDigits
  have hascii : ∀ c ∈ '0' :: 'x' :: l, c.val ≤ 0x7F := by
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · decide
    · decide
    · exact h c hc
  have hs : ("0x" ++ String.ofList l).toUTF8 =
      ('0'.val.toUInt8 :: 'x'.val.toUInt8 :: l.map fun c => c.val.toUInt8).toByteArray := by
    have : ("0x" ++ String.ofList l) = String.ofList ('0' :: 'x' :: l) := by
      apply String.ext; simp
    rw [this, String.toUTF8_eq_toByteArray, String.toByteArray_ofList, ascii_utf8Encode _ hascii]
    rfl
  simp only [hs]
  generalize l.map (fun c => c.val.toUInt8) = ds
  have h0 : '0'.val.toUInt8 = 48 := by decide
  have hx : 'x'.val.toUInt8 = 120 := by decide
  rw [h0, hx]
  have h1 : (48 :: 120 :: ds).toByteArray[0]? = some 48 := by simp
  have h2 : (48 :: 120 :: ds).toByteArray[1]? = some 120 := by simp
  simp only [h1, h2, and_self, ↓reduceIte]
  congr 1
  apply ByteArray.ext
  simp [ByteArray.data_extract]

/-- The digits after the marker `0x` of a hex encoding are the ASCII codes of its characters. -/
theorem hexDigits_hexString (what : String) (data : List UInt8) :
    hexDigits what (.str (hexString data)) =
      .ok ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8).toByteArray := by
  have htext : hexString data = "0x" ++ String.ofList (data.flatMap byteHexDigits) := by
    apply String.ext
    simp [toList_hexString]
  rw [htext]
  refine hexDigits_ascii what _ fun c hc => ?_
  simp only [List.mem_flatMap, byteHexDigits, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ⟨b, -, rfl | rfl⟩ <;> exact hexDigitChar_ascii _

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

/-- A list decodes exactly when the value is an array whose items each decode, in order.

Item `i` of the list is the decoded item `i` of the array. -/
theorem array_eq_ok_iff {α : Type} {what : String} {f : Lean.Json → Decode α} {j : Lean.Json}
    {l : List α} :
    array what f j = .ok l ↔
      ∃ items : Array Lean.Json, j = .arr items ∧
        ∃ h : l.length = items.size, ∀ (i : Nat) (hi : i < items.size), f items[i] = .ok l[i] := by
  cases j with
  | arr items =>
    simp only [array, Lean.Json.arr.injEq, exists_eq_left', mapM_eq_ok_iff]
    simp
  -- Any other JSON value is not an array, so the read fails at once.
  | _ => simp [array, invalid, throw, throwThe, MonadExceptOf.throw]

/-- A byte string of a fixed size decodes to a vector exactly when its bytes are the vector's.

The decoder of byte strings must then return exactly those bytes, so their number is the size. -/
theorem fixed_eq_ok_iff {what : String} {n : Nat} {j : Lean.Json} {upper : Bool}
    {v : Vector UInt8 n} :
    fixed what n j upper = .ok v ↔ bytesOf what upper j = .ok ⟨v.toArray⟩ := by
  unfold fixed
  constructor
  · intro h
    obtain ⟨b, hb, h⟩ := bind_ok_iff.mp h
    -- A string of another size fails, so the bytes have the size and form the vector.
    split at h
    · cases h
      rw [hb]
    · cases h
  · intro h
    rw [h]
    simp [bind, Except.bind, pure, Except.pure, v.size_toArray]

/-- An address decodes exactly when its bytes are the address's, with uppercase digits allowed. -/
theorem address_eq_ok_iff {what : String} {j : Lean.Json} {a : Address} :
    address what j = .ok a ↔ bytesOf what true j = .ok ⟨a.toArray⟩ :=
  fixed_eq_ok_iff

/-! ## A number written in hex -/

/-- The value of the code of a hex digit, or zero for any other code. -/
private def digitValue (c : UInt8) : Nat := ((hexValue false c).getD 0).toNat

/-- The digit that Lean core writes for a value below sixteen is the lowercase hex digit. -/
private theorem digitChar_eq_hexDigitChar : ∀ n (h : n < 16),
    Nat.digitChar n = hexDigitChar ⟨n, h⟩ := by
  decide

/-- Each digit that `Nat.toDigits 16` writes is a lowercase hex digit, read back as its value. -/
private theorem hexValue_digitChar (n : Nat) (hn : n < 16) :
    hexValue false (Nat.digitChar n).val.toUInt8 = some n.toUInt8 ∧
      (Nat.digitChar n).val ≤ 0x7F := by
  rw [digitChar_eq_hexDigitChar n hn]
  exact ⟨hexValue_hexDigitChar false ⟨n, hn⟩, hexDigitChar_ascii _⟩

/-- No digit of a positive value below sixteen is the digit `0`. -/
private theorem digitChar_ne_zero : ∀ n, n < 16 → 0 < n → ¬ Nat.digitChar n = '0' := by
  decide

/-- The hex digits of a number are ASCII digits whose values, read from the first, give the number.

A positive number does not start with the digit `0`. -/
private theorem toDigits_hex (n : Nat) :
    (∀ c ∈ Nat.toDigits 16 n, ∃ d, d < 16 ∧ c = Nat.digitChar d) ∧
      ((Nat.toDigits 16 n).map fun c => c.val.toUInt8).foldl
        (fun acc c => 16 * acc + digitValue c) 0 = n ∧
      (0 < n → (Nat.toDigits 16 n).head? ≠ some '0') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide : 1 < 16)]
    split
    · rename_i hn
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        exact ⟨n, hn, by simpa using hc⟩
      · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, digitValue]
        rw [(hexValue_digitChar n hn).1]
        simp [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n < 256)]
      · intro hpos
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact digitChar_ne_zero n hn hpos
    · rename_i hn
      have hq : n / 16 < n := by omega
      obtain ⟨hall, hval, hhead⟩ := ih (n / 16) hq
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hall c hc
        · exact ⟨n % 16, by omega, by simpa using hc⟩
      · rw [List.map_append, List.foldl_append, hval]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, digitValue]
        rw [(hexValue_digitChar (n % 16) (by omega)).1]
        simp [Nat.toUInt8_eq, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega : n % 16 < 256)]
        omega
      · intro _
        have hne := Nat.toDigits_ne_nil (b := 16) (n := n / 16)
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        have := hhead (by omega)
        rw [hx] at this ⊢
        simpa using this

/-- A digit whose code is that of `0` is the digit `0`. -/
private theorem digitChar_code_zero : ∀ n, n < 16 →
    (Nat.digitChar n).val.toUInt8 = 48 → Nat.digitChar n = '0' := by
  decide

/-- A loop whose step multiplies by sixteen and adds the value of a digit computes the fold. -/
private theorem forIn_digits {ds : List UInt8}
    {f : UInt8 → Nat → Except EngineError (ForInStep Nat)}
    (h : ∀ c ∈ ds, ∀ s, f c s = .ok (.yield (16 * s + digitValue c))) (acc : Nat) :
    forIn ds acc f = .ok (ds.foldl (fun a c => 16 * a + digitValue c) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c ds ih =>
    rw [List.forIn_cons, h c (by simp) acc]
    exact ih (fun c' hc' s => h c' (by simp [hc']) s) _

/-- The decoder of numbers reads back a number below its bound, written in lowercase hex.

The text is `0x` and the digits of the number, without leading zeros, and `0x0` for zero.

The converse also holds: no other text decodes to the number. -/
theorem quantity_toDigits (what : String) {bits v : Nat} (hv : v < 2 ^ bits) :
    quantity what bits (.str ("0x" ++ String.ofList (Nat.toDigits 16 v))) = .ok v := by
  obtain ⟨hall, hval, hhead⟩ := toDigits_hex v
  have hascii : ∀ c ∈ Nat.toDigits 16 v, c.val ≤ 0x7F := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := hall c hc
    exact (hexValue_digitChar d hd).2
  unfold quantity
  rw [hexDigits_ascii _ _ hascii]
  simp only [bind, Except.bind]
  have hne := Nat.toDigits_ne_nil (b := 16) (n := v)
  have hsize : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 v)).toByteArray.size =
      (Nat.toDigits 16 v).length := by simp
  -- There is at least one digit.
  rw [ite_eq_right (by rw [hsize]; exact fun h => hne (List.length_eq_zero_iff.mp h))]
  -- The first digit is `0` only for the number 0, which has no other digit.
  rw [ite_eq_right]
  · -- Every digit is read, and the digits give the number.
    rw [forIn_eq_forIn_toList]
    have hdata : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 v)).toByteArray.data.toList =
        List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 v) := by simp
    rw [hdata, forIn_digits, hval]
    · simp [hv, pure, Except.pure]
    · intro c hc s
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd, rfl⟩ := hall c' hc'
      simp only [digitValue, (hexValue_digitChar d hd).1, Option.getD_some]
      rfl
  · rintro ⟨hgt, hzero⟩
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    rw [hx] at hzero hgt
    have hx48 : x.val.toUInt8 = 48 := by simpa using hzero
    obtain ⟨d, hd, rfl⟩ := hall x (by simp [hx])
    have hpos : 0 < v := by
      rcases Nat.eq_zero_or_pos v with rfl | hp
      · simp [Nat.toDigits_zero] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp at hgt
      · exact hp
    exact hhead hpos (by rw [hx]; simp [digitChar_code_zero d hd hx48])

/-- The decoder of 64-bit numbers reads back any 64-bit number, written in lowercase hex. -/
theorem uint64_toDigits (what : String) (x : UInt64) :
    uint64 what (.str ("0x" ++ String.ofList (Nat.toDigits 16 x.toNat))) = .ok x :=
  uint64_eq_ok_iff.mpr (quantity_toDigits what x.toNat_lt)

/-! ## Only the canonical text decodes -/

/-- A code that the decoder reads as a hex digit is the code of the digit of its value. -/
private theorem digitChar_digitValue_lt : ∀ n, n < 256 →
    (hexValue false n.toUInt8).isSome = true →
    digitValue n.toUInt8 < 16 ∧ (Nat.digitChar (digitValue n.toUInt8)).val.toUInt8 = n.toUInt8 ∧
      (n.toUInt8 ≠ 48 → 0 < digitValue n.toUInt8) := by
  decide +kernel

private theorem digitChar_digitValue (c : UInt8) (h : (hexValue false c).isSome = true) :
    digitValue c < 16 ∧ (Nat.digitChar (digitValue c)).val.toUInt8 = c ∧
      (c ≠ 48 → 0 < digitValue c) := by
  have := digitChar_digitValue_lt c.toNat c.toNat_lt
  simp only [show c.toNat.toUInt8 = c from UInt8.ofNat_toNat] at this
  exact this h

/-- A loop whose step reads a hex digit and fails on any other code succeeds only on hex digits. -/
private theorem forIn_digits_ok {ds : List UInt8}
    {f : UInt8 → Nat → Except EngineError (ForInStep Nat)}
    (hf : ∀ c s r, f c s = .ok r → (hexValue false c).isSome = true ∧
      r = .yield (16 * s + digitValue c))
    {acc w : Nat} (h : forIn ds acc f = .ok w) :
    (∀ c ∈ ds, (hexValue false c).isSome = true) ∧
      w = ds.foldl (fun a c => 16 * a + digitValue c) acc := by
  induction ds generalizing acc with
  | nil => exact ⟨by simp, by cases h; rfl⟩
  | cons c ds ih =>
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_ok_iff.mp h
    obtain ⟨hc, rfl⟩ := hf c acc r hr
    obtain ⟨hall, hw⟩ := ih h
    exact ⟨fun c' hc' => (List.mem_cons.mp hc').elim (· ▸ hc) (hall c'), hw⟩

/-- Digits read from a positive first digit give a number at least that digit. -/
private theorem foldl_digits_pos {ds : List UInt8} {acc : Nat} (h : 0 < acc) :
    0 < ds.foldl (fun a c => 16 * a + digitValue c) acc := by
  induction ds generalizing acc with
  | nil => exact h
  | cons c ds ih => exact ih (by simp only; omega)

/-- Hex digits without a leading `0` are what `Nat.toDigits 16` writes for their value. -/
private theorem digits_canonical : ∀ (k : Nat) (ds : List UInt8), ds.length = k → ds ≠ [] →
    (∀ c ∈ ds, (hexValue false c).isSome = true) → (1 < ds.length → ds.head? ≠ some 48) →
    ds = (Nat.toDigits 16 (ds.foldl (fun a c => 16 * a + digitValue c) 0)).map
      fun c => c.val.toUInt8 := by
  intro k
  induction k with
  | zero => intro ds hk hne; exact absurd (List.length_eq_zero_iff.mp hk) hne
  | succ k ih =>
    intro ds hk hne hall hlead
    obtain ⟨l, c, rfl⟩ : ∃ l c, ds = l ++ [c] := by
      rcases List.eq_nil_or_concat ds with h | ⟨l, c, h⟩
      · exact absurd h hne
      · exact ⟨l, c, by simpa using h⟩
    have hc := digitChar_digitValue c (hall c (by simp))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases hl : l = []
    · -- One digit: its value is below sixteen and `Nat.toDigits` writes that digit.
      subst hl
      simp only [List.nil_append, List.foldl_nil, Nat.mul_zero, Nat.zero_add]
      rw [Nat.toDigits_eq_ite (by decide), ite_eq_left hc.1]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact hc.2.1.symm
    · -- Several digits: the first is not `0`, so the digits before the last give a positive number.
      obtain ⟨y, ys, hy⟩ := List.exists_cons_of_ne_nil hl
      have hy48 : y ≠ 48 := by
        have := hlead (by simp [hy])
        subst hy
        simpa using this
      have hpos : 0 < l.foldl (fun a c => 16 * a + digitValue c) 0 := by
        rw [hy, List.foldl_cons]
        have := (digitChar_digitValue y (hall y (by simp [hy]))).2.2 hy48
        exact foldl_digits_pos (by omega)
      have hih := ih l (by simp at hk; omega) hl (fun c' hc' => hall c' (by simp [hc']))
        (fun _ => by rw [hy]; simpa using hy48)
      generalize l.foldl (fun a c => 16 * a + digitValue c) 0 = n at hpos hih
      have hge : ¬ 16 * n + digitValue c < 16 := by omega
      rw [Nat.toDigits_eq_ite (by decide), ite_eq_right hge,
        show (16 * n + digitValue c) / 16 = n by omega,
        show (16 * n + digitValue c) % 16 = digitValue c by omega, List.map_append]
      congr 1
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      exact hc.2.1.symm

/-- A text from which the decoder reads digits is `0x` and the codes of those digits. -/
private theorem toUTF8_of_hexDigits {what s : String} {digits : ByteArray}
    (h : hexDigits what (.str s) = .ok digits) :
    s.toUTF8.data.toList = 48 :: 120 :: digits.data.toList := by
  unfold hexDigits at h
  dsimp only at h
  split at h
  · rename_i hm
    cases h
    obtain ⟨h0, h1⟩ := hm
    generalize s.toUTF8 = b at h0 h1 ⊢
    obtain ⟨arr⟩ := b
    obtain ⟨l⟩ := arr
    have hsize : (ByteArray.mk ⟨l⟩).size = l.length := rfl
    have hx : (ByteArray.mk ⟨l⟩).extract 2 (ByteArray.mk ⟨l⟩).size = ByteArray.mk ⟨l.drop 2⟩ := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract, hsize, List.extract_toArray]
      simp [List.take_of_length_le]
    rw [hx]
    -- The first two bytes are those of `0` and `x`.
    match l, h0, h1 with
    | x :: y :: rest, h0, h1 =>
      have e0 : (ByteArray.mk ⟨x :: y :: rest⟩)[0]? = some x := rfl
      have e1 : (ByteArray.mk ⟨x :: y :: rest⟩)[1]? = some y := rfl
      rw [e0] at h0
      rw [e1] at h1
      cases Option.some.inj h0
      cases Option.some.inj h1
      rfl
  · cases h

/-- The decoder of numbers returns a number exactly when the text is the canonical text of it.

That text is `0x` and the lowercase hex digits of the number, without leading zeros.

The number must also be below the bound of the decoder.

So uppercase digits, leading zeros, `0x` alone and any other text are rejected. -/
theorem quantity_eq_ok_iff {what : String} {bits : Nat} {j : Lean.Json} {v : Nat} :
    quantity what bits j = .ok v ↔
      v < 2 ^ bits ∧ j = .str ("0x" ++ String.ofList (Nat.toDigits 16 v)) := by
  constructor
  · intro h
    refine ⟨lt_of_quantity h, ?_⟩
    have h' := h
    unfold quantity at h'
    cases j with
    | str s =>
      obtain ⟨digits, hd, h'⟩ := bind_ok_iff.mp h'
      dsimp only at h'
      -- A text with no digits, or with a leading `0` before other digits, fails.
      split at h'
      · cases h'
      rename_i hsize
      split at h'
      · cases h'
      rename_i hlead
      -- The loop reads every digit, and the value it returns is the number.
      obtain ⟨w, hw, h'⟩ := bind_ok_iff.mp h'
      have hwv : w = v := by
        split at h'
        · cases h'; rfl
        · cases h'
      subst hwv
      rw [forIn_eq_forIn_toList] at hw
      obtain ⟨hall, hval⟩ := forIn_digits_ok (fun c s r hr => by
        cases hc : hexValue false c with
        | none => simp [hc, invalid, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hr
        | some d =>
          simp only [hc, pure, Except.pure, Except.ok.injEq] at hr
          exact ⟨rfl, by rw [← hr, digitValue, hc]; rfl⟩) hw
      -- Those digits are the canonical digits of the number.
      have hcanon := digits_canonical _ _ rfl
        (fun hnil => hsize (by simp [ByteArray.size, ← Array.length_toList, hnil]))
        hall
        (fun hlen hzero => hlead ⟨by simpa [ByteArray.size, ← Array.length_toList] using hlen,
          by obtain ⟨arr⟩ := digits; obtain ⟨l⟩ := arr; cases l with
            | nil => simp at hzero
            | cons x xs =>
              have hx : x = 48 := by simpa using hzero
              subst hx
              rfl⟩)
      rw [← hval] at hcanon
      -- So the text has the bytes of the canonical text, and is that text.
      have ht := toUTF8_of_hexDigits (hexDigits_ascii what (Nat.toDigits 16 w) fun c hc => by
        obtain ⟨d, hdl, rfl⟩ := (toDigits_hex w).1 c hc
        exact (hexValue_digitChar d hdl).2)
      have hs := toUTF8_of_hexDigits hd
      rw [List.data_toByteArray, ← hcanon, ← hs] at ht
      congr 1
      apply String.toByteArray_inj.mp
      rw [← String.toUTF8_eq_toByteArray, ← String.toUTF8_eq_toByteArray]
      exact ByteArray.ext (Array.ext' ht.symm)
    -- Any other JSON value is not a string, so the read fails at once.
    | _ =>
      obtain ⟨digits, hd, -⟩ := bind_ok_iff.mp h'
      simp [hexDigits, invalid, throw, throwThe, MonadExceptOf.throw] at hd
  · rintro ⟨hv, rfl⟩
    exact quantity_toDigits what hv

end EthLib.Engine.Json
