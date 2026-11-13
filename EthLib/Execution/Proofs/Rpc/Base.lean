module

public import EthLib.Execution.Rpc.Base
public import EthLib.Serialization.Proofs.JsonRpc
import EthLib.Base.Proofs.BigEndian
-- The hex digits of a number must unfold for the decision procedure to read them.
import all Init.Data.Repr

/-!
# Proofs: the base types of the execution JSON-RPC API

Each reader of a base type reads back what its writer writes.

A byte reads back from the digits of its value, and a decimal number from its decimal digits.

The 32-bit and 256-bit numbers read back from their quantities.

A storage slot reads back from the hex digits of its 32 bytes.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc

/-- The hex digits of a byte are one or two ASCII characters, and they read back as the byte. -/
private theorem byte_digits : ∀ n, n < 256 →
    (∀ c ∈ Nat.toDigits 16 n, c.val ≤ 0x7F) ∧
      (0 < (Nat.toDigits 16 n).length ∧ (Nat.toDigits 16 n).length ≤ 2) ∧
      (∀ c ∈ (Nat.toDigits 16 n).map (fun c => c.val.toUInt8), (hexValue false c).isSome) ∧
      ((Nat.toDigits 16 n).map (fun c => c.val.toUInt8)).foldl
        (fun a c => 16 * a + (hexValue false c).getD 0) (0 : UInt8) = n.toUInt8 := by
  decide +kernel

/-- A loop whose step multiplies by sixteen and adds the digit of a code computes the fold. -/
private theorem forIn_byte {ds : List UInt8}
    {f : UInt8 → UInt8 → Except String (ForInStep UInt8)}
    (h : ∀ c ∈ ds, ∀ s, f c s = .ok (.yield (16 * s + (hexValue false c).getD 0)))
    (acc : UInt8) :
    forIn ds acc f = .ok (ds.foldl (fun a c => 16 * a + (hexValue false c).getD 0) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c ds ih =>
    rw [List.forIn_cons, h c (by simp) acc]
    exact ih (fun c' hc' s => h c' (by simp [hc']) s) _

/-- The reader of bytes reads back the byte that its writer writes. -/
theorem byte_byteJson (what : String) (b : UInt8) : byte what (byteJson b) = .ok b := by
  have hb := b.toNat_lt
  obtain ⟨hascii, ⟨hpos, hle⟩, hsome, hfold⟩ := byte_digits b.toNat hb
  unfold byteJson quantityJson
  unfold byte
  rw [hexDigits_ascii _ _ hascii]
  simp only [bind, Except.bind]
  have hsize : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 b.toNat)).toByteArray.size =
      (Nat.toDigits 16 b.toNat).length := by simp
  rw [ite_eq_right (by rw [hsize]; omega)]
  rw [forIn_eq_forIn_toList]
  have hdata : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 b.toNat)).toByteArray.data.toList
      = List.map (fun c => c.val.toUInt8) (Nat.toDigits 16 b.toNat) := by simp
  rw [hdata, forIn_byte, hfold]
  · simp
    rfl
  · intro c hc s
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hsome c hc)
    simp [hd]
    rfl

/-- Each decimal digit of a number is an ASCII digit whose code gives its value. -/
private theorem digitChar_dec : ∀ d, d < 10 →
    (Nat.digitChar d).val ≤ 0x7F ∧ 48 ≤ (Nat.digitChar d).val.toUInt8 ∧
      (Nat.digitChar d).val.toUInt8 ≤ 57 ∧
      ((Nat.digitChar d).val.toUInt8 - 48).toNat = d ∧ (0 < d → Nat.digitChar d ≠ '0') := by
  decide

/-- The decimal digits of a number are ASCII digits whose values, read from the first, give it.

A positive number does not start with the digit `0`. -/
private theorem toDigits_dec (n : Nat) :
    (∀ c ∈ Nat.toDigits 10 n, ∃ d, d < 10 ∧ c = Nat.digitChar d) ∧
      ((Nat.toDigits 10 n).map fun c => c.val.toUInt8).foldl
        (fun acc c => 10 * acc + (c - 48).toNat) 0 = n ∧
      (0 < n → (Nat.toDigits 10 n).head? ≠ some '0') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide : 1 < 10)]
    split
    · rename_i hn
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        exact ⟨n, hn, by simpa using hc⟩
      · simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        rw [(digitChar_dec n hn).2.2.2.1]
        omega
      · intro hpos
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact (digitChar_dec n hn).2.2.2.2 hpos
    · rename_i hn
      have hq : n / 10 < n := by omega
      obtain ⟨hall, hval, hhead⟩ := ih (n / 10) hq
      refine ⟨?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hall c hc
        · exact ⟨n % 10, by omega, by simpa using hc⟩
      · rw [List.map_append, List.foldl_append, hval]
        simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
        rw [(digitChar_dec (n % 10) (by omega)).2.2.2.1]
        omega
      · intro _
        have hne := Nat.toDigits_ne_nil (b := 10) (n := n / 10)
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        have := hhead (by omega)
        rw [hx] at this ⊢
        simpa using this

/-- A loop whose step multiplies by ten and adds the value of a digit code computes the fold. -/
private theorem forIn_dec {ds : List UInt8}
    {f : UInt8 → Nat → Except String (ForInStep Nat)}
    (h : ∀ c ∈ ds, ∀ s, f c s = .ok (.yield (10 * s + (c - 48).toNat))) (acc : Nat) :
    forIn ds acc f = .ok (ds.foldl (fun a c => 10 * a + (c - 48).toNat) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c ds ih =>
    rw [List.forIn_cons, h c (by simp) acc]
    exact ih (fun c' hc' s => h c' (by simp [hc']) s) _

/-- The reader of 32-bit numbers reads back the quantity of any 32-bit number. -/
theorem uint32_quantityJson (what : String) (x : UInt32) :
    uint32 what (quantityJson x.toNat) = .ok x := by
  unfold uint32
  rw [quantity_toDigits what (bits := 32) (by simpa using x.toNat_lt)]
  simp [bind, Except.bind, pure, Except.pure]

/-- The reader of 256-bit numbers reads back the quantity of any 256-bit number. -/
theorem uint256_quantityJson (what : String) (x : U256) :
    uint256 what (quantityJson x.toNat) = .ok x := by
  unfold uint256
  rw [quantity_toDigits what (bits := 256) (by simpa using x.isLt)]
  simp [bind, Except.bind, pure, Except.pure]

/-- The reader of decimal numbers reads back the number that its writer writes. -/
theorem uintDecimal_uintDecimalJson (what : String) (n : Nat) :
    uintDecimal what (uintDecimalJson n) = .ok n := by
  obtain ⟨hall, hval, hhead⟩ := toDigits_dec n
  have hascii : ∀ c ∈ Nat.toDigits 10 n, c.val ≤ 0x7F := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := hall c hc
    exact (digitChar_dec d hd).1
  have hs : (String.ofList (Nat.toDigits 10 n)).toUTF8 =
      (List.map (fun c => c.val.toUInt8) (Nat.toDigits 10 n)).toByteArray := by
    rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, ascii_utf8Encode _ hascii]
  unfold uintDecimalJson uintDecimal
  simp only [hs, bind, Except.bind]
  have hne := Nat.toDigits_ne_nil (b := 10) (n := n)
  have hsize : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 10 n)).toByteArray.size =
      (Nat.toDigits 10 n).length := by simp
  rw [ite_eq_right (by rw [hsize]; exact fun h => hne (List.length_eq_zero_iff.mp h))]
  rw [ite_eq_right]
  · rw [forIn_eq_forIn_toList]
    have hdata : (List.map (fun c => c.val.toUInt8) (Nat.toDigits 10 n)).toByteArray.data.toList
        = List.map (fun c => c.val.toUInt8) (Nat.toDigits 10 n) := by simp
    rw [hdata, forIn_dec, hval]
    · rfl
    · intro c hc s
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      obtain ⟨d, hd, rfl⟩ := hall c' hc'
      obtain ⟨-, h1, h2, -, -⟩ := digitChar_dec d hd
      have h12 : 48 ≤ d.digitChar.toUInt8 ∧ d.digitChar.toUInt8 ≤ 57 := ⟨h1, h2⟩
      simp [h12]
      rfl
  · rintro ⟨hgt, hzero⟩
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
    rw [hx] at hzero hgt
    have hx48 : x.val.toUInt8 = 48 := by simpa using hzero
    obtain ⟨d, hd, rfl⟩ := hall x (by simp [hx])
    have hpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | hp
      · simp [Nat.toDigits_zero] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp at hgt
      · exact hp
    exact hhead hpos (by
      rw [hx]
      have key : ∀ d, d < 10 → (Nat.digitChar d).val.toUInt8 = 48 → Nat.digitChar d = '0' := by
        decide
      have h0 : Nat.digitChar d = '0' := key d hd hx48
      simp [h0])

/-- The two hex digits of each byte, read as one number, give the number that the bytes write. -/
private theorem foldl_byteHexDigits (data : List UInt8) (acc : Nat) :
    ((data.flatMap byteHexDigits).map fun c => c.val.toUInt8).foldl
        (fun a c => 16 * a + ((hexValue false c).getD 0).toNat) acc =
      data.foldl (fun a b => a * 256 + b.toNat) acc := by
  induction data generalizing acc with
  | nil => rfl
  | cons b data ih =>
    rw [List.flatMap_cons, List.map_append, List.foldl_append, List.foldl_cons, ← ih]
    have hv := fun n => hexValue_hexDigitChar false n
    simp only [Char.toUInt8] at hv
    simp only [byteHexDigits, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, hv,
      Option.getD_some]
    have hb := b.toNat_lt
    congr 1
    simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
    omega

/-- Byte `i` of a number written on `len` bytes is its digit worth `256 ^ (len - 1 - i)`. -/
theorem getElem_natToBytes {len n i : Nat} (hi : i < len) :
    (natToBytes len n)[i]'(by rw [natToBytes_length]; exact hi) =
      UInt8.ofNat (n / 256 ^ (len - 1 - i) % 256) := by
  have hsplit := natToBytes_add (i + 1) (len - 1 - i) n
  rw [show i + 1 + (len - 1 - i) = len by omega, natToBytes_succ] at hsplit
  simp only [hsplit]
  rw [List.getElem_append_left (by simp [natToBytes_length]),
    List.getElem_append_right (by simp [natToBytes_length])]
  simp [natToBytes_length]

/-- A loop whose step multiplies by sixteen and adds the value of a digit computes the fold. -/
theorem forIn_hex {ds : List UInt8}
    {f : UInt8 → Nat → Except String (ForInStep Nat)}
    (h : ∀ c ∈ ds, ∀ s, f c s = .ok (.yield (16 * s + ((hexValue false c).getD 0).toNat)))
    (acc : Nat) :
    forIn ds acc f =
      .ok (ds.foldl (fun a c => 16 * a + ((hexValue false c).getD 0).toNat) acc) := by
  induction ds generalizing acc with
  | nil => rfl
  | cons c ds ih =>
    rw [List.forIn_cons, h c (by simp) acc]
    exact ih (fun c' hc' s => h c' (by simp [hc']) s) _

/-- The reader of storage slots reads back the 32 bytes that the writer of bytes writes. -/
theorem bytesMax32_dataJson (what : String) (v : Bytes32) :
    bytesMax32 what (dataJson v.toList) = .ok v := by
  unfold bytesMax32 dataJson
  rw [hexDigits_hexString]
  simp only [bind, Except.bind]
  have hsize : ((v.toList.flatMap byteHexDigits).map fun c => c.val.toUInt8).toByteArray.size =
      64 := by
    simp [byteHexDigits, List.map_const']
  rw [ite_eq_right (by rw [hsize]; omega), forIn_eq_forIn_toList]
  have hdata : ((v.toList.flatMap byteHexDigits).map fun c => c.val.toUInt8).toByteArray.data.toList
      = (v.toList.flatMap byteHexDigits).map fun c => c.val.toUInt8 := by simp
  rw [hdata, forIn_hex, foldl_byteHexDigits]
  · simp only [pure, Except.pure, Except.ok.injEq]
    apply Vector.ext
    intro i hi
    have hv := natToBytes_bytesToNat v.toList
    simp only [Vector.length_toList] at hv
    rw [Vector.getElem_ofFn]
    have h := congrArg (·[i]?) hv
    rw [List.getElem?_eq_getElem (by rw [natToBytes_length]; exact hi), getElem_natToBytes hi,
      List.getElem?_eq_getElem (by simpa using hi), Option.some.injEq,
      Vector.getElem_toList] at h
    rw [← h]
    rfl
  · intro c hc s
    simp only [List.mem_map, List.mem_flatMap, byteHexDigits, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    obtain ⟨_, ⟨b, -, rfl | rfl⟩, rfl⟩ := hc <;>
    · have hv := hexValue_hexDigitChar false
      simp only [Char.toUInt8] at hv
      rw [hv]
      rfl

end EthLib.Execution.Rpc
