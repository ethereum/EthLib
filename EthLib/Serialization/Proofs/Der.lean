module

public import EthLib.Serialization.Der
public import EthLib.Base.Except
public import EthLib.Base.Proofs.BigEndian

/-!
# DER reader checks

A successful typed read has the requested tag and a complete read consumes its input.

The reader is stated against X.690 itself, in terms of octets and numbers.

- A read is exactly a low-number tag octet other than 0, the shortest length, the content, the rest.
- So a tag and a content have a single encoding.
- An INTEGER reads as `i` exactly when its content is `i` in two's complement on the fewest octets.
- So an integer has a single content.
- A nonnegative one is its big-endian octets, at least one, after a zero if the top bit is set.
-/

@[expose] public section

namespace EthLib.Serialization.Proofs.Der

open EthLib.Serialization.Der
open EthLib.Base

/-- A typed read succeeds only with the requested tag and the underlying reader's result. -/
theorem readTag_ok_iff {tag : UInt8} {input rest : ByteArray} {value : Value} :
    readTag tag input = .ok (value, rest) ↔
      read input = .ok (value, rest) ∧ value.tag = tag := by
  simp only [readTag, bind_ok_iff]
  constructor
  · rintro ⟨⟨v, r⟩, parsed, checked⟩
    split at checked
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨parsed, ‹v.tag = tag›⟩
    · simp at checked
  · rintro ⟨parsed, same⟩
    exact ⟨(value, rest), parsed, by simp [same, pure, Except.pure]⟩

/-- An exact read succeeds only when no trailing bytes remain. -/
theorem exact_ok_iff {tag : UInt8} {input : ByteArray} {value : Value} :
    exact tag input = .ok value ↔
      ∃ rest, readTag tag input = .ok (value, rest) ∧ rest.isEmpty = true := by
  simp only [exact, bind_ok_iff]
  constructor
  · rintro ⟨⟨v, r⟩, parsed, checked⟩
    split at checked
    · simp only [pure, Except.pure, Except.ok.injEq] at checked
      subst v
      exact ⟨r, parsed, ‹r.isEmpty = true›⟩
    · simp at checked
  · rintro ⟨rest, parsed, empty⟩
    exact ⟨(value, rest), parsed, by simp [empty, pure, Except.pure]⟩

/-- An INTEGER whose zero sign byte is redundant is rejected for every remaining byte. -/
theorem integer_redundant_zero (next : UInt8) (rest : List UInt8)
    (small : next.toNat < 128) (encoded : ByteArray) :
    integer ⟨2, ⟨(0 :: next :: rest).toArray⟩, encoded⟩ = .error .value := by
  simp [integer, small, throw, throwThe, MonadExceptOf.throw,
    Functor.map, Except.map]

/-! ## The length octets -/

/-- A list of bytes in a byte array is the array. -/
private theorem byteArray_eq_of_toList {a b : ByteArray} (h : a.data.toList = b.data.toList) :
    a = b := ByteArray.ext (Array.toList_inj.mp h)

/-- The bytes of a slice are the bytes after its start, up to its end. -/
private theorem toList_extract (b : ByteArray) (x y : Nat) :
    (b.extract x y).data.toList = (b.data.toList.drop x).take (y - x) := by
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

/-- A read gives `value` and `rest` exactly when the input is the encoding of `value`, then `rest`.

The identifier is one octet whose five low bits are not all set (X.690 §8.1.2).

It is not zero, the identifier of the end-of-contents octets (X.690 §8.1.5).

The length is definite and on the fewest octets (X.690 §§8.1.3, 10.1).

A content of fewer than 128 octets has its length in one octet.

A longer content has an octet `129 + k`, then its length on `k + 1` big-endian octets.

Its length lies in `[256 ^ k, 256 ^ (k + 1))`, so the first of those octets is not zero.

`k` is below 126, because the initial octet 255 is reserved. -/
theorem read_ok_iff {input rest : ByteArray} {value : Value} :
    read input = .ok (value, rest) ↔
      value.tag.toNat % 32 ≠ 31 ∧ value.tag ≠ 0 ∧
      input.data.toList = value.encoded.data.toList ++ rest.data.toList ∧
      ((value.content.size < 128 ∧ value.encoded.data.toList =
          value.tag :: UInt8.ofNat value.content.size :: value.content.data.toList) ∨
        ∃ k, 256 ^ k ≤ value.content.size ∧ value.content.size < 256 ^ (k + 1) ∧ k < 126 ∧
          128 ≤ value.content.size ∧ value.encoded.data.toList =
            value.tag :: UInt8.ofNat (129 + k) ::
              (natToBytes (k + 1) value.content.size ++ value.content.data.toList)) := by
  constructor
  · intro h
    have hsz : input.size = input.data.toList.length := by rw [Array.length_toList]; rfl
    unfold EthLib.Serialization.Der.read at h
    generalize hL : input.data.toList = L at h hsz
    rcases L with _ | ⟨tag, _ | ⟨first, more⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h
    simp only at h
    by_cases ht : tag.toNat % 32 = 31 ∨ tag = 0
    · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    have hsize : ∀ x y, (input.extract x y).size = min y input.size - x := fun x y =>
      ByteArray.size_extract
    -- The short form gives the length in the second octet, the long form in the octets after it.
    by_cases hs : first.toNat < 128
    · simp [ht, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons] at hsz
      simp only [toList_extract, hL, hsize, hsz]
      have hm : min (2 + first.toNat) (more.length + 1 + 1) - 2 = first.toNat := by omega
      have e : 2 + first.toNat = first.toNat + 1 + 1 := by omega
      rw [hm, e]
      simp only [Nat.sub_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons,
        UInt8.ofNat_toNat]
      refine ⟨by omega, fun h => ht (.inr h), ?_, .inl ⟨hs, rfl⟩⟩
      rw [List.take_of_length_le (l := List.drop first.toNat more)
        (by simp only [List.length_drop]; omega)]
      simp
    · simp [ht, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure] at h
      have hf : first.toNat < 256 := first.toNat_lt
      split at h
      · cases h
      split at h
      · cases h
      rename_i hc hmore
      rcases htake : List.take (first.toNat - 128) more with _ | ⟨head, tail⟩
      · simp only [htake] at h
        cases h
      simp only [htake] at h
      split at h
      · cases h
      rename_i hhead
      split at h
      · cases h
      rename_i hn
      split at h
      · cases h
      rename_i hin
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [List.length_cons] at hsz
      simp only [toList_extract, hL, hsize, hsz]
      -- The length octets: `c` bytes, the first nonzero, worth `n`.
      have hlen : (head :: tail).length = first.toNat - 128 := by
        rw [← htake, List.length_take]; omega
      have hlo := bytesToNat_cons head tail
      have hhi := bytesToNat_lt (head :: tail)
      have hh : 1 ≤ head.toNat := by
        have : head.toNat ≠ 0 := fun h => hhead (UInt8.toNat_inj.mp h)
        omega
      have hpow : 256 ^ tail.length ≤ head.toNat * 256 ^ tail.length :=
        Nat.le_mul_of_pos_left _ hh
      generalize hnb : bytesToNat (head :: tail) = n at *
      obtain ⟨k, hk⟩ : ∃ k, first.toNat - 128 = k + 1 := ⟨first.toNat - 129, by omega⟩
      rw [hk] at hlen htake hin ⊢
      have hm : min (2 + (k + 1) + n) (more.length + 1 + 1) - (2 + (k + 1)) = n := by omega
      have e3 : 2 + (k + 1) + n - (2 + (k + 1)) = n := by omega
      have e : 2 + (k + 1) + n = (k + 1 + n) + 1 + 1 := by omega
      have e2 : 2 + (k + 1) = (k + 1) + 1 + 1 := by omega
      rw [hm, e3, e, e2]
      simp only [Nat.sub_zero, List.drop_zero, List.take_succ_cons, List.drop_succ_cons]
      have htl : tail.length = k := by simp at hlen; omega
      have hfirst : UInt8.ofNat (129 + k) = first := by
        apply UInt8.toNat_inj.mp
        simp only [UInt8.toNat_ofNat']
        omega
      have hbytes : natToBytes (k + 1) n = List.take (k + 1) more := by
        rw [htake, ← hnb, ← hlen, natToBytes_bytesToNat]
      refine ⟨fun h => ht (.inl h), fun h => ht (.inr h), ?_,
        .inr ⟨k, ?_, ?_, ?_, by omega, ?_⟩⟩
      · rw [List.take_of_length_le (l := List.drop (k + 1 + n) more) (by
          simp only [List.length_drop]; omega)]
        simp
      · rw [← htl]; omega
      · simpa [hlen] using hhi
      · omega
      · rw [hfirst, hbytes, List.take_add]
  · rintro ⟨ht1, ht0, hin, hcases⟩
    obtain ⟨tag, content, encoded⟩ := value
    simp only at *
    have hsz : input.size = input.data.toList.length := by rw [Array.length_toList]; rfl
    have hcs : content.size = content.data.toList.length := by rw [Array.length_toList]; rfl
    generalize hC : content.data.toList = C at *
    generalize hR : rest.data.toList = R at *
    have hext : ∀ x y,
        (input.extract x y).data.toList = (input.data.toList.drop x).take (y - x) :=
      fun x y => toList_extract input x y
    -- Run the reader on the encoding, in the short form and then in the long form.
    rcases hcases with ⟨hs, he⟩ | ⟨k, hlo, hhi, hk, h128, he⟩
    · rw [he] at hin
      have hfirst : (UInt8.ofNat content.size).toNat = content.size := by
        simp only [UInt8.toNat_ofNat']; omega
      unfold EthLib.Serialization.Der.read
      rw [hin]
      simp only [List.cons_append]
      simp [ht1, ht0, hfirst, hs, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure]
      have hnot : ¬ input.size < 2 + content.size := by rw [hsz, hin]; simp; omega
      have e : 2 + C.length = C.length + 1 + 1 := by omega
      simp only [hnot, ite_false, Except.ok.injEq, Prod.mk.injEq, Value.mk.injEq, true_and]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply byteArray_eq_of_toList <;>
        simp [hin, hC, hR, he, hcs, hsz, e]
    · rw [he] at hin
      have hfirst : (UInt8.ofNat (129 + k)).toNat = 129 + k := by
        simp only [UInt8.toNat_ofNat']; omega
      -- The length octets: the first is the quotient by `256 ^ k`, which is not zero.
      have hpos : 0 < 256 ^ k := Nat.pow_pos (by decide)
      have hq1 : 1 ≤ content.size / 256 ^ k := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
      have hq2 : content.size / 256 ^ k < 256 :=
        (Nat.div_lt_iff_lt_mul hpos).mpr (by rw [Nat.pow_succ] at hhi; omega)
      have hsplit : natToBytes (k + 1) content.size =
          UInt8.ofNat (content.size / 256 ^ k) :: natToBytes k content.size := by
        rw [Nat.add_comm, natToBytes_add, natToBytes_succ, natToBytes_zero, List.nil_append,
          Nat.mod_eq_of_lt hq2]
        rfl
      have hhead : UInt8.ofNat (content.size / 256 ^ k) ≠ 0 := by
        intro h
        have := congrArg UInt8.toNat h
        simp only [UInt8.toNat_ofNat'] at this
        simp at this
        omega
      have hval : bytesToNat (natToBytes (k + 1) content.size) = content.size :=
        bytesToNat_natToBytes_of_lt hhi
      rw [hsplit] at hin he hval
      have hnot : ¬ input.size < 2 + (k + 1) + content.size := by
        rw [hsz, hin]
        simp [natToBytes_length, ← hcs]
        omega
      unfold EthLib.Serialization.Der.read
      rw [hin]
      simp only [List.cons_append]
      simp [ht1, ht0, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure]
      have htk : List.take (k + 1) (UInt8.ofNat (content.size / 256 ^ k) ::
          (natToBytes k content.size ++ (C ++ R))) =
          UInt8.ofNat (content.size / 256 ^ k) :: natToBytes k content.size := by
        rw [List.take_succ_cons, List.take_left' (natToBytes_length k _)]
      simp only [show (129 + k) % 256 = 129 + k by omega, show 129 + k - 128 = k + 1 by omega,
        htk, hhead, hval, hnot]
      have a3 : ¬ (natToBytes k content.size).length + (C.length + R.length) + 1 < k + 1 := by
        rw [natToBytes_length]; omega
      simp only [show ¬ 129 + k < 128 by omega, show ¬ (k + 1 = 0 ∨ k + 1 = 127) by omega, a3,
        show ¬ content.size < 128 by omega, ite_false]
      simp only [Except.ok.injEq, Prod.mk.injEq, Value.mk.injEq, true_and]
      have e : 2 + (k + 1) = k + 1 + 1 + 1 := by omega
      rw [e]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply byteArray_eq_of_toList <;> rw [hext, hin]
      · simp [hC, hcs, List.drop_left' (natToBytes_length k _)]
      · have e2 : k + 1 + 1 + 1 + content.size = k + content.size + 1 + 1 + 1 := by omega
        have hl : (natToBytes k content.size ++ C).length = k + content.size := by
          simp [natToBytes_length, hcs]
        simp only [Nat.sub_zero, List.drop_zero, he, e2, List.take_succ_cons, List.cons_append,
          ← hl, List.take_left']
      · have e2 : k + 1 + 1 + 1 + content.size = k + content.size + 1 + 1 + 1 := by omega
        have hl : (natToBytes k content.size ++ C).length = k + content.size := by
          simp [natToBytes_length, hcs]
        rw [hR, hsz, hin, e2]
        simp only [List.drop_succ_cons, List.cons_append, ← hl,
          List.drop_left']
        exact List.take_of_length_le (by simp; omega)

/-- Two reads of one tag and one content have one encoding, so each value has a single header. -/
theorem encoded_eq_of_read_ok {a b rest rest' : ByteArray} {v w : Value}
    (ha : read a = .ok (v, rest)) (hb : read b = .ok (w, rest')) (tag : v.tag = w.tag)
    (content : v.content = w.content) : v.encoded = w.encoded := by
  obtain ⟨-, -, -, hv⟩ := read_ok_iff.mp ha
  obtain ⟨-, -, -, hw⟩ := read_ok_iff.mp hb
  rw [tag, content] at hv
  apply byteArray_eq_of_toList
  rcases hv with ⟨hs, hv⟩ | ⟨k, lo, hi, -, h128, hv⟩ <;>
    rcases hw with ⟨hs', hw⟩ | ⟨l, lo', hi', -, h128', hw⟩
  · rw [hv, hw]
  · omega
  · omega
  · -- The length lies in `[256 ^ k, 256 ^ (k + 1))` for one `k` only.
    have hkl : k = l := by
      rcases Nat.lt_trichotomy k l with h | h | h
      · have := Nat.pow_le_pow_right (show 0 < 256 by decide) h
        omega
      · exact h
      · have := Nat.pow_le_pow_right (show 0 < 256 by decide) h
        omega
    rw [hv, hw, hkl]

/-! ## INTEGER -/

/-- A power of 256 in the integers is the cast of the natural power. -/
private theorem natCast_pow_256 (n : Nat) : (256 : Int) ^ n = ((256 ^ n : Nat) : Int) := by
  rw [Int.natCast_pow]; rfl

/-- Modulo `M`, an integer in `[-M/2, M/2)` is itself, or `M` above itself if negative. -/
private theorem emod_cases {i M : Int} (lo : -M ≤ 2 * i) (hi : 2 * i < M) :
    (0 ≤ i ∧ i % M = i) ∨ (i < 0 ∧ i % M = i + M) := by
  by_cases h : 0 ≤ i
  · exact .inl ⟨h, Int.emod_eq_of_lt h (by omega)⟩
  · refine .inr ⟨by omega, ?_⟩
    rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]

/-- Bytes with no redundant sign octet read as `i` exactly when they hold `i` on the fewest octets.
-/
private theorem twos_complement_iff (first : UInt8) (rest : List UInt8) (i : Int) :
    ((∀ next tail, rest = next :: tail →
        ¬ ((first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat))) ∧
      i = if first.toNat < 128 then (bytesToNat (first :: rest) : Int)
        else bytesToNat (first :: rest) - 256 ^ (rest.length + 1)) ↔
    ∃ k : Nat, -(128 * 256 ^ k : Int) ≤ i ∧ i < 128 * 256 ^ k ∧
      (∀ j < k, i < -(128 * 256 ^ j : Int) ∨ 128 * 256 ^ j ≤ i) ∧
      first :: rest = natToBytes (k + 1) (i % 256 ^ (k + 1)).toNat := by
  have hN := bytesToNat_cons first rest
  have hR := bytesToNat_lt rest
  have hf : first.toNat < 256 := first.toNat_lt
  have mulQ : ∀ a b, a ≤ b → a * 256 ^ rest.length ≤ b * 256 ^ rest.length :=
    fun a b h => Nat.mul_le_mul_right _ h
  -- The second byte, when there is one, is worth `256 ^ (k - 1)` per unit.
  have hsecond : ∀ next tail, rest = next :: tail →
      bytesToNat rest = next.toNat * 256 ^ tail.length + bytesToNat tail ∧
      bytesToNat tail < 256 ^ tail.length ∧ 256 ^ rest.length = 256 * 256 ^ tail.length ∧
      (∀ a b, a ≤ b → a * 256 ^ tail.length ≤ b * 256 ^ tail.length) := by
    rintro next tail rfl
    exact ⟨bytesToNat_cons next tail, bytesToNat_lt tail, by
      rw [List.length_cons, Nat.pow_succ, Nat.mul_comm], fun a b h => Nat.mul_le_mul_right _ h⟩
  have hsmall : ∀ j < rest.length, ∀ tail : List UInt8, rest.length = tail.length + 1 →
      256 ^ j ≤ 256 ^ tail.length := fun j hj tail ht =>
    Nat.pow_le_pow_right (by decide) (by omega)
  simp only [natCast_pow_256, Nat.pow_succ]
  constructor
  · rintro ⟨nr, hi⟩
    refine ⟨rest.length, ?_⟩
    have hrange : -(128 * ((256 ^ rest.length : Nat) : Int)) ≤ i ∧
        i < 128 * ((256 ^ rest.length : Nat) : Int) := by
      split at hi
      · have := mulQ first.toNat 127 (by omega)
        omega
      · have := mulQ 128 first.toNat (by omega)
        have := mulQ first.toNat 255 (by omega)
        omega
    have hmod : (i % ((256 ^ rest.length * 256 : Nat) : Int)).toNat =
        bytesToNat (first :: rest) := by
      have := mulQ first.toNat 255 (by omega)
      rcases emod_cases (i := i) (M := ((256 ^ rest.length * 256 : Nat) : Int))
        (by omega) (by omega) with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] <;> split at hi <;> omega
    refine ⟨hrange.1, hrange.2, ?_, ?_⟩
    · intro j hj
      rcases rest with _ | ⟨next, tail⟩
      · simp at hj
      · obtain ⟨hr, ht, hq, mulP⟩ := hsecond next tail rfl
        have hjP := hsmall j hj tail rfl
        have hnr := nr next tail rfl
        suffices i < -(128 * ((256 ^ tail.length : Nat) : Int)) ∨
            128 * ((256 ^ tail.length : Nat) : Int) ≤ i by omega
        split at hi
        · by_cases h0 : first = 0
          · subst h0
            have : 128 ≤ next.toNat := by simp at hnr; omega
            have := mulP 128 next.toNat this
            omega
          · have : first.toNat ≠ 0 := fun h => h0 (UInt8.toNat_inj.mp h)
            have := mulQ 1 first.toNat (by omega)
            omega
        · by_cases h255 : first = 255
          · subst h255
            have : next.toNat < 128 := by simp at hnr; omega
            have := mulP next.toNat 127 (by omega)
            have := mulQ 255 255 (by omega)
            simp at hN
            omega
          · have : first.toNat ≠ 255 := fun h => h255 (UInt8.toNat_inj.mp h)
            have := mulQ first.toNat 254 (by omega)
            omega
    · rw [hmod]
      exact (natToBytes_bytesToNat (first :: rest)).symm
  · rintro ⟨k, lo, hi, hmin, hc⟩
    have hk : k = rest.length := by
      have := congrArg List.length hc
      rw [natToBytes_length, List.length_cons] at this
      omega
    subst hk
    -- The bytes hold `i` modulo `256 ^ (k + 1)`, which is `i` or `i + 256 ^ (k + 1)`.
    have hval :
        bytesToNat (first :: rest) = (i % ((256 ^ rest.length * 256 : Nat) : Int)).toNat := by
      rw [hc, bytesToNat_natToBytes_of_lt]
      rcases emod_cases (i := i) (M := ((256 ^ rest.length * 256 : Nat) : Int))
        (by omega) (by omega) with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h, Nat.pow_succ] <;> omega
    have hcase := emod_cases (i := i) (M := ((256 ^ rest.length * 256 : Nat) : Int))
      (by omega) (by omega)
    refine ⟨?_, ?_⟩
    · rintro next tail rfl hred
      obtain ⟨hr, ht, hq, mulP⟩ := hsecond next tail rfl
      have := hmin tail.length (by simp)
      rcases hred with ⟨rfl, hn⟩ | ⟨rfl, hn⟩
      · have := mulP next.toNat 127 (by omega)
        simp at hN
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega
      · have := mulP 128 next.toNat hn
        simp at hN
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega
    · split
      · have := mulQ first.toNat 127 (by omega)
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega
      · have := mulQ 128 first.toNat (by omega)
        rcases hcase with ⟨h0, h⟩ | ⟨h0, h⟩ <;> rw [h] at hval <;> omega

/-- An INTEGER reads as `i` exactly when its tag is 2 and its content is `i` on the fewest octets.

The octets are two's complement (X.690 §8.3.3).

The content is `i` modulo `256 ^ (k + 1)` on `k + 1` big-endian octets.

`i` lies in `[-(128 * 256 ^ k), 128 * 256 ^ k)`, the range of `k + 1` octets.

No shorter content holds `i`, so a first octet 0 or 255 is never redundant (X.690 §8.3.2). -/
theorem integer_ok_iff {value : Value} {i : Int} :
    integer value = .ok i ↔ value.tag = 2 ∧ ∃ k : Nat,
      -(128 * 256 ^ k : Int) ≤ i ∧ i < 128 * 256 ^ k ∧
      (∀ j < k, i < -(128 * 256 ^ j : Int) ∨ 128 * 256 ^ j ≤ i) ∧
      value.content.data.toList = natToBytes (k + 1) (i % 256 ^ (k + 1)).toNat := by
  unfold integer
  generalize hc : value.content.data.toList = c
  have hsize : value.content.size = c.length := by
    rw [← hc, Array.length_toList]
    rfl
  rw [hsize]
  by_cases ht : value.tag = 2
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    rcases c with _ | ⟨first, rest⟩
    · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_iff, not_exists,
        not_and]
      intro k _ _ _ h
      have := congrArg List.length h
      simp [natToBytes_length] at this
    rw [← twos_complement_iff]
    rcases rest with _ | ⟨next, tail⟩
    · simp [pure, Except.pure, eq_comm]
    · by_cases hr : (first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat)
      · simp only [hr, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
          reduceCtorEq, false_iff, not_and]
        intro h
        exact absurd hr (h next tail rfl)
      · have hnr : ∀ n t, next :: tail = n :: t →
            ¬ ((first = 0 ∧ n.toNat < 128) ∨ (first = 255 ∧ 128 ≤ n.toNat)) := by
          intro n t h
          cases h
          exact hr
        rw [and_iff_right hnr]
        simp [hr, pure, Except.pure, eq_comm]
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- Two INTEGERs that read as one value have one content. -/
theorem content_eq_of_integer_ok {v w : Value} {i : Int} (hv : integer v = .ok i)
    (hw : integer w = .ok i) : v.content = w.content := by
  obtain ⟨-, k, lo, hi, hmin, hc⟩ := integer_ok_iff.mp hv
  obtain ⟨-, l, lo', hi', hmin', hc'⟩ := integer_ok_iff.mp hw
  -- The fewest octets that hold `i` are one count, so both contents have it.
  have hkl : k = l := by
    rcases Nat.lt_trichotomy k l with h | h | h
    · rcases hmin' k h with h' | h' <;> omega
    · exact h
    · rcases hmin l h with h' | h' <;> omega
  subst hkl
  exact byteArray_eq_of_toList (hc.trans hc'.symm)

/-- A nonnegative INTEGER reads as `n` exactly when its tag is 2 and its content is `n` big-endian.

The content has the fewest octets that leave the top bit of the first clear (X.690 §§8.3.2, 8.3.3).

The content has `k + 1` octets, and `n` is below `128 * 256 ^ k`.

No shorter content holds `n`. -/
theorem natural_ok_iff {value : Value} {n : Nat} :
    natural value = .ok n ↔ value.tag = 2 ∧ ∃ k : Nat, n < 128 * 256 ^ k ∧
      (∀ j < k, 128 * 256 ^ j ≤ n) ∧ value.content.data.toList = natToBytes (k + 1) n := by
  have hnat : natural value = .ok n ↔ integer value = .ok (n : Int) := by
    unfold natural
    cases h : integer value with
    | error e => simp [bind, Except.bind]
    | ok i =>
      by_cases hi : i < 0
      · simp only [bind, Except.bind, hi, ite_true, throw, throwThe, MonadExceptOf.throw,
          reduceCtorEq, false_iff, Except.ok.injEq]
        omega
      · simp only [bind, Except.bind, hi, ite_false, pure, Except.pure, Except.ok.injEq]
        omega
  rw [hnat, integer_ok_iff]
  simp only [natCast_pow_256]
  refine and_congr_right fun _ => exists_congr fun k => ?_
  -- A nonnegative value below `256 ^ (k + 1)` is its own residue.
  have hpow : 0 < 256 ^ k := Nat.pow_pos (by decide)
  constructor
  · rintro ⟨-, hi, hmin, hc⟩
    refine ⟨by omega, fun j hj => ?_, ?_⟩
    · have := hmin j hj
      omega
    · rw [hc, Int.emod_eq_of_lt (by omega) (by rw [Nat.pow_succ]; omega)]
      rfl
  · rintro ⟨hi, hmin, hc⟩
    refine ⟨by omega, by omega, fun j hj => .inr (by have := hmin j hj; omega), ?_⟩
    rw [hc, Int.emod_eq_of_lt (by omega) (by rw [Nat.pow_succ]; omega)]
    rfl

end EthLib.Serialization.Proofs.Der
