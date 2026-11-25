module

public import EthLib.Serialization.Der
public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.ByteOrder

/-!
# DER reader checks

This module proves what the DER reader accepts, value by value and type by type.

The reader is stated against X.690 itself, in terms of octets and numbers.

The ECDSA signature codec is checked against its own encoder, not against X.690.
-/

@[expose] public section

namespace EthLib.Serialization.Proofs.Der

open EthLib.Serialization.Der
open EthLib.Base

/-- Cutting a byte array past its end gives the same bytes as cutting at its end. -/
private theorem extract_min_size (a : ByteArray) (i j : Nat) :
    a.extract i (min j a.size) = a.extract i j := by
  ext1
  simp [Array.extract_eq_extract_right]
  omega

/-- A read at an offset is the read at the start of the bytes from that offset, shifted back. -/
private theorem readAt_shift (input : ByteArray) (pos : Nat) :
    readAt input pos =
      (fun r => (r.1, r.2 + pos)) <$> readAt (input.extract pos input.size) 0 := by
  have hE : (input.extract pos input.size).size = input.size - pos := by
    simp [ByteArray.size_extract]
  unfold readAt
  by_cases h : pos + 2 ≤ input.size
  · have h' : 0 + 2 ≤ (input.extract pos input.size).size := by rw [hE]; omega
    rw [dite_eq_left h, dite_eq_left h']
    simp only [ByteArray.getElem_extract, hE, Nat.sub_zero, Nat.zero_add,
      ByteArray.extract_extract, extract_min_size, Nat.add_assoc]
    simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map]
    generalize input[pos] = tag
    generalize input[pos + 1] = first
    generalize (input.extract (pos + 2) (pos + (2 + (first.toNat - 128)))).data.toList = B
    rcases B with _ | ⟨b, B⟩ <;>
      by_cases c1 : tag.toNat % 32 = 31 ∨ tag = 0 <;> simp only [c1, ite_true, ite_false] <;>
      by_cases c2 : first.toNat < 128 <;> simp only [c2, ite_true, ite_false] <;>
      simp_all <;> repeat (split <;> (try simp_all [Nat.add_comm]))
  · rw [dite_eq_right h, dite_eq_right (by rw [hE]; omega)]
    simp [hE, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map]

/-- The reader at offset 0 in its form on the list of the input's octets.

It reads the value at the start, then hands back a copy of the bytes after it. -/
theorem read_eq (input : ByteArray) : read input = (do
    match input.data.toList with
    | tag :: first :: rest =>
      if tag.toNat % 32 = 31 ∨ tag = 0 then throw (.tag none tag)
      let (length, header) ←
        if first.toNat < 128 then pure (first.toNat, 2)
        else do
          let count := first.toNat - 128
          if count = 0 ∨ count = 127 then throw (.length first)
          if rest.length < count then throw (.truncated (2 + count) input.size)
          let bytes := rest.take count
          match bytes with
          | [] => throw (.length first)
          | head :: _ =>
            if head = 0 then throw (.length first)
            let length := EthLib.Base.ByteOrder.ofBE bytes
            if length < 128 then throw (.length first)
            pure (length, 2 + count)
      if input.size < header + length then throw (.truncated (header + length) input.size)
      return (⟨tag, input.extract header (header + length),
        input.extract 0 (header + length)⟩, input.extract (header + length) input.size)
    | _ => throw (.truncated 2 input.size)
  : Except Error (Value × ByteArray)) := by
  unfold EthLib.Serialization.Der.read readAt
  have hsz : input.size = input.data.toList.length := by simp
  rcases hL : input.data.toList with _ | ⟨tag, _ | ⟨first, rest⟩⟩ <;> rw [hL] at hsz
  · simp at hsz
    simp [hsz, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp at hsz
    simp [hsz, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · have h0 : ∀ hh, input[0]'hh = tag := by
      intro hh; simp [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList, hL]
    have h1 : ∀ hh, input[0 + 1]'hh = first := by
      intro hh; simp [ByteArray.getElem_eq_getElem_data, ← Array.getElem_toList, hL]
    have hb : ∀ n, (input.extract (0 + 2) (0 + 2 + n)).data.toList = rest.take n := by
      intro n; simp [ByteArray.data_extract, hL]
    simp at hsz
    rw [dite_eq_left (by omega)]
    simp only [h0, h1, hb, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
      Except.pure, Nat.sub_zero, Nat.zero_add]
    have hl : input.size - 2 = rest.length := by omega
    simp only [hl]
    symm
    generalize List.take (first.toNat - 128) rest = B
    rcases B with _ | ⟨b, B⟩ <;> repeat (split <;> (try simp_all))

/-- The siblings from an offset are the siblings of the bytes from that offset. -/
private theorem goAt_shift (fuel : Nat) : ∀ (input : ByteArray) (pos : Nat),
    children.goAt fuel input pos = children.go fuel (input.extract pos input.size) := by
  induction fuel with
  | zero =>
    intro input pos
    simp only [children.go, children.goAt, ByteArray.size_extract, Nat.min_self, Nat.sub_zero,
      Nat.le_zero, Nat.sub_eq_zero_iff_le]
  | succ fuel ih =>
    intro input pos
    simp only [children.go, children.goAt, ByteArray.size_extract, Nat.min_self,
      Nat.le_zero, Nat.sub_eq_zero_iff_le]
    by_cases hp : input.size ≤ pos
    · simp [hp]
    · rw [readAt_shift]
      simp only [hp, ite_false]
      cases readAt (input.extract pos input.size) 0 with
      | error e => rfl
      | ok r =>
        obtain ⟨v, n⟩ := r
        simp only [Functor.map, Except.map, bind, Except.bind]
        rw [ih, ih, ByteArray.extract_extract, ByteArray.size_extract, Nat.min_self,
          Nat.add_comm n pos, show pos + (input.size - pos) = input.size by omega, Nat.min_self]

/-- With no fuel, the siblings of an empty input are none, and any other input is truncated. -/
theorem children_go_zero (input : ByteArray) :
    children.go 0 input = if input.isEmpty then .ok [] else .error (.truncated 2 input.size) := by
  simp [children.go, children.goAt, ByteArray.isEmpty]

/-- With fuel, the siblings are the value read first, then the siblings of the bytes after it. -/
theorem children_go_succ (fuel : Nat) (input : ByteArray) :
    children.go (fuel + 1) input = (do
      if input.isEmpty then return []
      let (value, rest) ← read input
      return value :: (← children.go fuel rest)) := by
  simp only [children.go, children.goAt, EthLib.Serialization.Der.read, ByteArray.isEmpty,
    Nat.le_zero, beq_iff_eq]
  cases readAt input 0 with
  | error e => rfl
  | ok r =>
    obtain ⟨v, n⟩ := r
    simp only [bind, Except.bind, pure, Except.pure]
    rw [goAt_shift, children.go]

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

The length is definite and on the fewest octets (X.690 §§8.1.3, 10.1). -/
theorem read_ok_iff {input rest : ByteArray} {value : Value} :
    read input = .ok (value, rest) ↔
      -- The identifier is one octet whose five low bits are not all set (X.690 §8.1.2).
      --
      -- It is not zero, the identifier of the end-of-contents octets (X.690 §8.1.5).
      value.tag.toNat % 32 ≠ 31 ∧ value.tag ≠ 0 ∧
      input.data.toList = value.encoded.data.toList ++ rest.data.toList ∧
      -- A content of fewer than 128 octets has its length in one octet.
      ((value.content.size < 128 ∧ value.encoded.data.toList =
          value.tag :: UInt8.ofNat value.content.size :: value.content.data.toList) ∨
        -- A longer content has an octet `129 + k`, then its length on `k + 1` big-endian octets.
        --
        -- Its length lies in `[256 ^ k, 256 ^ (k + 1))`, so the first of those octets is not zero.
        --
        -- `k` is below 126, because the initial octet 255 is reserved.
        ∃ k, 256 ^ k ≤ value.content.size ∧ value.content.size < 256 ^ (k + 1) ∧ k < 126 ∧
          128 ≤ value.content.size ∧ value.encoded.data.toList =
            value.tag :: UInt8.ofNat (129 + k) ::
              ((ByteOrder.toBE (k + 1) value.content.size).toList
                ++ value.content.data.toList)) := by
  constructor
  · intro h
    have hsz : input.size = input.data.toList.length := by rw [Array.length_toList]; rfl
    rw [read_eq] at h
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
      have hlo := ByteOrder.ofBE_cons head tail
      have hhi := ByteOrder.ofBE_lt (head :: tail)
      have hh : 1 ≤ head.toNat := by
        have : head.toNat ≠ 0 := fun h => hhead (UInt8.toNat_inj.mp h)
        omega
      have hpow : 256 ^ tail.length ≤ head.toNat * 256 ^ tail.length :=
        Nat.le_mul_of_pos_left _ hh
      generalize hnb : ByteOrder.ofBE (head :: tail) = n at *
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
      have hbytes : (ByteOrder.toBE (k + 1) n).toList = List.take (k + 1) more := by
        rw [htake, ← hnb, ← hlen, ByteOrder.toList_toBE_ofBE]
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
      rw [read_eq]
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
      have hsplit : (ByteOrder.toBE (k + 1) content.size).toList =
          UInt8.ofNat (content.size / 256 ^ k) :: (ByteOrder.toBE k content.size).toList := by
        rw [Nat.add_comm, ByteOrder.toList_toBE_add, ByteOrder.toList_toBE_succ,
          ByteOrder.toList_toBE_zero, List.nil_append,
          Nat.mod_eq_of_lt hq2]
        rfl
      have hhead : UInt8.ofNat (content.size / 256 ^ k) ≠ 0 := by
        intro h
        have := congrArg UInt8.toNat h
        simp only [UInt8.toNat_ofNat'] at this
        simp at this
        omega
      have hval : ByteOrder.ofBE ((ByteOrder.toBE (k + 1) content.size).toList) = content.size :=
        ByteOrder.ofBE_toBE_of_lt hhi
      rw [hsplit] at hin he hval
      have hnot : ¬ input.size < 2 + (k + 1) + content.size := by
        rw [hsz, hin]
        simp [← hcs]
        omega
      rw [read_eq]
      rw [hin]
      simp only [List.cons_append]
      simp [ht1, ht0, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure,
        Except.pure]
      have htk : List.take (k + 1) (UInt8.ofNat (content.size / 256 ^ k) ::
          ((ByteOrder.toBE k content.size).toList ++ (C ++ R))) =
          UInt8.ofNat (content.size / 256 ^ k) :: (ByteOrder.toBE k content.size).toList := by
        rw [List.take_succ_cons, List.take_left' (ByteOrder.length_toList_toBE k _)]
      simp only [show (129 + k) % 256 = 129 + k by omega, show 129 + k - 128 = k + 1 by omega,
        htk, hhead, hval, hnot]
      have a3 : ¬ k + (C.length + R.length) + 1 < k + 1 := by omega
      simp only [show ¬ 129 + k < 128 by omega, show ¬ (k + 1 = 0 ∨ k + 1 = 127) by omega, a3,
        show ¬ content.size < 128 by omega, ite_false]
      simp only [Except.ok.injEq, Prod.mk.injEq, Value.mk.injEq, true_and]
      have e : 2 + (k + 1) = k + 1 + 1 + 1 := by omega
      rw [e]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> apply byteArray_eq_of_toList <;> rw [hext, hin]
      · simp [hC, hcs, List.drop_left' (ByteOrder.length_toList_toBE k _)]
      · have e2 : k + 1 + 1 + 1 + content.size = k + content.size + 1 + 1 + 1 := by omega
        have hl : ((ByteOrder.toBE k content.size).toList ++ C).length = k + content.size := by
          simp [hcs]
        simp only [Nat.sub_zero, List.drop_zero, he, e2, List.take_succ_cons, List.cons_append,
          ← hl, List.take_left']
      · have e2 : k + 1 + 1 + 1 + content.size = k + content.size + 1 + 1 + 1 := by omega
        have hl : ((ByteOrder.toBE k content.size).toList ++ C).length = k + content.size := by
          simp [hcs]
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

/-- A value that reads also reads from its own encoding followed by any bytes. -/
theorem read_encoded_append {a rest : ByteArray} {v : Value} (ha : read a = .ok (v, rest))
    (more : ByteArray) : read (v.encoded ++ more) = .ok (v, more) := by
  obtain ⟨t1, t2, -, hv⟩ := read_ok_iff.mp ha
  -- The conditions on the value do not depend on the bytes after it.
  exact read_ok_iff.mpr ⟨t1, t2, by simp, hv⟩

/-- No encoding that reads is a proper prefix of another one.

The header fixes the length of the whole encoding (X.690 §§8.1.3, 10.1). -/
theorem encoded_eq_of_prefix {a b rest rest' : ByteArray} {v w : Value}
    (ha : read a = .ok (v, rest)) (hb : read b = .ok (w, rest'))
    (hp : v.encoded.data.toList <+: w.encoded.data.toList) : v.encoded = w.encoded := by
  obtain ⟨t, ht⟩ := hp
  obtain ⟨-, -, hin, -⟩ := read_ok_iff.mp hb
  -- The input of the second read starts with the encoding of the first value.
  have hb' : b = v.encoded ++ ⟨(t ++ rest'.data.toList).toArray⟩ := by
    apply byteArray_eq_of_toList
    simp [hin, ← ht]
  rw [hb', read_encoded_append ha] at hb
  -- Both reads return the first value, so the two values are one.
  obtain ⟨hvw, -⟩ := Prod.mk.inj (Except.ok.inj hb)
  rw [hvw]

/-- Two lists of which neither is a prefix of the other compare as their extensions do. -/
private theorem le_append_iff_of_not_prefix {l1 l2 : List UInt8} (h12 : ¬ l1 <+: l2)
    (h21 : ¬ l2 <+: l1) (t1 t2 : List UInt8) : l1 ++ t1 ≤ l2 ++ t2 ↔ l1 ≤ l2 := by
  induction l1 generalizing l2 with
  | nil => exact absurd (List.nil_prefix) h12
  | cons a as ih =>
    cases l2 with
    | nil => exact absurd (List.nil_prefix) h21
    | cons b bs =>
      simp only [List.cons_append, List.cons_le_cons_iff]
      by_cases hab : a = b
      · -- Equal first bytes: the order is that of the rest, where neither is a prefix either.
        subst hab
        have h12' : ¬ as <+: bs := fun h => h12 (List.prefix_cons_inj a |>.mpr h)
        have h21' : ¬ bs <+: as := fun h => h21 (List.prefix_cons_inj a |>.mpr h)
        simp [ih h12' h21']
      · -- Different first bytes decide both comparisons alike.
        simp [hab]

/-- The order of two encodings that read is the order of §11.6, with zero padding. -/
theorem encoded_le_iff_padded {a b rest rest' : ByteArray} {v w : Value}
    (ha : read a = .ok (v, rest)) (hb : read b = .ok (w, rest')) (n : Nat) :
    v.encoded.data.toList ≤ w.encoded.data.toList ↔
      v.encoded.data.toList ++ List.replicate (n - v.encoded.size) 0 ≤
        w.encoded.data.toList ++ List.replicate (n - w.encoded.size) 0 := by
  by_cases heq : v.encoded = w.encoded
  · -- One encoding twice: both sides compare a list with itself.
    rw [heq]
    exact iff_of_true (List.le_refl _) (List.le_refl _)
  · -- Two encodings: neither is a prefix of the other, so the padding never decides.
    have h12 : ¬ v.encoded.data.toList <+: w.encoded.data.toList :=
      fun p => heq (encoded_eq_of_prefix ha hb p)
    have h21 : ¬ w.encoded.data.toList <+: v.encoded.data.toList :=
      fun p => heq (encoded_eq_of_prefix hb ha p).symm
    exact (le_append_iff_of_not_prefix h12 h21 _ _).symm

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
      i = if first.toNat < 128 then (ByteOrder.ofBE (first :: rest) : Int)
        else ByteOrder.ofBE (first :: rest) - 256 ^ (rest.length + 1)) ↔
    ∃ k : Nat, -(128 * 256 ^ k : Int) ≤ i ∧ i < 128 * 256 ^ k ∧
      (∀ j < k, i < -(128 * 256 ^ j : Int) ∨ 128 * 256 ^ j ≤ i) ∧
      first :: rest = (ByteOrder.toBE (k + 1) (i % 256 ^ (k + 1)).toNat).toList := by
  have hN := ByteOrder.ofBE_cons first rest
  have hR := ByteOrder.ofBE_lt rest
  have hf : first.toNat < 256 := first.toNat_lt
  have mulQ : ∀ a b, a ≤ b → a * 256 ^ rest.length ≤ b * 256 ^ rest.length :=
    fun a b h => Nat.mul_le_mul_right _ h
  -- The second byte, when there is one, is worth `256 ^ (k - 1)` per unit.
  have hsecond : ∀ next tail, rest = next :: tail →
      ByteOrder.ofBE rest = next.toNat * 256 ^ tail.length + ByteOrder.ofBE tail ∧
      ByteOrder.ofBE tail < 256 ^ tail.length ∧ 256 ^ rest.length = 256 * 256 ^ tail.length ∧
      (∀ a b, a ≤ b → a * 256 ^ tail.length ≤ b * 256 ^ tail.length) := by
    rintro next tail rfl
    exact ⟨ByteOrder.ofBE_cons next tail, ByteOrder.ofBE_lt tail, by
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
        ByteOrder.ofBE (first :: rest) := by
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
      exact (ByteOrder.toList_toBE_ofBE (first :: rest)).symm
  · rintro ⟨k, lo, hi, hmin, hc⟩
    have hk : k = rest.length := by
      have := congrArg List.length hc
      rw [ByteOrder.length_toList_toBE, List.length_cons] at this
      omega
    subst hk
    -- The bytes hold `i` modulo `256 ^ (k + 1)`, which is `i` or `i + 256 ^ (k + 1)`.
    have hval :
        ByteOrder.ofBE (first :: rest) = (i % ((256 ^ rest.length * 256 : Nat) : Int)).toNat := by
      rw [hc, ByteOrder.ofBE_toBE_of_lt]
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

The octets are two's complement (X.690 §8.3.3). -/
theorem integer_ok_iff {value : Value} {i : Int} :
    integer value = .ok i ↔ value.tag = 2 ∧ ∃ k : Nat,
      -- `i` lies in `[-(128 * 256 ^ k), 128 * 256 ^ k)`, the range of `k + 1` octets.
      -(128 * 256 ^ k : Int) ≤ i ∧ i < 128 * 256 ^ k ∧
      -- No shorter content holds `i`.
      --
      -- So a first octet 0 or 255 is never redundant (X.690 §8.3.2).
      (∀ j < k, i < -(128 * 256 ^ j : Int) ∨ 128 * 256 ^ j ≤ i) ∧
      -- The content is `i` modulo `256 ^ (k + 1)` on `k + 1` big-endian octets.
      value.content.data.toList = (ByteOrder.toBE (k + 1) (i % 256 ^ (k + 1)).toNat).toList := by
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
      simp at this
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
      (∀ j < k, 128 * 256 ^ j ≤ n) ∧ value.content.data.toList
        = (ByteOrder.toBE (k + 1) n).toList := by
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

/-! ## BOOLEAN and BIT STRING -/

/-- A BOOLEAN reads as `b` exactly when its tag is 1 and its content is the one octet of `b`.

TRUE is the octet FF and FALSE the octet 00, so every other content is rejected.

That is X.690 §§8.2.1 and 8.2.2, with the DER rule for TRUE of §11.1. -/
theorem boolean_ok_iff {value : Value} {b : Bool} :
    boolean value = .ok b ↔
      value.tag = 1 ∧ value.content.data.toList = [if b then 0xFF else 0x00] := by
  unfold boolean
  generalize value.content.data.toList = c
  by_cases ht : value.tag = 1
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    rcases c with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw]
    · by_cases h0 : x = 0
      · subst h0
        cases b <;> simp [pure, Except.pure]
      · by_cases h1 : x = 255
        · subst h1
          cases b <;> simp [pure, Except.pure]
        · cases b <;> simp [h0, h1, throw, throwThe, MonadExceptOf.throw]
    · simp [throw, throwThe, MonadExceptOf.throw]
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A BIT STRING reads as `bytes` exactly when its tag is 3 and its content is 0, then `bytes`.

The initial octet 0 says that no bit of the final octet is unused (X.690 §8.6.2.2). -/
theorem bitString_ok_iff {value : Value} {bytes : ByteArray} :
    bitString value = .ok bytes ↔
      value.tag = 3 ∧ value.content.data.toList = 0 :: bytes.data.toList := by
  unfold bitString
  generalize value.content.data.toList = c
  by_cases ht : value.tag = 3
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    rcases c with _ | ⟨x, rest⟩
    · simp [throw, throwThe, MonadExceptOf.throw]
    · by_cases h0 : x = 0
      · subst h0
        simp only [pure, Except.pure, Except.ok.injEq, List.cons.injEq, true_and]
        constructor
        · rintro rfl
          rfl
        · intro h
          apply byteArray_eq_of_toList
          simp [h]
      · simp [h0, throw, throwThe, MonadExceptOf.throw]
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- The low `u` bits of `n` are zero exactly when `2 ^ u` divides it with no remainder. -/
private theorem mod_two_pow_eq_zero_iff (n u : Nat) :
    n % 2 ^ u = 0 ↔ ∀ i < u, n.testBit i = false := by
  constructor
  · intro h i hi
    have := Nat.testBit_mod_two_pow n u i
    rw [h, Nat.zero_testBit] at this
    simpa [hi] using this.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    by_cases hi : i < u
    · simp [hi, h i hi]
    · simp [hi]

/-- BIT STRING contents pass exactly when the initial octet counts at most 7 unused bits, all zero.

The reader does not know the type, so it does not drop the trailing zero bits of §11.2.2. -/
theorem validBits_ok_iff {content : ByteArray} :
    -- The initial octet is 0 when no octet follows it (X.690 §8.6.2.3).
    validBits content = .ok () ↔ content.data.toList = [0] ∨
      -- Otherwise the unused bits are the low bits of the final octet (X.690 §§8.6.2.1, 8.6.2.2).
      ∃ unused init last, content.data.toList = unused :: (init ++ [last]) ∧
        -- At most 7 bits are unused, and each of them is zero (X.690 §11.2.1).
        unused.toNat ≤ 7 ∧ ∀ i < unused.toNat, last.toNat.testBit i = false := by
  unfold validBits
  generalize content.data.toList = c
  rcases c with _ | ⟨unused, bytes⟩
  · simp [throw, throwThe, MonadExceptOf.throw]
  rcases List.eq_nil_or_concat bytes with rfl | ⟨init, last, rfl⟩
  · by_cases h0 : unused = 0
    · subst h0
      simp [pure, Except.pure]
    · have : unused.toNat ≠ 0 := fun h => h0 (UInt8.toNat_inj.mp h)
      simp [h0, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
      Option.some_or]
    have hr : (unused :: (init ++ [last]) = [0] ∨ ∃ u i l, unused :: (init ++ [last]) =
        u :: (i ++ [l]) ∧ u.toNat ≤ 7 ∧ ∀ j < u.toNat, l.toNat.testBit j = false) ↔
        unused.toNat ≤ 7 ∧ last.toNat % 2 ^ unused.toNat = 0 := by
      constructor
      · rintro (h | ⟨u, i, l, h, h7, hb⟩)
        · simp at h
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, h⟩ := h
          obtain ⟨-, hl⟩ := List.append_inj' h rfl
          simp only [List.cons.injEq, and_true] at hl
          subst hl
          exact ⟨h7, (mod_two_pow_eq_zero_iff _ _).mpr hb⟩
      · rintro ⟨h7, hb⟩
        exact .inr ⟨unused, init, last, rfl, h7, (mod_two_pow_eq_zero_iff _ _).mp hb⟩
    rw [hr]
    by_cases h7 : 7 < unused.toNat
    · simp [h7, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      omega
    · by_cases hm : last.toNat % 2 ^ unused.toNat = 0
      · simp [h7, hm, pure, Except.pure]
        omega
      · simp [h7, hm, throw, throwThe, MonadExceptOf.throw]

/-! ## BMPString and UniversalString -/

/-- One step of the code-unit reader: the octets of the current unit, their value, the verdict. -/
private def step (width : Nat) (state : Nat × Nat × Bool) (byte : UInt8) : Nat × Nat × Bool :=
  let n := state.2.1 * 256 + byte.toNat
  if state.1 + 1 = width then (0, 0, state.2.2 && unicodeScalar n)
  else (state.1 + 1, n, state.2.2)

/-- The verdict at the end: no partial code unit, and every code unit a scalar. -/
private def finish (state : Nat × Nat × Bool) : Bool := state.1 == 0 && state.2.2

/-- The code-unit reader is the fold of one step. -/
private theorem fixedString_eq (width : Nat) (bytes : List UInt8) :
    fixedString width bytes = finish (bytes.foldl (step width) (0, 0, true)) := rfl

/-- Octets that do not complete a code unit are counted and read big-endian. -/
private theorem foldl_step_partial {width : Nat} (bytes : List UInt8) (i acc : Nat) (ok : Bool)
    (h : i + bytes.length < width) :
    bytes.foldl (step width) (i, acc, ok) =
      (i + bytes.length, acc * 256 ^ bytes.length + ByteOrder.ofBE bytes, ok) := by
  induction bytes generalizing i acc with
  | nil => simp [ByteOrder.ofBE_eq_foldl]
  | cons x xs ih =>
    simp only [List.length_cons] at h
    have hne : ¬ i + 1 = width := by omega
    simp only [List.foldl_cons, step, hne, ite_false]
    rw [ih (i + 1) (acc * 256 + x.toNat) (by omega), ByteOrder.ofBE_cons]
    simp only [List.length_cons, Prod.mk.injEq, and_true]
    refine ⟨by omega, ?_⟩
    rw [Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256, Nat.add_assoc]

/-- A complete code unit resets the count and adds its scalar check to the verdict. -/
private theorem foldl_step_chunk {width : Nat} (chunk : List UInt8) (ok : Bool)
    (pos : 0 < width) (h : chunk.length = width) :
    chunk.foldl (step width) (0, 0, ok) = (0, 0, ok && unicodeScalar (ByteOrder.ofBE chunk)) := by
  rcases List.eq_nil_or_concat chunk with rfl | ⟨init, last, rfl⟩
  · simp at h
    omega
  · simp only [List.concat_eq_append, List.length_append, List.length_singleton] at h ⊢
    rw [List.foldl_append, foldl_step_partial init 0 0 ok (by omega)]
    simp [step, h, ByteOrder.ofBE_eq_foldl, Nat.mul_comm]

/-- A Unicode scalar value is at most 10FFFF and is not a surrogate, D800 to DFFF. -/
private theorem unicodeScalar_iff (n : Nat) :
    unicodeScalar n = true ↔ n ≤ 0x10FFFF ∧ (n < 0xD800 ∨ 0xDFFF < n) := by
  simp only [unicodeScalar, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega

/-- The fold accepts from a verdict `ok` exactly when `ok` holds and the octets write scalars.

Each scalar takes `width` octets, big-endian. -/
private theorem finish_foldl_iff {width : Nat} (pos : 0 < width) (bytes : List UInt8)
    (ok : Bool) :
    finish (bytes.foldl (step width) (0, 0, ok)) = true ↔ ok = true ∧ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ width ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      bytes = chars.flatMap (fun x => (ByteOrder.toBE width x).toList) := by
  induction h : bytes.length using Nat.strongRecOn generalizing bytes ok with
  | _ n ih =>
    by_cases hw : width ≤ bytes.length
    · -- The first code unit is the first `width` octets.
      rw [← List.take_append_drop width bytes, List.foldl_append,
        foldl_step_chunk _ ok pos (by simp; omega),
        ih (bytes.drop width).length (by simp; omega) _ _ rfl]
      constructor
      · rintro ⟨hok, chars, hc, he⟩
        rw [Bool.and_eq_true, unicodeScalar_iff] at hok
        refine ⟨hok.1, ByteOrder.ofBE (bytes.take width) :: chars, ?_, ?_⟩
        · intro c hc'
          rcases List.mem_cons.mp hc' with rfl | hc'
          · refine ⟨?_, hok.2⟩
            have := ByteOrder.ofBE_lt (bytes.take width)
            simpa [Nat.min_eq_left hw] using this
          · exact hc c hc'
        · have hl : (bytes.take width).length = width := by simp; omega
          rw [List.flatMap_cons, ← he]
          conv => lhs; rw [← ByteOrder.toList_toBE_ofBE (bytes.take width)]
          rw [hl]
      · rintro ⟨hok, chars, hc, he⟩
        rcases chars with _ | ⟨c, chars⟩
        · simp only [List.flatMap_nil, List.take_append_drop] at he
          rw [he] at hw
          simp at hw
          omega
        · rw [List.take_append_drop, List.flatMap_cons] at he
          have hc0 := hc c (by simp)
          have ht : bytes.take width = (ByteOrder.toBE width c).toList := by
            rw [he, List.take_left' (ByteOrder.length_toList_toBE width c)]
          have hd : bytes.drop width
              = chars.flatMap (fun x => (ByteOrder.toBE width x).toList) := by
            rw [he, List.drop_left' (ByteOrder.length_toList_toBE width c)]
          rw [Bool.and_eq_true, unicodeScalar_iff, ht, ByteOrder.ofBE_toBE_of_lt hc0.1]
          exact ⟨⟨hok, hc0.2⟩, chars, fun c' h' => hc c' (by simp [h']), hd⟩
    · -- Fewer than `width` octets pass only when there are none.
      rw [foldl_step_partial bytes 0 0 ok (by omega)]
      rcases bytes with _ | ⟨x, xs⟩
      · simp only [finish]
        simp
        intro _
        exact ⟨[], by simp, by simp⟩
      · have hz : (0 + (x :: xs).length == 0) = false := by simp
        simp only [finish, hz, Bool.false_and, Bool.false_eq_true, false_iff, not_and,
          not_exists]
        intro _ chars _ he
        rcases chars with _ | ⟨c, chars⟩
        · simp at he
        · have := congrArg List.length he
          simp at this
          simp at hw
          omega

/-- Code units of `width` octets pass exactly when they write a list of Unicode scalar values.

The reader takes a scalar value to be at most 10FFFF and outside the surrogates D800 to DFFF.

Each is written big-endian on `width` octets, so it is below `256 ^ width`.

A UniversalString has four octets per character and a BMPString two (X.690 §§8.23.7, 8.23.8). -/
theorem fixedString_eq_true_iff {width : Nat} (pos : 0 < width) {bytes : List UInt8} :
    fixedString width bytes = true ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ width ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      bytes = chars.flatMap (fun x => (ByteOrder.toBE width x).toList) := by
  rw [fixedString_eq, finish_foldl_iff pos]
  simp

/-! ## OBJECT IDENTIFIER -/

/-- One step of the subidentifier check: reject a leading 80, then note whether one ends here. -/
private def oidStep (atStart : Bool) (byte : UInt8) : Except Error Bool := do
  if atStart ∧ byte = 128 then throw .value
  return byte.toNat < 128

/-- The check of a content is the fold of one step from the start of a subidentifier. -/
private theorem oid_eq (value : Value) : oid value = (do
    if value.tag != 6 then throw (.tag (some 6) value.tag)
    if value.content.isEmpty then throw .value
    let atStart ← value.content.data.toList.foldlM oidStep true
    if atStart then return value.content else throw .value) := rfl

/-- Octets that end a subidentifier: bit 8 set on each but the last, clear on the last. -/
private def Tail (p : List UInt8) : Prop :=
  ∃ init last, p = init ++ [last] ∧ (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80

/-- A subidentifier also has a first octet other than 80, so it is on the fewest octets. -/
private def Sub (p : List UInt8) : Prop := p.head? ≠ some 0x80 ∧ Tail p

/-- The octets that end a subidentifier are never empty. -/
private theorem tail_ne_nil {p : List UInt8} (h : Tail p) : p ≠ [] := by
  obtain ⟨init, last, rfl, -, -⟩ := h
  simp

/-- An octet that ends a subidentifier has bit 8 clear, and any other has it set. -/
private theorem tail_cons_iff (x : UInt8) (r : List UInt8) :
    Tail (x :: r) ↔ (r = [] ∧ x.toNat < 0x80) ∨ (0x80 ≤ x.toNat ∧ Tail r) := by
  constructor
  · rintro ⟨init, last, h, hi, hl⟩
    rcases init with _ | ⟨y, init⟩
    · simp only [List.nil_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inl ⟨rfl, hl⟩
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .inr ⟨hi _ (by simp), init, last, rfl, fun b hb => hi b (by simp [hb]), hl⟩
  · rintro (⟨rfl, hx⟩ | ⟨hx, init, last, rfl, hi, hl⟩)
    · exact ⟨[], x, rfl, by simp, hx⟩
    · refine ⟨x :: init, last, rfl, ?_, hl⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hx
      · exact hi b hb

/-- A split whose first piece is nonempty starts that piece with the first octet. -/
private theorem cons_eq_append_iff {Q : List UInt8 → Prop} (hQ : ∀ t, Q t → t ≠ [])
    (R : List (List UInt8) → Prop) (x : UInt8) (xs : List UInt8) :
    (∃ (t : List UInt8) (parts : List (List UInt8)),
        x :: xs = t ++ parts.flatten ∧ Q t ∧ R parts) ↔
      ∃ (r : List UInt8) (parts : List (List UInt8)),
        xs = r ++ parts.flatten ∧ Q (x :: r) ∧ R parts := by
  constructor
  · rintro ⟨t, parts, h, hq, hr⟩
    rcases t with _ | ⟨y, r⟩
    · exact absurd rfl (hQ _ hq)
    · simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨r, parts, rfl, hq, hr⟩
  · rintro ⟨r, parts, rfl, hq, hr⟩
    exact ⟨x :: r, parts, rfl, hq, hr⟩

/-- Nonempty octets split into subidentifiers exactly when a first one comes before the rest. -/
private theorem cons_eq_flatten_iff (x : UInt8) (xs : List UInt8) :
    (∃ parts : List (List UInt8), x :: xs = parts.flatten ∧ ∀ q ∈ parts, Sub q) ↔
      ∃ (t : List UInt8) (parts : List (List UInt8)),
        x :: xs = t ++ parts.flatten ∧ Sub t ∧ ∀ q ∈ parts, Sub q := by
  constructor
  · rintro ⟨_ | ⟨t, parts⟩, h, hp⟩
    · simp at h
    · exact ⟨t, parts, h, hp t (by simp), fun q hq => hp q (by simp [hq])⟩
  · rintro ⟨t, parts, h, ht, hp⟩
    refine ⟨t :: parts, h, ?_⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ht
    · exact hp q hq

/-- From the start of a subidentifier the fold ends at a start exactly on whole subidentifiers.

From inside one, it ends at a start exactly when the octets end that one first. -/
private theorem foldlM_oidStep (c : List UInt8) :
    (c.foldlM oidStep true = .ok true ↔
      ∃ parts : List (List UInt8), c = parts.flatten ∧ ∀ q ∈ parts, Sub q) ∧
    (c.foldlM oidStep false = .ok true ↔
      ∃ (t : List UInt8) (parts : List (List UInt8)),
        c = t ++ parts.flatten ∧ Tail t ∧ ∀ q ∈ parts, Sub q) := by
  induction c with
  | nil =>
    refine ⟨?_, ?_⟩
    · simp only [List.foldlM_nil, pure, Except.pure, true_iff]
      exact ⟨[], rfl, by simp⟩
    · simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Bool.false_eq_true,
        false_iff, not_exists, not_and]
      intro t parts h ht
      have := tail_ne_nil ht
      simp_all
  | cons x xs ih =>
    have hS : ∀ t, Sub t → t ≠ [] := fun t h => tail_ne_nil h.2
    rw [cons_eq_flatten_iff, cons_eq_append_iff hS, cons_eq_append_iff (fun t h => tail_ne_nil h)]
    have hsub : ∀ r, Sub (x :: r) ↔ x ≠ 0x80 ∧ Tail (x :: r) := fun r => by simp [Sub]
    simp only [hsub, tail_cons_iff]
    have hnil : ∀ P : List (List UInt8) → Prop,
        (∃ parts : List (List UInt8), xs = parts.flatten ∧ P parts) ↔
          ∃ (r : List UInt8) (parts : List (List UInt8)),
            xs = r ++ parts.flatten ∧ r = [] ∧ P parts := by
      intro P
      constructor
      · rintro ⟨parts, h, hp⟩
        exact ⟨[], parts, h, rfl, hp⟩
      · rintro ⟨r, parts, h, rfl, hp⟩
        exact ⟨parts, h, hp⟩
    by_cases h128 : x = 0x80
    · subst h128
      simp [List.foldlM_cons, oidStep, throw, throwThe, MonadExceptOf.throw, bind,
        Except.bind, pure, Except.pure, ih.2]
    · by_cases hx : x.toNat < 0x80
      · have hx' : ¬ 0x80 ≤ x.toNat := by omega
        simp only [List.foldlM_cons, oidStep, h128, hx, hx', and_false, ite_false, pure,
          Except.pure, bind, Except.bind, decide_true, ih.1, false_and, or_false, true_and,
          ne_eq, not_false_eq_true, and_true]
        exact ⟨hnil _, hnil _⟩
      · have hx' : 0x80 ≤ x.toNat := by omega
        simp only [List.foldlM_cons, oidStep, h128, hx, hx', and_false, ite_false, pure,
          Except.pure, bind, Except.bind, decide_false, ih.2, false_or, true_and,
          ne_eq, not_false_eq_true]

/-- An OBJECT IDENTIFIER reads as `bytes` exactly when its tag is 6 and `bytes` is its content.

The first subidentifier combines two arcs, and any value of it names a valid pair (§8.19.4). -/
theorem oid_ok_iff {value : Value} {bytes : ByteArray} :
    oid value = .ok bytes ↔ value.tag = 6 ∧ bytes = value.content ∧
      -- The content must be one or more subidentifiers (X.690 §8.19.2).
      ∃ parts : List (List UInt8), parts ≠ [] ∧ value.content.data.toList = parts.flatten ∧
        -- The first octet of a subidentifier is not 80, so that it takes the fewest octets.
        ∀ p ∈ parts, p.head? ≠ some 0x80 ∧ ∃ init last, p = init ++ [last] ∧
          -- Bit 8 is set on each octet of a subidentifier but the last, and clear on the last.
          (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80 := by
  rw [oid_eq]
  change _ ↔ _ ∧ _ ∧ ∃ parts : List (List UInt8), parts ≠ [] ∧
    value.content.data.toList = parts.flatten ∧ ∀ p ∈ parts, Sub p
  have hempty : value.content.isEmpty = true ↔ value.content.data.toList = [] := by
    have hsize : value.content.size = value.content.data.toList.length := by
      rw [Array.length_toList]
      rfl
    simp only [ByteArray.isEmpty, hsize, beq_iff_eq, List.length_eq_zero_iff]
  by_cases ht : value.tag = 6
  · simp only [ht, bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    revert hempty
    generalize value.content.data.toList = c
    intro hempty
    rcases c with _ | ⟨x, xs⟩
    · simp only [hempty, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
        reduceCtorEq, false_iff, not_and, not_exists]
      intro _ parts hne h hp
      rcases parts with _ | ⟨p, parts⟩
      · exact hne rfl
      · have := tail_ne_nil (hp p (by simp)).2
        simp_all
    · have hne : ¬ value.content.isEmpty = true := by simp [hempty]
      have key := (foldlM_oidStep (x :: xs)).1
      cases h : (x :: xs).foldlM oidStep true with
      | error e =>
        simp only [hne, ↓reduceIte, bind, Except.bind, reduceCtorEq, false_iff, not_and,
          not_exists]
        intro _ parts _ hc hp
        rw [key.mpr ⟨parts, hc, hp⟩] at h
        cases h
      | ok a =>
        cases a
        · simp only [hne, ↓reduceIte, bind, Except.bind, Bool.false_eq_true, throw, throwThe,
            MonadExceptOf.throw, reduceCtorEq, false_iff, not_and, not_exists]
          intro _ parts _ hc hp
          rw [key.mpr ⟨parts, hc, hp⟩] at h
          cases h
        · obtain ⟨parts, hc, hp⟩ := key.mp h
          simp only [hne, ↓reduceIte, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
            Bool.false_eq_true]
          constructor
          · rintro rfl
            refine ⟨rfl, parts, ?_, hc, hp⟩
            rintro rfl
            simp at hc
          · rintro ⟨rfl, -⟩
            rfl
  · simp [ht, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-! ## The certificate subset -/

/-- With positive fuel, a value of tag 1 passes validation exactly when its content is 00 or FF. -/
theorem validate_go_boolean_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 1) :
    validate.go (fuel + 1) value = .ok () ↔
      value.content.data.toList = [0x00] ∨ value.content.data.toList = [0xFF] := by
  have hb : (∃ b, boolean value = .ok b) ↔
      value.content.data.toList = [0x00] ∨ value.content.data.toList = [0xFF] := by
    simp only [boolean_ok_iff, tag, true_and]
    constructor
    · rintro ⟨b, h⟩
      cases b <;> simp_all
    · rintro (h | h)
      · exact ⟨false, by simp [h]⟩
      · exact ⟨true, by simp [h]⟩
  rw [← hb, validate.go, tag]
  cases boolean value <;> simp [bind, Except.bind, pure, Except.pure]

/-- With positive fuel, a value of tag 3 passes validation exactly when its contents do. -/
theorem validate_go_bitString {value : Value} (fuel : Nat) (tag : value.tag = 3) :
    validate.go (fuel + 1) value = validBits value.content := by
  rw [validate.go, tag]
  rfl

/-- With positive fuel, a value of tag 30 passes validation exactly when it writes scalar values.

Each takes two octets. -/
theorem validate_go_bmpString_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 30) :
    validate.go (fuel + 1) value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 2 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (fun x => (ByteOrder.toBE 2 x).toList) := by
  rw [← fixedString_eq_true_iff (by decide), validate.go, tag]
  dsimp only
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of tag 28 passes validation exactly when it writes scalar values.

Each takes four octets. -/
theorem validate_go_universalString_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 28) :
    validate.go (fuel + 1) value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 4 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (fun x => (ByteOrder.toBE 4 x).toList) := by
  rw [← fixedString_eq_true_iff (by decide), validate.go, tag]
  dsimp only
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- A value of tag 1 passes validation exactly when its content is the octet 00 or the octet FF. -/
theorem validate_boolean_ok_iff {value : Value} (tag : value.tag = 1) :
    validate value = .ok () ↔
      value.content.data.toList = [0x00] ∨ value.content.data.toList = [0xFF] :=
  validate_go_boolean_ok_iff _ tag

/-- A value of tag 3 passes validation exactly when its contents are those of a BIT STRING. -/
theorem validate_bitString {value : Value} (tag : value.tag = 3) :
    validate value = validBits value.content :=
  validate_go_bitString _ tag

/-- A BMPString passes validation exactly when it writes Unicode scalar values, two octets each. -/
theorem validate_bmpString_ok_iff {value : Value} (tag : value.tag = 30) :
    validate value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 2 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (fun x => (ByteOrder.toBE 2 x).toList) :=
  validate_go_bmpString_ok_iff _ tag

/-- A UniversalString passes validation exactly when it writes scalar values, four octets each. -/
theorem validate_universalString_ok_iff {value : Value} (tag : value.tag = 28) :
    validate value = .ok () ↔ ∃ chars : List Nat,
      (∀ c ∈ chars, c < 256 ^ 4 ∧ c ≤ 0x10FFFF ∧ (c < 0xD800 ∨ 0xDFFF < c)) ∧
      value.content.data.toList = chars.flatMap (fun x => (ByteOrder.toBE 4 x).toList) :=
  validate_go_universalString_ok_iff _ tag

/-- With positive fuel, a value of tag 6 passes validation exactly when it is subidentifiers.

Each has bit 8 set on all its octets but the last, and a first octet other than 80. -/
private theorem validate_go_oid_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 6) :
    validate.go (fuel + 1) value = .ok () ↔
      ∃ parts : List (List UInt8), parts ≠ [] ∧ value.content.data.toList = parts.flatten ∧
        ∀ p ∈ parts, p.head? ≠ some 0x80 ∧ ∃ init last, p = init ++ [last] ∧
          (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80 := by
  have ho : (∃ b, oid value = .ok b) ↔ ∃ parts : List (List UInt8), parts ≠ [] ∧
      value.content.data.toList = parts.flatten ∧ ∀ p ∈ parts, p.head? ≠ some 0x80 ∧
        ∃ init last, p = init ++ [last] ∧ (∀ b ∈ init, 0x80 ≤ b.toNat) ∧
          last.toNat < 0x80 := by
    simp only [oid_ok_iff, tag, true_and, exists_eq_left]
  rw [← ho, validate.go, tag]
  cases oid value <;> simp [bind, Except.bind, pure, Except.pure]

/-- With positive fuel, a value of tag 5 passes validation exactly when its content is empty.

That is the NULL of X.690 §8.8.2. -/
private theorem validate_go_null_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 5) :
    validate.go (fuel + 1) value = .ok () ↔ value.content.data.toList = [] := by
  have hsize : value.content.size = value.content.data.toList.length := by
    rw [Array.length_toList]
    rfl
  rw [validate.go, tag]
  simp only [ByteArray.isEmpty, hsize, beq_iff_eq, List.length_eq_zero_iff]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of tag 12 passes validation exactly when it is UTF-8 characters.

That is the UTF8String of X.690 §8.23.10. -/
private theorem validate_go_utf8String_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 12) :
    validate.go (fuel + 1) value = .ok () ↔
      ∃ chars : List Char, value.content = chars.utf8Encode := by
  have hv : (String.fromUTF8? value.content).isSome = true ↔
      ∃ chars : List Char, value.content = chars.utf8Encode := by
    by_cases h : value.content.IsValidUTF8
    · simp only [String.fromUTF8?, h, dite_true, Option.isSome_some, true_iff]
      obtain ⟨chars, hc⟩ := h
      exact ⟨chars, hc⟩
    · simp only [String.fromUTF8?, h, dite_false, Option.isSome_none, Bool.false_eq_true,
        false_iff, not_exists]
      exact fun chars hc => h ⟨chars, hc⟩
  rw [← hv, validate.go, tag]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- The marks of PrintableString besides the letters and digits (X.680 §41.4). -/
private def printableMarks : List Char :=
  [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?']

/-- An octet is a PrintableString character: a Latin letter, a digit, or one of 12 marks. -/
private theorem printable_iff (b : UInt8) :
    ((48 ≤ b.toNat && b.toNat ≤ 57) || (65 ≤ b.toNat && b.toNat ≤ 90) ||
      (97 ≤ b.toNat && b.toNat ≤ 122) ||
      ([32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63] : List UInt8).contains b) = true ↔
      (Char.ofNat b.toNat).isAlphanum ∨ Char.ofNat b.toNat ∈ printableMarks := by
  have key : ∀ n < 256,
      ((48 ≤ n && n ≤ 57) || (65 ≤ n && n ≤ 90) || (97 ≤ n && n ≤ 122) ||
        ([32, 39, 40, 41, 43, 44, 45, 46, 47, 58, 61, 63] : List UInt8).contains
          (UInt8.ofNat n)) = true ↔
        (Char.ofNat n).isAlphanum ∨ Char.ofNat n ∈ printableMarks := by
    decide +kernel
  have := key b.toNat b.toNat_lt
  rwa [UInt8.ofNat_toNat] at this

/-- With positive fuel, a value of tag 19 passes validation exactly when it is PrintableString.

Each octet is then a Latin letter, a digit, a space or one of `'()+,-./:=?` (X.680 §41.4). -/
private theorem validate_go_printableString_ok_iff {value : Value} (fuel : Nat)
    (tag : value.tag = 19) :
    validate.go (fuel + 1) value = .ok () ↔ ∀ b ∈ value.content.data.toList,
      (Char.ofNat b.toNat).isAlphanum ∨
        Char.ofNat b.toNat ∈ [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?'] := by
  simp only [show [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?'] = printableMarks
    from rfl, ← printable_iff]
  rw [← List.all_eq_true, validate.go, tag]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of tag 2 passes validation exactly when it is a DER INTEGER.

Its content has one octet or more (X.690 §8.3.1).

With two octets or more, its first nine bits are neither all zero nor all one (X.690 §8.3.2). -/
private theorem validate_go_integer_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 2) :
    validate.go (fuel + 1) value = .ok () ↔ value.content.data.toList ≠ [] ∧
      ∀ first next rest, value.content.data.toList = first :: next :: rest →
        ¬(first = 0x00 ∧ next.toNat < 0x80) ∧ ¬(first = 0xFF ∧ 0x80 ≤ next.toNat) := by
  have step : validate.go (fuel + 1) value = (do let _ ← integer value; pure ()) := by
    rw [validate.go, tag]
    rfl
  rw [step, integer]
  simp only [tag, bne_self_eq_false, Bool.false_eq_true, ite_false]
  generalize value.content.data.toList = c
  rcases c with _ | ⟨first, _ | ⟨next, rest⟩⟩
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
  · simp [pure, Except.pure, bind, Except.bind]
  · by_cases hr : (first = 0 ∧ next.toNat < 128) ∨ (first = 255 ∧ 128 ≤ next.toNat)
    · simp only [hr, ite_true, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.cons.injEq, true_and]
      refine ⟨False.elim, fun h => ?_⟩
      obtain ⟨zero, one⟩ := h first next rest ⟨rfl, rfl, rfl⟩
      rcases hr with h | h
      · exact zero h
      · exact one h
    · simp only [hr, ite_false, pure, Except.pure, bind, Except.bind]
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.cons.injEq, true_and]
      refine ⟨fun _ => ?_, fun _ => trivial⟩
      rintro f n r ⟨rfl, rfl, rfl⟩
      exact ⟨fun h => hr (.inl h), fun h => hr (.inr h)⟩

/-- With positive fuel, a value of tag 4 passes validation whatever its content. -/
private theorem validate_go_octetString {value : Value} (fuel : Nat) (tag : value.tag = 4) :
    validate.go (fuel + 1) value = .ok () := by
  rw [validate.go, tag]
  rfl

/-- With positive fuel, a value of tag 22 passes validation exactly when each octet is below 128.

Those are the 128 characters of IA5, one octet each. -/
private theorem validate_go_ia5String_ok_iff {value : Value} (fuel : Nat) (tag : value.tag = 22) :
    validate.go (fuel + 1) value = .ok () ↔ ∀ b ∈ value.content.data.toList, b.toNat < 0x80 := by
  have hall : (value.content.data.toList.all fun b => decide (b.toNat < 128)) = true ↔
      ∀ b ∈ value.content.data.toList, b.toNat < 0x80 := by
    simp only [List.all_eq_true, decide_eq_true_eq]
  rw [← hall, validate.go, tag]
  split <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

/-- With positive fuel, a value of any tag outside the certificate subset is rejected by its tag.

The subset is BOOLEAN, INTEGER, BIT STRING, OCTET STRING, NULL and OBJECT IDENTIFIER.

It also holds the UTF8String, PrintableString, IA5String, UniversalString and BMPString.

The constructed SEQUENCE and SET have identifier octets 48 and 49. -/
private theorem validate_go_eq_error_tag {value : Value} (fuel : Nat)
    (tag : value.tag.toNat ∉ [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49]) :
    validate.go (fuel + 1) value = .error (.tag none value.tag) := by
  rw [validate.go]
  split <;> simp_all <;> rfl

/-- A value of tag 6 passes validation exactly when its content is one or more subidentifiers.

Each has bit 8 set on all its octets but the last, and a first octet other than 80. -/
theorem validate_oid_ok_iff {value : Value} (tag : value.tag = 6) :
    validate value = .ok () ↔
      ∃ parts : List (List UInt8), parts ≠ [] ∧ value.content.data.toList = parts.flatten ∧
        ∀ p ∈ parts, p.head? ≠ some 0x80 ∧ ∃ init last, p = init ++ [last] ∧
          (∀ b ∈ init, 0x80 ≤ b.toNat) ∧ last.toNat < 0x80 :=
  validate_go_oid_ok_iff _ tag

/-- A NULL passes validation exactly when its content is empty (X.690 §8.8.2). -/
theorem validate_null_ok_iff {value : Value} (tag : value.tag = 5) :
    validate value = .ok () ↔ value.content.data.toList = [] :=
  validate_go_null_ok_iff _ tag

/-- A UTF8String passes validation exactly when it is the UTF-8 encoding of some characters. -/
theorem validate_utf8String_ok_iff {value : Value} (tag : value.tag = 12) :
    validate value = .ok () ↔ ∃ chars : List Char, value.content = chars.utf8Encode :=
  validate_go_utf8String_ok_iff _ tag

/-- A PrintableString passes validation exactly when each octet is one of its characters.

Those are the Latin letters, the digits, the space and `'()+,-./:=?` (X.680 §41.4). -/
theorem validate_printableString_ok_iff {value : Value} (tag : value.tag = 19) :
    validate value = .ok () ↔ ∀ b ∈ value.content.data.toList,
      (Char.ofNat b.toNat).isAlphanum ∨
        Char.ofNat b.toNat ∈ [' ', '\'', '(', ')', '+', ',', '-', '.', '/', ':', '=', '?'] :=
  validate_go_printableString_ok_iff _ tag

/-- An INTEGER passes validation exactly when its content is the fewest octets of its value.

Its content has one octet or more (X.690 §8.3.1).

With two octets or more, its first nine bits are neither all zero nor all one (X.690 §8.3.2). -/
theorem validate_integer_ok_iff {value : Value} (tag : value.tag = 2) :
    validate value = .ok () ↔ value.content.data.toList ≠ [] ∧
      ∀ first next rest, value.content.data.toList = first :: next :: rest →
        ¬(first = 0x00 ∧ next.toNat < 0x80) ∧ ¬(first = 0xFF ∧ 0x80 ≤ next.toNat) :=
  validate_go_integer_ok_iff _ tag

/-- An OCTET STRING passes validation whatever its content (X.690 §8.7.2). -/
theorem validate_octetString {value : Value} (tag : value.tag = 4) : validate value = .ok () :=
  validate_go_octetString _ tag

/-- An IA5String passes validation exactly when each octet is below 128.

Those are the 128 characters of IA5, one octet each (X.680 §41.1, Table 8). -/
theorem validate_ia5String_ok_iff {value : Value} (tag : value.tag = 22) :
    validate value = .ok () ↔ ∀ b ∈ value.content.data.toList, b.toNat < 0x80 :=
  validate_go_ia5String_ok_iff _ tag

/-- A value of a tag outside the certificate subset fails validation with a tag error.

The error names that tag, and no expected one. -/
theorem validate_eq_error_tag {value : Value}
    (tag : value.tag.toNat ∉ [1, 2, 3, 4, 5, 6, 12, 19, 22, 28, 30, 48, 49]) :
    validate value = .error (.tag none value.tag) :=
  validate_go_eq_error_tag _ tag

/-! ## SEQUENCE and SET OF -/

/-- The size of a byte array is the length of its octet list. -/
theorem size_eq_length (b : ByteArray) : b.size = b.data.toList.length := by
  rw [Array.length_toList]
  rfl

/-- A value that the reader returns has an encoding longer than its content, by its header. -/
theorem size_lt_of_read_ok {input rest : ByteArray} {v : Value}
    (h : read input = .ok (v, rest)) :
    v.content.size < v.encoded.size ∧ v.encoded.size + rest.size = input.size := by
  obtain ⟨-, -, hin, hv⟩ := read_ok_iff.mp h
  refine ⟨?_, by rw [size_eq_length, size_eq_length, size_eq_length, hin, List.length_append]⟩
  rw [size_eq_length, size_eq_length]
  rcases hv with ⟨-, hv⟩ | ⟨k, -, -, -, -, hv⟩ <;> rw [hv] <;> simp <;> omega

/-- An empty byte array has no octets. -/
theorem data_toList_eq_nil_of_isEmpty {b : ByteArray} (h : b.isEmpty = true) :
    b.data.toList = [] := by
  have : b.size = 0 := by simpa [ByteArray.isEmpty] using h
  rw [size_eq_length] at this
  exact List.eq_nil_of_length_eq_zero this

/-- An input whose first value has under 128 content octets starts with that value.

It is the tag, one length octet, the content, then the rest. -/
theorem data_toList_eq_of_read_ok {input rest : ByteArray} {v : Value} {content : List UInt8}
    (h : read input = .ok (v, rest)) (hc : v.content.data.toList = content)
    (small : content.length < 128) :
    input.data.toList = v.tag :: UInt8.ofNat content.length :: (content ++ rest.data.toList) := by
  obtain ⟨-, -, hin, hv⟩ := read_ok_iff.mp h
  have hs : v.content.size = content.length := by rw [size_eq_length, hc]
  rcases hv with ⟨-, he⟩ | ⟨k, -, -, -, big, -⟩
  · rw [hin, he, hs, hc]
    rfl
  · omega

/-- A tag, a length octet under 128 and a content of that length read as one value. -/
theorem read_eq_ok_of_length_lt {tag : UInt8} {content rest : List UInt8}
    (low : tag.toNat % 32 ≠ 31) (nonzero : tag ≠ 0) (small : content.length < 128) :
    read ⟨(tag :: UInt8.ofNat content.length :: (content ++ rest)).toArray⟩ =
      .ok (⟨tag, ⟨content.toArray⟩, ⟨(tag :: UInt8.ofNat content.length :: content).toArray⟩⟩,
        ⟨rest.toArray⟩) :=
  read_ok_iff.mpr ⟨low, nonzero, by simp,
    .inl ⟨show content.toArray.size < 128 by simpa using small, by simp [ByteArray.size]⟩⟩

/-- A read of siblings that returns a value has read that value first. -/
theorem exists_of_children_go_eq_ok_cons {fuel : Nat} {input : ByteArray} {v : Value}
    {vs : List Value} (h : children.go fuel input = .ok (v :: vs)) :
    ∃ f rest, fuel = f + 1 ∧ read input = .ok (v, rest) ∧ children.go f rest = .ok vs := by
  cases fuel with
  | zero =>
    rw [children_go_zero] at h
    split at h <;> simp at h
  | succ f =>
    rw [children_go_succ] at h
    by_cases he : input.isEmpty = true
    · simp [he, pure, Except.pure] at h
    · cases hr : read input with
      | error e => simp [he, hr, bind, Except.bind] at h
      | ok p =>
        obtain ⟨w, rest⟩ := p
        cases hg : children.go f rest with
        | error e => simp [he, hr, hg, bind, Except.bind] at h
        | ok ws =>
          simp [he, hr, hg, bind, Except.bind, pure, Except.pure] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨f, rest, rfl, rfl, hg⟩

/-- A read of siblings that returns no value has read an empty input. -/
theorem isEmpty_of_children_go_eq_ok_nil {fuel : Nat} {input : ByteArray}
    (h : children.go fuel input = .ok []) : input.isEmpty = true := by
  cases fuel with
  | zero =>
    rw [children_go_zero] at h
    split at h
    · assumption
    · simp at h
  | succ f =>
    rw [children_go_succ] at h
    by_cases he : input.isEmpty = true
    · exact he
    · cases hr : read input with
      | error e => simp [he, hr, bind, Except.bind] at h
      | ok p =>
        cases hg : children.go f p.2 with
        | error e => simp [he, hr, hg, bind, Except.bind] at h
        | ok ws => simp [he, hr, hg, bind, Except.bind, pure, Except.pure] at h

/-- A value read first, then siblings read from the rest, are the siblings of the input. -/
theorem children_go_succ_eq_ok_of_read {fuel : Nat} {input rest : ByteArray} {v : Value}
    {vs : List Value} (h : read input = .ok (v, rest))
    (hg : children.go fuel rest = .ok vs) :
    children.go (fuel + 1) input = .ok (v :: vs) := by
  obtain ⟨hv, hs⟩ := size_lt_of_read_ok h
  have he : input.isEmpty = false := by
    simp only [ByteArray.isEmpty, beq_eq_false_iff_ne, ne_eq]
    omega
  simp [children_go_succ, he, h, hg, bind, Except.bind, pure, Except.pure]

/-- An empty input has no siblings, whatever the fuel. -/
theorem children_go_empty (fuel : Nat) : children.go fuel ⟨#[]⟩ = .ok [] := by
  cases fuel <;> rfl

/-- Two siblings are read in turn, and nothing follows them. -/
theorem exists_read_of_children_eq_ok_pair {input : ByteArray} {a b : Value}
    (h : children input = .ok [a, b]) :
    ∃ rest last, read input = .ok (a, rest) ∧ read rest = .ok (b, last) ∧
      last.isEmpty = true := by
  obtain ⟨f, rest, -, ha, h⟩ := exists_of_children_go_eq_ok_cons h
  obtain ⟨g, last, -, hb, h⟩ := exists_of_children_go_eq_ok_cons h
  exact ⟨rest, last, ha, hb, isEmpty_of_children_go_eq_ok_nil h⟩

/-- Each value that a read of siblings returns has a header and is at most as long as the input. -/
theorem children_go_sizes : ∀ (fuel : Nat) (input : ByteArray) (vs : List Value),
    children.go fuel input = .ok vs →
      ∀ v ∈ vs, v.content.size < v.encoded.size ∧ v.encoded.size ≤ input.size := by
  intro fuel
  induction fuel with
  | zero =>
    intro input vs h v hv
    rw [children_go_zero] at h
    split at h
    · cases h
      simp at hv
    · cases h
  | succ fuel ih =>
    intro input vs h v hv
    rw [children_go_succ] at h
    by_cases he : input.isEmpty = true
    · simp only [he, ite_true, pure, Except.pure, bind, Except.bind, Except.ok.injEq] at h
      subst h
      simp at hv
    · cases hr : read input with
      | error e => simp [he, hr, bind, Except.bind] at h
      | ok p =>
        obtain ⟨w, rest⟩ := p
        obtain ⟨hw, hsize⟩ := size_lt_of_read_ok hr
        cases hg : children.go fuel rest with
        | error e => simp [he, hr, hg, bind, Except.bind] at h
        | ok ws =>
          simp only [he, hr, hg, Bool.false_eq_true, ite_false, bind, Except.bind, pure,
            Except.pure, Except.ok.injEq] at h
          subst h
          rcases List.mem_cons.mp hv with rfl | hv
          · exact ⟨hw, by omega⟩
          · have := ih rest ws hg v hv
            omega

/-- Two checks that agree on each value agree on the list. -/
private theorem forM_congr {F G : Value → Except Error Unit} :
    ∀ vs : List Value, (∀ v ∈ vs, F v = G v) → vs.forM F = vs.forM G
  | [], _ => rfl
  | v :: vs, h => by
    show (F v >>= fun _ => vs.forM F) = (G v >>= fun _ => vs.forM G)
    rw [h v (by simp), forM_congr vs (fun w hw => h w (by simp [hw]))]

/-- Validation of a read value gives one verdict for every fuel above its encoded size. -/
private theorem go_fuel : ∀ (f g : Nat) (w : Value), w.content.size < w.encoded.size →
    w.encoded.size < f → w.encoded.size < g → validate.go f w = validate.go g w := by
  intro f
  induction f with
  | zero => intros; omega
  | succ f ih =>
    intro g w hw hf hg
    cases g with
    | zero => omega
    | succ g =>
      rw [validate.go, validate.go]
      split <;> try rfl
      all_goals
        cases hc : children w.content with
        | error e => rfl
        | ok vs =>
          have hvs : vs.forM (validate.go f) = vs.forM (validate.go g) := by
            apply forM_congr
            intro v hv
            have := children_go_sizes _ _ _ hc v hv
            exact ih g v this.1 (by omega) (by omega)
          simp only [bind, Except.bind, hvs]

/-- A constructed value passes validation exactly when its content reads as values that pass.

A SET OF also needs the encodings of those values in ascending order. -/
private theorem validate_constructed_ok_iff {value : Value}
    (tag : value.tag.toNat = 48 ∨ value.tag.toNat = 49)
    (header : value.content.size < value.encoded.size) :
    validate value = .ok () ↔ ∃ values, children value.content = .ok values ∧
      (value.tag = 49 → (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·)) ∧
        ∀ v ∈ values, validate v = .ok () := by
  have hforM : ∀ vs, children value.content = .ok vs →
      (vs.forM (validate.go value.encoded.size) = .ok () ↔
        ∀ v ∈ vs, validate v = .ok ()) := by
    intro vs hc
    rw [forM_ok_iff]
    have hgo : ∀ v ∈ vs, validate.go value.encoded.size v = validate v := by
      intro v hv
      have := children_go_sizes _ _ _ hc v hv
      exact go_fuel _ _ v this.1 (by omega) (by omega)
    constructor
    · intro h v hv
      rw [← hgo v hv]
      exact h v hv
    · intro h v hv
      rw [hgo v hv]
      exact h v hv
  rw [validate, validate.go]
  rcases tag with h | h <;> simp only [h] <;>
    cases hc : children value.content with
    | error e => simp [bind, Except.bind]
    | ok vs =>
      simp only [bind, Except.bind, Except.ok.injEq, exists_eq_left', ← hforM vs hc]
      by_cases h49 : value.tag = 49
      · by_cases hp : (vs.map (·.encoded.data.toList)).Pairwise (· ≤ ·)
        · simp [h49, hp]
        · simp [h49, hp, throw, throwThe, MonadExceptOf.throw]
      · simp [h49]

/-- A SEQUENCE passes validation exactly when its content reads as values that each pass.

Every value that the reader returns has a header, so its encoding is longer than its content. -/
theorem validate_sequence_ok_iff {value : Value} (tag : value.tag = 48)
    (header : value.content.size < value.encoded.size) :
    validate value = .ok () ↔ ∃ values, children value.content = .ok values ∧
      ∀ v ∈ values, validate v = .ok () := by
  rw [validate_constructed_ok_iff (.inl (by rw [tag]; rfl)) header]
  simp [tag]

/-- Every value in a read of siblings reads on its own. -/
private theorem exists_read_of_mem_children_go : ∀ (fuel : Nat) (input : ByteArray)
    (vs : List Value), children.go fuel input = .ok vs →
      ∀ v ∈ vs, ∃ a rest, read a = .ok (v, rest) := by
  intro fuel input vs
  induction vs generalizing fuel input with
  | nil => intro _ v hv; simp at hv
  | cons w ws ih =>
    intro h v hv
    obtain ⟨f, rest, -, hw, h⟩ := exists_of_children_go_eq_ok_cons h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨input, rest, hw⟩
    · exact ih f rest h v hv

/-- Siblings are in ascending order exactly when they are once padded with zero octets.

So the order check of a SET OF is the order of X.690 §11.6. -/
theorem pairwise_le_iff_padded {input : ByteArray} {values : List Value}
    (h : children input = .ok values) (n : Nat) :
    (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·) ↔
      (values.map fun v => v.encoded.data.toList ++
        List.replicate (n - v.encoded.size) 0).Pairwise (· ≤ ·) := by
  rw [List.pairwise_map, List.pairwise_map]
  apply List.Pairwise.iff_of_mem
  intro v w hv hw
  -- Each sibling reads, so each pair compares alike with or without the padding.
  obtain ⟨a, rest, ha⟩ := exists_read_of_mem_children_go _ _ _ h v hv
  obtain ⟨b, rest', hb⟩ := exists_read_of_mem_children_go _ _ _ h w hw
  exact encoded_le_iff_padded ha hb n

/-- A SET OF passes validation exactly when its content reads as values that each pass.

Their encodings must also come in ascending order, compared octet by octet, a proper prefix first.

X.690 §11.6 pads the shorter encoding with zero octets instead, which never changes the order.

Every value that the reader returns has a header, so its encoding is longer than its content. -/
theorem validate_set_ok_iff {value : Value} (tag : value.tag = 49)
    (header : value.content.size < value.encoded.size) :
    validate value = .ok () ↔ ∃ values, children value.content = .ok values ∧
      (values.map (·.encoded.data.toList)).Pairwise (· ≤ ·) ∧
        ∀ v ∈ values, validate v = .ok () := by
  rw [validate_constructed_ok_iff (.inr (by rw [tag]; rfl)) header]
  simp [tag]

/-! ## ECDSA signatures

Rule 1 of BIP 62 asks for strict DER, which its section [DER encoding][bip62der] spells out.

An INTEGER content starts with `0x00` only when the next byte is `0x80` or more.

So a positive number gets a leading zero byte exactly when its first nonzero byte is `0x80` or more.

The decoder accepts a signature only when the encoder writes the same bytes back.

[bip62der]: https://github.com/bitcoin/bips/blob/24e96e870fffaa257b465ce1f0370c14aac588e8/bip-0062.mediawiki#der-encoding
-/

/-- On `i + 1` bytes, the first byte is `n / 256 ^ i` modulo 256, then `n` follows on `i` bytes. -/
private theorem toBE_succ_eq_cons (i n : Nat) :
    (ByteOrder.toBE (i + 1) n).toList
      = UInt8.ofNat (n / 256 ^ i) :: (ByteOrder.toBE i n).toList := by
  rw [Nat.add_comm, ByteOrder.toList_toBE_add]
  rfl

/-- A number below `2 ^ 256` with `i + 1` significant bytes has them as its fewest bytes. -/
private theorem minimal_toBE {n i : Nat} (hn : n < 2 ^ 256) (low : 256 ^ i ≤ n)
    (high : n < 256 ^ (i + 1)) :
    (ByteOrder.toBE (ByteOrder.byteLength (n % 256 ^ 32)) (n % 256 ^ 32)).toList
      = (ByteOrder.toBE (i + 1) n).toList := by
  have h256 : n < 256 ^ 32 := by simpa using hn
  rw [Nat.mod_eq_of_lt h256, ByteOrder.byteLength_eq_of_bounds low high]

/-- The DER INTEGER of a number below `2 ^ 256`, as BIP 62 spells out strict DER.

Its content is the number on `k` big-endian bytes, for the `k` that meets two bounds.

The number is below `2 ^ (8 * k - 1)`, and, for `k` above 1, at least `2 ^ (8 * (k - 1) - 1)`.

These bounds pick the fewest bytes such that the first has its top bit clear. -/
theorem ecdsaInteger_eq {n k : Nat} (hn : n < 2 ^ 256) (high : n < 2 ^ (8 * k - 1))
    (low : k = 1 ∨ 2 ^ (8 * (k - 1) - 1) ≤ n) :
    ecdsaInteger n = [0x02, UInt8.ofNat k] ++ (ByteOrder.toBE k n).toList := by
  obtain _ | j := k
  · simp at high low; omega
  have hhigh : n < 128 * 256 ^ j := by
    rw [show 8 * (j + 1) - 1 = 7 + 8 * j by omega, Nat.pow_add, Nat.pow_mul] at high
    simpa using high
  have h256 : n < 256 ^ 32 := by simpa using hn
  -- With the two bounds, the first content byte is below `0x80`.
  by_cases hj : 256 ^ j ≤ n
  · have hj32 : j < 32 := (Nat.pow_lt_pow_iff_right (a := 256) (by decide)).mp (by omega)
    have hdiv : n / 256 ^ j < 128 :=
      (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr (by omega)
    have hdrop := minimal_toBE (i := j) hn hj (by rw [Nat.pow_succ]; omega)
    rw [toBE_succ_eq_cons j n] at hdrop ⊢
    have : ¬ (UInt8.ofNat (n / 256 ^ j)).toNat ≥ 128 := by
      rw [UInt8.toNat_ofNat_of_lt' (by rw [UInt8.size]; omega)]; omega
    simp only [ecdsaInteger, hdrop]
    rw [ite_eq_right this]
    simp
  -- It is `0x00` only before `0x80` or more.
  · obtain _ | i := j
    -- Zero is one content byte, `0x00`.
    · have hzero : n = 0 := by simp at hj; omega
      subst hzero
      decide
    · have hlow : 128 * 256 ^ i ≤ n := by
        rcases low with h | h
        · omega
        · rw [show 8 * (i + 1 + 1 - 1) - 1 = 7 + 8 * i by omega, Nat.pow_add, Nat.pow_mul] at h
          simpa using h
      have hdrop := minimal_toBE (n := n) (i := i) hn (by omega) (by omega)
      have hdiv : 128 ≤ n / 256 ^ i :=
        (Nat.le_div_iff_mul_le (Nat.pow_pos (by decide))).mpr (by omega)
      have hdiv256 : n / 256 ^ i < 256 :=
        (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).mpr
          (by rw [Nat.pow_succ] at hj; omega)
      rw [toBE_succ_eq_cons i n] at hdrop
      rw [toBE_succ_eq_cons (i + 1) n, Nat.div_eq_of_lt (by omega),
        toBE_succ_eq_cons i n]
      have : (UInt8.ofNat (n / 256 ^ i)).toNat ≥ 128 := by
        rw [UInt8.toNat_ofNat_of_lt' hdiv256]; omega
      simp only [ecdsaInteger, hdrop]
      rw [ite_eq_left this]
      simp

-- The bound for 33 bytes is `2 ^ 263`, above the default threshold for evaluating a power.
set_option exponentiation.threshold 263 in
/-- Every number below `2 ^ 256` has a byte count from 1 to 33 that meets the bounds above. -/
theorem exists_derByteCount {n : Nat} (hn : n < 2 ^ 256) :
    ∃ k, 1 ≤ k ∧ k ≤ 33 ∧ n < 2 ^ (8 * k - 1) ∧
      (k = 1 ∨ 2 ^ (8 * (k - 1) - 1) ≤ n) := by
  suffices h : ∀ k, 1 ≤ k → k ≤ 33 → n < 2 ^ (8 * k - 1) →
      ∃ k, 1 ≤ k ∧ k ≤ 33 ∧ n < 2 ^ (8 * k - 1) ∧
        (k = 1 ∨ 2 ^ (8 * (k - 1) - 1) ≤ n) from
    h 33 (by decide) (by decide) (Nat.lt_trans hn (by decide))
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro h1 h33 high
    by_cases hk : k = 0
    · exact ⟨k + 1, h1, h33, high, .inl (by omega)⟩
    by_cases hlow : 2 ^ (8 * (k + 1 - 1) - 1) ≤ n
    · exact ⟨k + 1, h1, h33, high, .inr hlow⟩
    · exact ih (by omega) (by omega)
        (by rw [show 8 * k - 1 = 8 * (k + 1 - 1) - 1 by omega]; omega)

/-- Every number below `2 ^ 256` has its DER INTEGER on at most 33 content bytes. -/
private theorem exists_ecdsaInteger_eq {n : Nat} (hn : n < 2 ^ 256) :
    ∃ k, 1 ≤ k ∧ k ≤ 33 ∧ n < 256 ^ k ∧
      ecdsaInteger n = [0x02, UInt8.ofNat k] ++ (ByteOrder.toBE k n).toList := by
  obtain ⟨k, h1, h33, high, low⟩ := exists_derByteCount hn
  refine ⟨k, h1, h33, ?_, ecdsaInteger_eq hn high low⟩
  have : 2 ^ (8 * k - 1) ≤ 256 ^ k := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- The scalar reader accepts exactly the encodings of r and s in [1, 2^256), BIP 62.

It returns those r and s.

So each accepted pair r, s has exactly one byte encoding. -/
theorem decodeEcdsaScalars_eq_some_iff {signature : ByteArray} {r s : Nat} :
    decodeEcdsaScalars signature = some (r, s) ↔
      0 < r ∧ r < 2 ^ 256 ∧ 0 < s ∧ s < 2 ^ 256 ∧ encodeEcdsaSignature r s = signature := by
  constructor
  -- The last check of the reader is that the encoder writes the same bytes back.
  --
  -- So acceptance gives the encoding.
  · intro h
    unfold decodeEcdsaScalars at h
    split at h
    · split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · dsimp only at h
            split at h
            · rename_i hc
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hc
            · simp at h
        · simp at h
    · simp at h
  -- The converse is the content: the reader parses back every encoding of scalars in that range.
  · rintro ⟨hr, hr256, hs, hs256, rfl⟩
    obtain ⟨kr, hkr1, hkr, hrk, hder_r⟩ := exists_ecdsaInteger_eq hr256
    obtain ⟨ks, hks1, hks, hsk, hder_s⟩ := exists_ecdsaInteger_eq hs256
    have hdata : (encodeEcdsaSignature r s).data.toList =
        0x30 :: UInt8.ofNat (kr + ks + 4) :: 0x02 :: UInt8.ofNat kr ::
          ((ByteOrder.toBE kr r).toList
            ++ 0x02 :: UInt8.ofNat ks :: (ByteOrder.toBE ks s).toList) := by
      simp [encodeEcdsaSignature, hder_r, hder_s]
      apply UInt8.toNat_inj.mp
      simp
      omega
    have hsize : (encodeEcdsaSignature r s).size = kr + ks + 6 := by
      rw [ByteArray.size, ← Array.length_toList, hdata]
      simp
      omega
    have hkr8 : (UInt8.ofNat kr).toNat = kr := UInt8.toNat_ofNat_of_lt' (by rw [UInt8.size]; omega)
    have hks8 : (UInt8.ofNat ks).toNat = ks := UInt8.toNat_ofNat_of_lt' (by rw [UInt8.size]; omega)
    have htotal : (UInt8.ofNat (kr + ks + 4)).toNat = kr + ks + 4 :=
      UInt8.toNat_ofNat_of_lt' (by rw [UInt8.size]; omega)
    have hcond : 0 < r ∧ r < 2 ^ 256 ∧ 0 < s ∧ s < 2 ^ 256 ∧
        encodeEcdsaSignature r s = encodeEcdsaSignature r s := ⟨hr, hr256, hs, hs256, rfl⟩
    unfold decodeEcdsaScalars
    rw [hdata]
    simp only [hsize, htotal, hkr8, hks8, List.take_left' (ByteOrder.length_toList_toBE kr r),
      List.drop_left' (ByteOrder.length_toList_toBE kr r), ByteOrder.length_toList_toBE,
      ByteOrder.ofBE_toBE_of_lt hrk, ByteOrder.ofBE_toBE_of_lt hsk]
    simp only [hcond, and_self, ite_true]
    simp

end EthLib.Serialization.Proofs.Der
