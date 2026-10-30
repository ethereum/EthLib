import EthLib.Serialization.Rlp.Item

/-!
# `Serialization.Proofs.Rlp.Item`

`bigEndian` is `BE` of the Yellow Paper.

The Yellow Paper defines `BE(x)` by two properties of its bytes `b`:

- `b_0` is not zero;
- `x = sum_n b_n * 256^(k - 1 - n)`, where `k` is the number of bytes.

`bigEndian_value` and `bigEndian_head_ne_zero` prove both.

`bigEndian_unique` proves that no other bytes have them, so `BE` is well defined and `bigEndian` is it.

`bigEndian_size_le` bounds the number of bytes, which keeps the first byte of a prefix below 256.
-/

namespace EthLib.Serialization.Rlp

/-- Zero has no digits, whatever the budget. -/
theorem bigEndianAux_zero (fuel : Nat) : bigEndianAux 0 fuel = .empty := by
  cases fuel <;> simp [bigEndianAux]

/-- A nonzero number is its higher digits, then its lowest digit. -/
theorem bigEndianAux_succ (n fuel : Nat) (hn : n ≠ 0) :
    (bigEndianAux n (fuel + 1)).data.toList
      = (bigEndianAux (n / 256) fuel).data.toList ++ [UInt8.ofNat (n % 256)] := by
  simp [bigEndianAux, hn]

/-- Any budget of at least `n` bytes gives the same digits. -/
theorem bigEndianAux_fuel (n fuel fuel' : Nat) (h : n ≤ fuel) (h' : n ≤ fuel') :
    bigEndianAux n fuel = bigEndianAux n fuel' := by
  induction fuel generalizing n fuel' with
  | zero =>
    -- A budget of 0 serves only `n = 0`, which has no digits.
    have hn : n = 0 := by omega
    subst hn
    simp [bigEndianAux_zero]
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn
      simp [bigEndianAux_zero]
    · -- Both budgets are positive, and both cover the higher digits `n / 256`.
      obtain ⟨g, rfl⟩ : ∃ g, fuel' = g + 1 := ⟨fuel' - 1, by omega⟩
      simp only [bigEndianAux, hn, ite_false]
      rw [ih (n / 256) g (by omega) (by omega)]

/-- With a budget of at least `n` bytes, the digits of `n` read back as `n`. -/
theorem ofBigEndian_bigEndianAux (fuel n : Nat) (h : n ≤ fuel) :
    ofBigEndian (bigEndianAux n fuel).data.toList = n := by
  induction fuel generalizing n with
  | zero => simp_all [bigEndianAux, ofBigEndian]
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn
      simp [bigEndianAux_zero, ofBigEndian]
    · rw [bigEndianAux_succ n fuel hn]
      -- The higher digits read back as `n / 256`.
      have hq := ih (n / 256) (by omega)
      simp only [ofBigEndian, List.foldl_append, List.foldl_cons, List.foldl_nil] at hq ⊢
      -- Then `256 * (n / 256) + n % 256 = n`.
      rw [hq, UInt8.toNat_ofNat']
      omega

/-- `BE(n)` read back in base 256 is `n`. -/
theorem bigEndian_value (n : Nat) : ofBigEndian (bigEndian n).data.toList = n :=
  ofBigEndian_bigEndianAux n n (Nat.le_refl n)

/-- `BE(n)` has no leading zero byte. -/
theorem bigEndian_head_ne_zero (n : Nat) : ∀ b ∈ (bigEndian n).data.toList.head?, b ≠ 0 := by
  suffices ∀ fuel n, n ≤ fuel → ∀ b ∈ (bigEndianAux n fuel).data.toList.head?, b ≠ 0 from
    this n n (Nat.le_refl n)
  intro fuel
  induction fuel with
  | zero => simp [bigEndianAux]
  | succ fuel ih =>
    intro n h
    by_cases hn : n = 0
    · subst hn
      simp [bigEndianAux_zero]
    · rw [bigEndianAux_succ n fuel hn]
      by_cases hq : n / 256 = 0
      · -- One digit: it is `n` itself, which is not zero.
        rw [hq, bigEndianAux_zero]
        intro b hb
        simp only [ByteArray.data_empty, Array.toList_empty, List.nil_append, List.head?_cons,
          Option.mem_def, Option.some.injEq] at hb
        subst hb
        intro h0
        have := congrArg UInt8.toNat h0
        simp [UInt8.toNat_ofNat'] at this
        omega
      · -- More digits: the first one is the first of `n / 256`, which reads back as nonzero.
        have hne : (bigEndianAux (n / 256) fuel).data.toList ≠ [] := by
          intro hnil
          have := ofBigEndian_bigEndianAux fuel (n / 256) (by omega)
          rw [hnil] at this
          simp [ofBigEndian] at this
          omega
        intro b hb
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hne
        rw [hx] at hb
        apply ih (n / 256) (by omega) b
        rw [hx]
        simpa using hb

/-- A number below `256^k` has at most `k` digits. -/
theorem bigEndian_size_le (n k : Nat) (h : n < 256 ^ k) : (bigEndian n).size ≤ k := by
  suffices ∀ fuel n k, n < 256 ^ k → (bigEndianAux n fuel).size ≤ k from this n n k h
  intro fuel
  induction fuel with
  | zero => simp [bigEndianAux]
  | succ fuel ih =>
    intro n k h
    by_cases hn : n = 0
    · subst hn
      simp [bigEndianAux_zero]
    · cases k with
      | zero =>
        -- `n < 256^0 = 1` makes `n` zero.
        simp at h
        omega
      | succ k =>
        -- One digit, then the digits of `n / 256 < 256^k`.
        simp only [bigEndianAux, hn, ite_false, ByteArray.size_push]
        have := ih (n / 256) k (by rw [Nat.pow_succ] at h; omega)
        omega

/-- Induction on a list of bytes from its last byte: a property of `[]` that survives appending a byte holds for every list. -/
private theorem snocInduction {motive : List UInt8 → Prop} (nil : motive [])
    (append_singleton : ∀ init last, motive init → motive (init ++ [last])) (bytes : List UInt8) :
    motive bytes := by
  rw [← List.reverse_reverse bytes]
  induction bytes.reverse with
  | nil => simpa using nil
  | cons last rest ih => simpa using append_singleton _ last ih

/-- Bytes that read back as 0 are all zero. -/
theorem ofBigEndian_eq_zero (bytes : List UInt8) (h : ofBigEndian bytes = 0) :
    ∀ b ∈ bytes, b = 0 := by
  induction bytes using snocInduction with
  | nil => simp
  | append_singleton init last ih =>
    simp only [ofBigEndian, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    -- `256 * v + last = 0` makes both `v` and `last` zero.
    have hInit : ofBigEndian init = 0 := by
      simp only [ofBigEndian]
      omega
    have hLast : last.toNat = 0 := by omega
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih hInit b hb
    · simp only [List.mem_singleton] at hb
      subst hb
      exact UInt8.toNat_inj.mp hLast

/-- Bytes with no leading zero are `BE` of the number they write.

So `BE(x)` is the only byte string with the two properties the Yellow Paper asks for. -/
theorem bigEndian_unique (bytes : List UInt8) (h : ∀ b ∈ bytes.head?, b ≠ 0) :
    (bigEndian (ofBigEndian bytes)).data.toList = bytes := by
  induction bytes using snocInduction with
  | nil => simp [ofBigEndian, bigEndian, bigEndianAux]
  | append_singleton init last ih =>
    -- The bytes write `m = 256 * v + last`, where `v` is the number `init` writes.
    have hm : ofBigEndian (init ++ [last]) = 256 * ofBigEndian init + last.toNat := by
      simp [ofBigEndian]
    by_cases hInit : init = []
    · -- One byte, nonzero, so `m` is that byte.
      subst hInit
      have hLast : last ≠ 0 := h last (by simp)
      have hPos : last.toNat ≠ 0 := fun h0 => hLast (UInt8.toNat_inj.mp h0)
      rw [hm]
      simp only [bigEndian]
      have hval : 256 * ofBigEndian [] + last.toNat = last.toNat := by simp [ofBigEndian]
      rw [hval]
      obtain ⟨g, hg⟩ : ∃ g, last.toNat = g + 1 := ⟨last.toNat - 1, by omega⟩
      rw [hg, bigEndianAux_succ _ _ (by omega), ← hg, show last.toNat / 256 = 0 by
        have := last.toNat_lt; omega, bigEndianAux_zero]
      simp [show last.toNat % 256 = last.toNat by have := last.toNat_lt; omega]
    · -- Several bytes: `init` has no leading zero, so `v` is not zero.
      have hInitHead : ∀ b ∈ init.head?, b ≠ 0 := by
        intro b hb
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hInit
        subst hx
        exact h b (by simpa using hb)
      have hv : ofBigEndian init ≠ 0 := by
        intro h0
        obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hInit
        have hx0 := ofBigEndian_eq_zero init h0 x (by simp [hx])
        exact hInitHead x (by simp [hx]) hx0
      -- Split off the lowest digit of `m`, which is `last`, and recurse on `v`.
      rw [hm]
      simp only [bigEndian]
      obtain ⟨g, hg⟩ : ∃ g, 256 * ofBigEndian init + last.toNat = g + 1 :=
        ⟨256 * ofBigEndian init + last.toNat - 1, by omega⟩
      have hlt := last.toNat_lt
      rw [hg, bigEndianAux_succ _ _ (by omega), ← hg,
        show (256 * ofBigEndian init + last.toNat) / 256 = ofBigEndian init by omega,
        show (256 * ofBigEndian init + last.toNat) % 256 = last.toNat by omega,
        bigEndianAux_fuel (ofBigEndian init) g (ofBigEndian init) (by omega) (Nat.le_refl _)]
      have := ih hInitHead
      simp only [bigEndian] at this
      rw [this]
      simp

end EthLib.Serialization.Rlp
