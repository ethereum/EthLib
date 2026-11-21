module

/-!
# Proofs: the list of a byte array

Reading a byte array one byte at a time gives the bytes of its array, in order.
-/

@[expose] public section

namespace EthLib.Base

/-- The bytes of a byte array, read one by one, are the bytes of its array. -/
theorem toList_eq_data_toList (bytes : ByteArray) : bytes.toList = bytes.data.toList := by
  have length : bytes.data.toList.length = bytes.size := Array.length_toList
  -- From index `i` on, the loop puts the bytes it has read back in order, then the rest.
  have loop : ∀ i out, i ≤ bytes.size →
      ByteArray.toList.loop bytes i out = out.reverse ++ bytes.data.toList.drop i := by
    intro i out bound
    fun_induction ByteArray.toList.loop bytes i out with
    | case1 i out more ih =>
      rw [ih (by omega)]
      have get : bytes.get! i = bytes.data.toList[i]'(by omega) := by
        obtain ⟨data⟩ := bytes
        exact (getElem!_pos data i more).trans (Array.getElem_toList _).symm
      rw [get, List.reverse_cons, List.append_assoc, List.singleton_append,
        ← List.drop_eq_getElem_cons]
    | case2 i out done =>
      rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
  unfold ByteArray.toList
  simpa using loop 0 [] (Nat.zero_le _)

end EthLib.Base
