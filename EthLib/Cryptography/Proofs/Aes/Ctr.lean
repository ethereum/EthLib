module

public import EthLib.Cryptography.Aes.Ctr

/-!
# Proofs: `Aes.Ctr`

CTR decryption returns the plaintext, for every cipher, counter and message.

The output has the length of the input.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes

/-- XOR with a key stream twice gives back the data, when the stream is long enough. -/
theorem zipWith_xor_xor (a k : List UInt8) (h : a.length ≤ k.length) :
    List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) a k) k = a := by
  induction a generalizing k with
  | nil => simp
  | cons x a ih =>
    cases k with
    | nil => simp at h
    | cons y k =>
      simp only [List.zipWith_cons_cons, UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]
      rw [ih k (by simpa using h)]

/-- The output of the loop is the output so far, then the output of the loop from nothing. -/
theorem xorKeystream.go_toList (ciph : Block → Block) (m n : Nat) (T : Block)
    (data : List UInt8) (out : Array UInt8) :
    (go ciph m n T data out).toList = out.toList ++ (go ciph m n T data #[]).toList := by
  induction n generalizing T data out with
  | zero => simp [go]
  | succ n ih => rw [go, go, ih, ih (out := #[] ++ _)]; simp

/-- No blocks give no output. -/
theorem xorKeystream_zero (ciph : Block → Block) (m : Nat) (T : Block) (data : List UInt8) :
    xorKeystream ciph m 0 T data = [] := rfl

/-- The first block of the output is the first block of data XOR the cipher of the counter.

The rest is the output of the next counter on the rest of the data. -/
theorem xorKeystream_succ (ciph : Block → Block) (m n : Nat) (T : Block) (data : List UInt8) :
    xorKeystream ciph m (n + 1) T data =
      List.zipWith (· ^^^ ·) (data.take 16) (ciph T).toList ++
        xorKeystream ciph m n (inc m T) (data.drop 16) := by
  rw [xorKeystream, xorKeystream.go, xorKeystream.go_toList, xorKeystream]
  simp

theorem xorKeystream_nil (ciph : Block → Block) (m n : Nat) (T : Block) :
    xorKeystream ciph m n T [] = [] := by
  induction n generalizing T with
  | zero => rfl
  | succ n ih => simp [xorKeystream_succ, ih]

/-- The output has the length of the data, when the blocks cover it. -/
theorem length_xorKeystream (ciph : Block → Block) (m n : Nat) (T : Block) (data : List UInt8)
    (h : data.length ≤ 16 * n) : (xorKeystream ciph m n T data).length = data.length := by
  induction n generalizing T data with
  | zero => simp_all [xorKeystream_zero]
  | succ n ih =>
    simp only [xorKeystream_succ, List.length_append, List.length_zipWith, List.length_take,
      Vector.length_toList]
    rw [ih _ _ (by simp; omega)]
    simp only [List.length_drop]
    omega

/-- Running the key stream twice gives back the data. -/
theorem xorKeystream_xorKeystream (ciph : Block → Block) (m n : Nat) (T : Block)
    (data : List UInt8) (h : data.length ≤ 16 * n) :
    xorKeystream ciph m n T (xorKeystream ciph m n T data) = data := by
  induction n generalizing T data with
  | zero => simp_all [xorKeystream_zero]
  | succ n ih =>
    -- The first block of the output is the XOR of the first block of the data.
    have first :
        (List.zipWith (· ^^^ ·) (data.take 16) (ciph T).toList).length = min data.length 16 := by
      simp [List.length_take]; omega
    by_cases full : 16 ≤ data.length
    · -- A full first block: the output splits after 16 bytes, at the same place.
      simp only [xorKeystream_succ]
      rw [List.take_left' (by rw [first]; omega), List.drop_left' (by rw [first]; omega),
        zipWith_xor_xor _ _ (by simp; omega), ih _ _ (by simp; omega), List.take_append_drop]
    · -- A partial last block: the rest of the data is empty.
      have rest : data.drop 16 = [] := List.drop_eq_nil_of_le (by omega)
      have short : data.take 16 = data := List.take_of_length_le (by omega)
      simp only [short] at first
      simp only [xorKeystream_succ, rest, short, xorKeystream_nil, List.append_nil]
      rw [List.take_of_length_le (by rw [first]; omega),
        List.drop_eq_nil_of_le (by rw [first]; omega),
        xorKeystream_nil, List.append_nil, zipWith_xor_xor _ _ (by simp; omega)]

/-- CTR keeps the length of the data. -/
theorem size_ctr (ciph : Block → Block) (m : Nat) (T : Block) (data : ByteArray) :
    (ctr ciph m T data).size = data.size := by
  simp only [ctr, ByteArray.size]
  simp only [List.size_toArray]
  rw [length_xorKeystream _ _ _ _ _ (by simp; omega)]
  simp

/-- CTR decryption of SP 800-38A §6.5 undoes CTR encryption with the same cipher and counters.

It holds for every forward cipher, so for AES under every key. -/
theorem ctr_ctr (ciph : Block → Block) (m : Nat) (T : Block) (data : ByteArray) :
    ctr ciph m T (ctr ciph m T data) = data := by
  apply ByteArray.ext
  -- The outer call cuts the output of the inner one into as many blocks as the data.
  show (xorKeystream ciph m (((ctr ciph m T data).size + 15) / 16) T
    (ctr ciph m T data).data.toList).toArray = data.data
  rw [size_ctr]
  simp only [ctr, List.toList_toArray]
  rw [xorKeystream_xorKeystream _ _ _ _ _ (by rw [Array.length_toList]; show data.size ≤ _; omega)]

end EthLib.Cryptography.Aes
