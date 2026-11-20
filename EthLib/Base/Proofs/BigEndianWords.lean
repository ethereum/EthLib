module

public import EthLib.Base.BigEndianWords

/-!
# Proofs for big-endian word conversion

Reading by words gives the same integer as the byte-wise fold.

The direct writer gives the same bytes as appending a big-endian list.
-/

@[expose] public section

namespace EthLib.Base

/-- Read big-endian bytes in groups of eight, with a byte-wise fold for the last short group. -/
private def bytesToNatWords (bytes : List UInt8) : Nat := go bytes 0
where
  go : List UInt8 → Nat → Nat
    | a :: b :: c :: d :: e :: f :: g :: h :: rest, acc =>
        go rest ((acc <<< 64) + (readWord a b c d e f g h).toNat)
    | rest, acc => rest.foldl (fun n byte => n * 256 + byte.toNat) acc

private theorem readWord_toNat (a b c d e f g h : UInt8) :
    (readWord a b c d e f g h).toNat = bytesToNat [a,b,c,d,e,f,g,h] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have he := e.toNat_lt
  have hf := f.toNat_lt
  have hg := g.toNat_lt
  have hh := h.toNat_lt
  simp only [readWord, appendByte, UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64,
    UInt64.reduceToNat, bytesToNat, List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  omega

private theorem step_eq (acc : Nat) (a b c d e f g h : UInt8) :
    (acc <<< 64) + (readWord a b c d e f g h).toNat =
      [a,b,c,d,e,f,g,h].foldl (fun n byte => n * 256 + byte.toNat) acc := by
  rw [readWord_toNat, Nat.shiftLeft_eq, foldl_bytesToNat]
  have hlen : ([a,b,c,d,e,f,g,h] : List UInt8).length = 8 := rfl
  rw [hlen, show 256 ^ 8 = 2^64 by decide]

private theorem bytesToNatWords.go_eq (bytes : List UInt8) (acc : Nat) :
    bytesToNatWords.go bytes acc = bytes.foldl (fun n byte => n * 256 + byte.toNat) acc := by
  fun_induction bytesToNatWords.go bytes acc with
  | case1 a b c d e f g h rest acc ih =>
    rw [ih, step_eq]
    simp only [List.foldl_cons, List.foldl_nil]
  | case2 rest acc h => rfl

/-- Reading by words gives the same integer as the byte-wise fold. -/
private theorem bytesToNatWords_eq (bytes : List UInt8) :
    bytesToNatWords bytes = bytesToNat bytes :=
  bytesToNatWords.go_eq bytes 0

/-- Read 32 indexed big-endian bytes as four words. -/
@[inline] def indexedBytesToNat32 (byte : Fin 32 → UInt8) : Nat :=
  withIndexedWords32 byte fun a b c d =>
    (((((a.toNat <<< 64) + b.toNat) <<< 64) + c.toNat) <<< 64) + d.toNat

/-- Indexed word reads preserve the big-endian integer. -/
private theorem indexedBytesToNat32_eq (byte : Fin 32 → UInt8) :
    indexedBytesToNat32 byte = bytesToNat (List.ofFn byte) := by
  have h : List.ofFn byte = [
    byte 0, byte 1, byte 2, byte 3, byte 4, byte 5, byte 6, byte 7,
    byte 8, byte 9, byte 10, byte 11, byte 12, byte 13, byte 14, byte 15,
    byte 16, byte 17, byte 18, byte 19, byte 20, byte 21, byte 22, byte 23,
    byte 24, byte 25, byte 26, byte 27, byte 28, byte 29, byte 30, byte 31] := by
    simp only [List.ofFn_succ, List.ofFn_zero]
    rfl
  rw [← bytesToNatWords_eq, h]
  simp only [indexedBytesToNat32, withIndexedWords32, bytesToNatWords, bytesToNatWords.go,
    List.foldl_nil,
    Nat.zero_shiftLeft, Nat.zero_add]

/-- Read a 32-byte block directly from a byte array. -/
@[inline] def byteArrayToNat32 (bytes : ByteArray) (start : Nat)
    (h : start + 32 ≤ bytes.size) : Nat :=
  indexedBytesToNat32 (fun i => bytes[start + i.val]'(by omega))

/-- A block read gives the big-endian integer of the corresponding slice. -/
theorem byteArrayToNat32_eq (bytes : ByteArray) (start : Nat)
    (h : start + 32 ≤ bytes.size) :
    byteArrayToNat32 bytes start h = bytesToNat ((bytes.data.toList.drop start).take 32) := by
  rw [byteArrayToNat32, indexedBytesToNat32_eq]
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, List.length_drop, Array.length_toList,
      ByteArray.size_data]
    omega
  · intro i hi hj
    rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop,
      ByteArray.getElem_eq_getElem_data, Array.getElem_toList]

/-- Prepend the requested low bytes of a word in big-endian order. -/
private def pushWordBytes : Nat → UInt64 → List UInt8 → List UInt8
  | 0, _, rest => rest
  | k+1, word, rest => pushWordBytes k (word >>> 8) (word.toUInt8 :: rest)

private theorem pushWordBytes_eq (n : Nat) (w : UInt64) (rest : List UInt8) :
    pushWordBytes n w rest = natToBytes.go n w.toNat rest := by
  induction n generalizing w rest with
  | zero => rfl
  | succ n ih =>
    simp only [pushWordBytes, natToBytes.go, ih]
    have hshift : (w >>> (8 : UInt64)).toNat = w.toNat / 256 := by
      rw [UInt64.toNat_shiftRight]
      exact Nat.shiftRight_eq_div_pow w.toNat 8
    have hbyte : w.toUInt8 = UInt8.ofNat w.toNat := by
      apply UInt8.toNat_inj.mp
      rfl
    rw [hshift, hbyte]

private theorem natToBytes_go_of_modEq (len a b : Nat) (rest : List UInt8)
    (h : a % 256 ^ len = b % 256 ^ len) : natToBytes.go len a rest = natToBytes.go len b rest := by
  induction len generalizing a b rest with
  | zero => rfl
  | succ len ih =>
    have pow : 256 ^ (len + 1) = 256 * 256 ^ len := by rw [Nat.pow_succ, Nat.mul_comm]
    have hlow : a % 256 = b % 256 := by
      rw [pow] at h
      rw [← Nat.mod_mul_right_mod a 256 (256 ^ len), ← Nat.mod_mul_right_mod b 256 (256 ^ len), h]
    have hhigh : (a / 256) % (256 ^ len) = (b / 256) % (256 ^ len) := by
      rw [pow] at h
      rw [← Nat.mod_mul_right_div_self a 256 (256^len),
        ← Nat.mod_mul_right_div_self b 256 (256^len), h]
    have e : UInt8.ofNat a = UInt8.ofNat b := UInt8.toNat_inj.mp hlow
    rw [natToBytes.go, natToBytes.go, e, ih _ _ _ hhigh]

private theorem pushLowWord_eq (n : Nat) (rest : List UInt8) :
    pushWordBytes 8 n.toUInt64 rest = natToBytes.go 8 n rest := by
  rw [pushWordBytes_eq]
  apply natToBytes_go_of_modEq
  change ((n % 2^64) % 256^8) = n % 256^8
  exact Nat.mod_mod _ _

/-- Write the low 256 bits as 32 big-endian bytes, using four 64-bit words. -/
private def natToBytes32 (n : Nat) : List UInt8 :=
  let b0 := pushWordBytes 8 n.toUInt64 []
  let b1 := pushWordBytes 8 (n >>> 64).toUInt64 b0
  let b2 := pushWordBytes 8 (n >>> 128).toUInt64 b1
  pushWordBytes 8 (n >>> 192).toUInt64 b2

private theorem go_add (m n x : Nat) (rest : List UInt8) :
    natToBytes.go (m + n) x rest =
      natToBytes.go m (x / 256^n) (natToBytes.go n x rest) := by
  induction n generalizing x rest with
  | zero => simp [natToBytes.go]
  | succ n ih =>
    rw [Nat.add_succ, natToBytes.go, ih, natToBytes.go, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm]

/-- Writing by words gives the same 32 bytes as writing one byte at a time. -/
private theorem natToBytes32_eq (n : Nat) : natToBytes32 n = natToBytes 32 n := by
  unfold natToBytes32 natToBytes
  simp only [pushLowWord_eq, Nat.shiftRight_eq_div_pow]
  conv => rhs; change natToBytes.go (24 + 8) n []; rw [go_add]
  conv => rhs; arg 1; change 16 + 8
  conv => rhs; rw [go_add]
  conv => rhs; arg 1; change 8 + 8
  conv => rhs; rw [go_add]
  simp only [Nat.div_div_eq_div_mul]

private theorem pushWord64_toList (out : ByteArray) (w : UInt64) :
    (pushWord64 out w).data.toList = out.data.toList ++ pushWordBytes 8 w [] := by
  simp only [pushWord64, ByteArray.data_push, Array.toList_push, pushWordBytes,
    List.append_assoc, List.cons_append, List.nil_append]

/-- Writing directly gives the same bytes as constructing a list and appending it. -/
theorem pushNatBytes32_toList (out : ByteArray) (n : Nat) :
    (pushNatBytes32 out n).data.toList = out.data.toList ++ natToBytes 32 n := by
  rw [← natToBytes32_eq n]
  simp only [pushNatBytes32, pushWord64_toList, natToBytes32, pushWordBytes_eq,
    natToBytes.go_append, List.append_nil, List.append_assoc]

end EthLib.Base
