import EthLib.Cryptography.Proofs.Hash.Blake2s

/-!
# Proofs: a fast form of BLAKE2s for the kernel

A known answer is checked by the kernel, which evaluates the hash term by term.

The specification keeps the 16 working words in an array.

The kernel is slow at array reads and writes, so one compression costs it about 0.9 s.

This file states the same hash with one record field per word.

The kernel evaluates it about seven times faster.

```text
    array of 16 words   -->   record with fields v0 .. v15
    mix on the array     =    mixing function G on four fields
    hash input           =    hashFast input, for every input
```

The equality is proved once, for every input.

A known answer rewrites its hash to the fast form, then lets the kernel evaluate it.
-/

namespace EthLib.Cryptography.Hash.Blake2s

open private compress blockWords IV mix rotateRight from EthLib.Cryptography.Hash.Blake2s

/-! ## The working vector as a record -/

/-- The 16 words of the working vector `v_0, ..., v_15` of RFC 7693 Section 3.2. -/
structure Work where
  (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt32)

namespace Work

/-- The words in index order. -/
def toArray (w : Work) : Array UInt32 :=
  #[w.v0, w.v1, w.v2, w.v3, w.v4, w.v5, w.v6, w.v7,
    w.v8, w.v9, w.v10, w.v11, w.v12, w.v13, w.v14, w.v15]

/-- The record of the first 16 words of an array. -/
def ofArray (a : Array UInt32) : Work :=
  ⟨a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!,
   a[8]!, a[9]!, a[10]!, a[11]!, a[12]!, a[13]!, a[14]!, a[15]!⟩

/-- Read one word by index.

Past the end it reads zero, as an array read does.
-/
def get (w : Work) : Nat → UInt32
  | 0 => w.v0 | 1 => w.v1 | 2 => w.v2 | 3 => w.v3
  | 4 => w.v4 | 5 => w.v5 | 6 => w.v6 | 7 => w.v7
  | 8 => w.v8 | 9 => w.v9 | 10 => w.v10 | 11 => w.v11
  | 12 => w.v12 | 13 => w.v13 | 14 => w.v14 | 15 => w.v15
  | _ => 0

/-- Replace one word by index.

Past the end it changes nothing, as an array write does.
-/
def set (w : Work) : Nat → UInt32 → Work
  | 0, x => { w with v0 := x } | 1, x => { w with v1 := x }
  | 2, x => { w with v2 := x } | 3, x => { w with v3 := x }
  | 4, x => { w with v4 := x } | 5, x => { w with v5 := x }
  | 6, x => { w with v6 := x } | 7, x => { w with v7 := x }
  | 8, x => { w with v8 := x } | 9, x => { w with v9 := x }
  | 10, x => { w with v10 := x } | 11, x => { w with v11 := x }
  | 12, x => { w with v12 := x } | 13, x => { w with v13 := x }
  | 14, x => { w with v14 := x } | 15, x => { w with v15 := x }
  | _, _ => w

/-- Reading the array reads the record. -/
theorem getElem!_toArray (w : Work) (i : Nat) : w.toArray[i]! = w.get i := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => rfl
  -- Both read zero past the end.
  | _ + 16 =>
    simp only [toArray, get]
    rfl

/-- Writing the array writes the record. -/
theorem set!_toArray (w : Work) (i : Nat) (x : UInt32) :
    w.toArray.set! i x = (w.set i x).toArray := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => rfl
  -- Both leave the words unchanged past the end.
  | _ + 16 => simp [toArray, set, Array.set!, Array.setIfInBounds]

/-- An array of 16 words is the record of its reads. -/
theorem toArray_ofArray (a : Array UInt32) (h : a.size = 16) : (ofArray a).toArray = a := by
  apply Array.ext (by simp [h, toArray])
  intro i _ hi
  rw [h] at hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
    simp [getElem!_pos, h, ofArray, toArray]
  | _ + 16, hi => omega

/-! ## Mixing -/

/-- The mixing function G of RFC 7693 Section 3.1, on words named by index. -/
def mix (w : Work) (a b c d : Nat) (x y : UInt32) : Work :=
  let w := w.set a (w.get a + w.get b + x)
  let w := w.set d (rotateRight (w.get d ^^^ w.get a) 16)
  let w := w.set c (w.get c + w.get d)
  let w := w.set b (rotateRight (w.get b ^^^ w.get c) 12)
  let w := w.set a (w.get a + w.get b + y)
  let w := w.set d (rotateRight (w.get d ^^^ w.get a) 8)
  let w := w.set c (w.get c + w.get d)
  w.set b (rotateRight (w.get b ^^^ w.get c) 7)

end Work

/-- Mixing the array mixes the record, for any four indices. -/
theorem mix_toArray (w : Work) (a b c d : Nat) (x y : UInt32) :
    mix w.toArray a b c d x y = (w.mix a b c d x y).toArray := by
  simp only [mix, Work.getElem!_toArray, Work.set!_toArray, Work.mix]
  rfl

/-- The mixing function G of RFC 7693 Section 3.1, on four words. -/
def g (a b c d x y : UInt32) : UInt32 × UInt32 × UInt32 × UInt32 :=
  let a := a + b + x
  let d := rotateRight (d ^^^ a) 16
  let c := c + d
  let b := rotateRight (b ^^^ c) 12
  let a := a + b + y
  let d := rotateRight (d ^^^ a) 8
  let c := c + d
  let b := rotateRight (b ^^^ c) 7
  (a, b, c, d)

/-- One round of RFC 7693 Section 3.2, with each mix on named fields.

The kernel evaluates named fields directly, without an index lookup.

The schedule is the round's row of the message permutation.
-/
def round (m : Work) (schedule : Array Nat) (w : Work) : Work :=
  let x (k : Nat) : UInt32 := m.get schedule[k]!
  -- Four column mixes.
  let (v0, v4, v8, v12) := g w.v0 w.v4 w.v8 w.v12 (x 0) (x 1)
  let (v1, v5, v9, v13) := g w.v1 w.v5 w.v9 w.v13 (x 2) (x 3)
  let (v2, v6, v10, v14) := g w.v2 w.v6 w.v10 w.v14 (x 4) (x 5)
  let (v3, v7, v11, v15) := g w.v3 w.v7 w.v11 w.v15 (x 6) (x 7)
  -- Four diagonal mixes.
  let (v0, v5, v10, v15) := g v0 v5 v10 v15 (x 8) (x 9)
  let (v1, v6, v11, v12) := g v1 v6 v11 v12 (x 10) (x 11)
  let (v2, v7, v8, v13) := g v2 v7 v8 v13 (x 12) (x 13)
  let (v3, v4, v9, v14) := g v3 v4 v9 v14 (x 14) (x 15)
  ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15⟩

/-- The round on named fields is the eight mixes on indexed words. -/
theorem round_eq (m : Work) (schedule : Array Nat) (w : Work) :
    round m schedule w =
      let x (k : Nat) : UInt32 := m.get schedule[k]!
      let w := w.mix 0 4 8 12 (x 0) (x 1)
      let w := w.mix 1 5 9 13 (x 2) (x 3)
      let w := w.mix 2 6 10 14 (x 4) (x 5)
      let w := w.mix 3 7 11 15 (x 6) (x 7)
      let w := w.mix 0 5 10 15 (x 8) (x 9)
      let w := w.mix 1 6 11 12 (x 10) (x 11)
      let w := w.mix 2 7 8 13 (x 12) (x 13)
      w.mix 3 4 9 14 (x 14) (x 15) := by
  simp only [round, g, Work.mix, Work.get, Work.set]

/-! ## Compression -/

/-- The compression function F of RFC 7693 Section 3.2, on the record. -/
def compressFast (chaining : Array UInt32) (m : Work) (counter : UInt64) (last : Bool) :
    Array UInt32 :=
  -- The chaining value, then the IV with the counter and the final flag folded in.
  let w : Work := ⟨chaining[0]!, chaining[1]!, chaining[2]!, chaining[3]!,
    chaining[4]!, chaining[5]!, chaining[6]!, chaining[7]!,
    IV[0]!, IV[1]!, IV[2]!, IV[3]!,
    IV[4]! ^^^ Internal.counterLow counter, IV[5]! ^^^ Internal.counterHigh counter,
    if last then ~~~IV[6]! else IV[6]!, IV[7]!⟩
  let w := (List.range' 0 10).foldl (fun w r => round m Internal.sigma[r]! w) w
  Array.ofFn fun i : Fin 8 => chaining[i.val]! ^^^ w.get i.val ^^^ w.get (i.val + 8)

/-- An array of eight words is the literal of its reads. -/
private theorem eq_lit8 (a : Array UInt32) (h : a.size = 8) :
    a = #[a[0]!, a[1]!, a[2]!, a[3]!, a[4]!, a[5]!, a[6]!, a[7]!] := by
  apply Array.ext (by simp [h])
  intro i hi _
  rw [h] at hi
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => simp [getElem!_pos, h]

/-- A loop whose body keeps the words in record form is a fold over the record. -/
private theorem forIn_range_toArray (n : Nat)
    (body : Nat → Array UInt32 → Id (ForInStep (Array UInt32)))
    (f : Nat → Work → Work) (h : ∀ r w, body r w.toArray = .yield (f r w).toArray) (w : Work) :
    forIn (m := Id) [:n] w.toArray body =
      ((List.range' 0 n).foldl (fun w r => f r w) w).toArray := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  induction List.range' 0 n generalizing w with
  | nil => rfl
  | cons r l ih =>
    rw [List.forIn_cons, h]
    exact ih _

/-- The compression on the record equals the specification's, for every input. -/
theorem compress_eq_compressFast (chaining message : Array UInt32) (counter : UInt64)
    (last : Bool) (hc : chaining.size = 8) (hm : message.size = 16) :
    compress chaining message counter last =
      compressFast chaining (Work.ofArray message) counter last := by
  conv_lhs => rw [eq_lit8 chaining hc, ← Work.toArray_ofArray message hm]
  unfold compress compressFast
  -- The chaining value and the IV fill the 16 words.
  have hw : #[chaining[0]!, chaining[1]!, chaining[2]!, chaining[3]!,
      chaining[4]!, chaining[5]!, chaining[6]!, chaining[7]!] ++ IV =
      (⟨chaining[0]!, chaining[1]!, chaining[2]!, chaining[3]!,
        chaining[4]!, chaining[5]!, chaining[6]!, chaining[7]!,
        IV[0]!, IV[1]!, IV[2]!, IV[3]!, IV[4]!, IV[5]!, IV[6]!, IV[7]!⟩ : Work).toArray := rfl
  -- The counter and the final flag write the record.
  cases last <;>
    simp only [hw, Work.getElem!_toArray, Work.set!_toArray, Id.run, pure_bind, ite_true,
      ite_false, Bool.false_eq_true]
  -- Each pass of the loop is one round on the record.
  all_goals
    rw [forIn_range_toArray 10 _ (fun r w => round (Work.ofArray message) Internal.sigma[r]! w)
      fun r w => by simp only [round_eq, mix_toArray]; rfl]
  -- The feed-forward reads the same words on both sides.
  all_goals
    rw [← eq_lit8 chaining hc]
    show Array.ofFn _ = _
    simp only [Work.getElem!_toArray]
    rfl

/-! ## Reading a block -/

/-- Read four bytes of a list as one little-endian word, reading zero past the end. -/
def le32 (bytes : List UInt8) : UInt32 :=
  (bytes.getD 0 0).toUInt32
  ||| ((bytes.getD 1 0).toUInt32 <<< 8)
  ||| ((bytes.getD 2 0).toUInt32 <<< 16)
  ||| ((bytes.getD 3 0).toUInt32 <<< 24)

/-- The 16 message words at the start of a list of bytes.

The kernel walks the list once to drop the block offset, not once per byte.
-/
def Work.ofBytes (bytes : List UInt8) : Work :=
  ⟨le32 bytes, le32 (bytes.drop 4), le32 (bytes.drop 8), le32 (bytes.drop 12),
   le32 (bytes.drop 16), le32 (bytes.drop 20), le32 (bytes.drop 24), le32 (bytes.drop 28),
   le32 (bytes.drop 32), le32 (bytes.drop 36), le32 (bytes.drop 40), le32 (bytes.drop 44),
   le32 (bytes.drop 48), le32 (bytes.drop 52), le32 (bytes.drop 56), le32 (bytes.drop 60)⟩

/-- Reading a block from the dropped list reads the same words as the specification. -/
theorem ofArray_blockWords (input : ByteArray) (offset : Nat) :
    Work.ofArray (blockWords input offset) = Work.ofBytes (input.data.toList.drop offset) := by
  simp only [Work.ofArray, Work.ofBytes, blockWords, le32, Internal.little32]
  simp [getElem!_pos, List.getD_eq_getElem?_getD, List.getElem?_drop, Nat.add_assoc]

/-! ## The hash -/

/-- One compression on the record: the chaining value after block `block` of `input`. -/
def blockStepFast (input : ByteArray) (chaining : Array UInt32) (block : Nat) : Array UInt32 :=
  compressFast chaining (Work.ofBytes (input.data.toList.drop (Internal.blockOffset block)))
    (UInt64.ofNat (Internal.blockCounter input.size block))
    (block + 1 == Internal.blockCount input.size)

/-- BLAKE2s-256 computed with the compression on the record. -/
def hashFast (input : ByteArray) : Vector UInt8 32 :=
  finalBytes
    ((List.range' 0 (Internal.blockCount input.size)).foldl (blockStepFast input) initialState)

/-- Both compressions agree on every chaining value of eight words. -/
theorem blockStep_eq_blockStepFast (input : ByteArray) (chaining : Array UInt32) (block : Nat)
    (h : chaining.size = 8) :
    blockStep input chaining block = blockStepFast input chaining block := by
  rw [blockStep, compress_eq_compressFast _ _ _ _ h (by simp [blockWords]), ofArray_blockWords]
  rfl

/-- The fast form computes the same digest as the specification, for every input. -/
theorem hash_eq_hashFast (input : ByteArray) : hash input = hashFast input := by
  rw [hash_eq_foldl, hashFast]
  congr 1
  -- Every chaining value in the fold has eight words, so each step agrees.
  have hfold (l : List Nat) (s : Array UInt32) (h : s.size = 8) :
      l.foldl (blockStep input) s = l.foldl (blockStepFast input) s := by
    induction l generalizing s with
    | nil => rfl
    | cons b l ih =>
      rw [List.foldl_cons, List.foldl_cons, blockStep_eq_blockStepFast _ _ _ h]
      exact ih _ (by simp [blockStepFast, compressFast])
  exact hfold _ _ rfl

/-! ## A long known answer

The 1024-byte input of RFC 7693 Appendix E runs 16 compressions.

On the specification's arrays that costs the kernel about 14 GB, on the record a few. -/

set_option maxRecDepth 200000 in
/-- The 1024-byte Appendix E input matches an independent BLAKE2s-256 digest. -/
theorem hash_selfTest_1024 : (hash (selfTestInput 1024 1024)).toArray = #[
    0xc7, 0x95, 0xe9, 0xac, 0x66, 0xad, 0x49, 0x54,
    0x0e, 0x9c, 0xe4, 0x3e, 0xfc, 0xc6, 0xda, 0x14,
    0x2c, 0x61, 0xc1, 0xe6, 0x05, 0x1f, 0x06, 0x08,
    0xbb, 0x10, 0x9c, 0x14, 0xd2, 0x4e, 0x4e, 0xbb
  ] := by
  -- Sixteen full blocks, the final flag on block 16, evaluated on the record.
  rw [hash_eq_hashFast]
  decide +kernel

end EthLib.Cryptography.Hash.Blake2s
