module

public import EthLib.Networking.Rlpx.Frame
public import EthLib.Networking.Proofs.Rlpx.Handshake
public import EthLib.Cryptography.Proofs.Hash.KeccakHasher

/-!
# Proofs: RLPx frames

A reader in step with the writer reads back each frame, and ends in the writer's new state.

After an honest handshake, each side's sending direction is the other side's receiving direction.

A frame changed outside its MACs is rejected, or a search names a collision of its MAC.

That collision is two Keccak-256 inputs whose digests agree on their first 16 bytes.
-/

@[expose] public section

namespace EthLib.Networking.Rlpx

open EthLib.Cryptography
open EthLib.Cryptography.Hash.Keccak
open EthLib.Cryptography.Secp256k1.Point

/-- The bytes of a byte array, as a list, give back the byte array. -/
private theorem ByteArray.mk_toArray_toList (b : ByteArray) :
    (⟨b.data.toList.toArray⟩ : ByteArray) = b := by
  simp

theorem size_crypt (aesKey : Aes.Key .aes256) (counter : Aes.Block) (data : ByteArray) :
    (crypt aesKey counter data).size = data.size :=
  Aes.size_ctr _ _ _ _

theorem crypt_crypt (aesKey : Aes.Key .aes256) (counter : Aes.Block) (data : ByteArray) :
    crypt aesKey counter (crypt aesKey counter data) = data :=
  Aes.ctr_ctr _ _ _ _

theorem size_header (size : Nat) : (header size).size = BLOCK_SIZE := by
  simp [header, HEADER_DATA, ByteArray.size, BLOCK_SIZE]

theorem readSize_header {size : Nat} (h : size < 2 ^ 24) :
    readSize (header size).data.toList = size := by
  simp [readSize, header, HEADER_DATA]
  omega

theorem size_macBytes (h : Hasher) : (macBytes h).size = BLOCK_SIZE := by
  simp [macBytes, ByteArray.size, BLOCK_SIZE]

theorem le_paddedSize (size : Nat) : size ≤ paddedSize size := by
  unfold paddedSize; omega

/-- The five parts of a frame and the bytes after it, cut at their sizes. -/
theorem split_frame {α : Type} (a b c d e : List α) (ha : a.length = BLOCK_SIZE)
    (hb : b.length = BLOCK_SIZE) (hd : d.length = BLOCK_SIZE) :
    (a ++ b ++ c ++ d ++ e).take BLOCK_SIZE = a ∧
      ((a ++ b ++ c ++ d ++ e).drop BLOCK_SIZE).take BLOCK_SIZE = b ∧
      ((a ++ b ++ c ++ d ++ e).drop (2 * BLOCK_SIZE)).take c.length = c ∧
      ((a ++ b ++ c ++ d ++ e).drop (2 * BLOCK_SIZE + c.length)).take BLOCK_SIZE = d ∧
      (a ++ b ++ c ++ d ++ e).drop (2 * BLOCK_SIZE + c.length + BLOCK_SIZE) = e ∧
      (a ++ b ++ c ++ d ++ e).length = 2 * BLOCK_SIZE + c.length + BLOCK_SIZE + e.length := by
  simp only [BLOCK_SIZE] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ha]
  · simp [ha, hb]
  · rw [show a ++ b ++ c ++ d ++ e = (a ++ b) ++ (c ++ (d ++ e)) by simp,
      List.drop_left' (by simp [ha, hb]), List.take_left' rfl]
  · rw [show a ++ b ++ c ++ d ++ e = (a ++ b ++ c) ++ (d ++ e) by simp,
      List.drop_left' (by simp [ha, hb]; omega), List.take_left' hd]
  · rw [List.drop_left' (by simp [ha, hb, hd]; omega)]
  · simp [ha, hb, hd]; omega

/--
A reader in step with the writer reads back the frame data, and moves to the writer's new state.

Any bytes after the frame come back untouched.
-/
theorem readFrame_writeFrame {st st' : FrameState} {frameData frame : ByteArray}
    (h : writeFrame st frameData = .ok (frame, st')) (rest : ByteArray) :
    readFrame st (frame ++ rest) = .ok (frameData, st', rest) := by
  unfold writeFrame at h
  by_cases hsize : 16777216 ≤ frameData.size
  · simp [hsize] at h
  simp only [hsize, ite_false, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hpad : (frameData ++ ⟨Array.replicate (paddedSize frameData.size - frameData.size) 0⟩).size =
      paddedSize frameData.size := by
    have := le_paddedSize frameData.size
    have hz (k : Nat) : (⟨Array.replicate k 0⟩ : ByteArray).size = k := by simp [ByteArray.size]
    rw [ByteArray.size_append, hz]
    omega
  set P := frameData ++ ⟨Array.replicate (paddedSize frameData.size - frameData.size) 0⟩ with hP
  set H := crypt st.aesKey st.counter (header frameData.size) with hH
  set h1 := macStep st.macKey st.mac H.data.toList with hh1
  set F := crypt st.aesKey (advance 1 st.counter) P with hF
  set h2 := frameMacStep st.macKey h1 F with hh2
  have hHs : H.data.toList.length = BLOCK_SIZE := by
    rw [Array.length_toList]; exact (size_crypt _ _ _).trans (size_header frameData.size)
  have hFs : F.data.toList.length = paddedSize frameData.size := by
    rw [Array.length_toList]; exact (size_crypt _ _ _).trans hpad
  have hM (h : Hasher) : (macBytes h).data.toList.length = BLOCK_SIZE := by
    rw [Array.length_toList]; exact size_macBytes h
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := split_frame H.data.toList (macBytes h1).data.toList
    F.data.toList (macBytes h2).data.toList rest.data.toList hHs (hM h1) (hM h2)
  have hheader : readSize (crypt st.aesKey st.counter ⟨H.data.toList.toArray⟩).data.toList =
      frameData.size := by
    rw [ByteArray.mk_toArray_toList, hH, crypt_crypt, readSize_header (by omega)]
  unfold readFrame
  simp only [ByteArray.data_append, Array.toList_append]
  simp only [s1, s2, s6]
  rw [hheader, ← hFs]
  simp only [s3, s4, s5, ByteArray.mk_toArray_toList]
  have c1 : ¬ (2 * BLOCK_SIZE + F.data.toList.length + BLOCK_SIZE + rest.data.toList.length <
      2 * BLOCK_SIZE) := by omega
  have c2 : ¬ ((macBytes h1).data.toList ≠
      (macDigest (macStep st.macKey st.mac H.data.toList)).toList) := fun h => h rfl
  have c3 : ¬ (2 * BLOCK_SIZE + F.data.toList.length + BLOCK_SIZE + rest.data.toList.length <
      2 * BLOCK_SIZE + F.data.toList.length + BLOCK_SIZE) := by omega
  have c4 : ¬ ((macBytes h2).data.toList ≠
      (macDigest (frameMacStep st.macKey (macStep st.macKey st.mac H.data.toList) F)).toList) :=
    fun h => h rfl
  simp only [c1, c2, c3, c4, ite_false]
  -- The frame data is the first bytes of the padded data.
  rw [hF, crypt_crypt, hP]
  simp only [ByteArray.data_append, Array.toList_append, Except.ok.injEq, Prod.mk.injEq]
  refine ⟨?_, ?_, trivial⟩
  · simp
  · rfl

/-! ## A changed frame -/

/-- A frame that the reader accepts has both MACs right, and the input is long enough. -/
theorem readFrame_eq_ok {st : FrameState} {input : ByteArray}
    {out : ByteArray × FrameState × ByteArray} (h : readFrame st input = .ok out) :
    let b := input.data.toList
    let h1 := macStep st.macKey st.mac (b.take BLOCK_SIZE)
    let header := crypt st.aesKey st.counter ⟨(b.take BLOCK_SIZE).toArray⟩
    let n := paddedSize (readSize header.data.toList)
    let frameCt : ByteArray := ⟨((b.drop (2 * BLOCK_SIZE)).take n).toArray⟩
    (b.drop BLOCK_SIZE).take BLOCK_SIZE = (macDigest h1).toList ∧
      2 * BLOCK_SIZE + n + BLOCK_SIZE ≤ b.length ∧
      (b.drop (2 * BLOCK_SIZE + n)).take BLOCK_SIZE =
        (macDigest (frameMacStep st.macKey h1 frameCt)).toList := by
  unfold readFrame at h
  dsimp only at h
  intro b h1 header n frameCt
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i hm
  split at h
  · simp at h
  rename_i hlen
  split at h
  · simp at h
  rename_i hm2
  exact ⟨not_not.mp hm, Nat.le_of_not_lt hlen, not_not.mp hm2⟩

/-- An honest frame: a header ciphertext, its MAC, a frame ciphertext and its MAC. -/
theorem writeFrame_eq_ok {st st' : FrameState} {frameData frame : ByteArray}
    (h : writeFrame st frameData = .ok (frame, st')) :
    ∃ H F : ByteArray, H.data.toList.length = BLOCK_SIZE ∧
      F.data.toList.length = paddedSize frameData.size ∧
      readSize (crypt st.aesKey st.counter H).data.toList = frameData.size ∧
      frame = H ++ macBytes (macStep st.macKey st.mac H.data.toList) ++ F ++
        macBytes (frameMacStep st.macKey (macStep st.macKey st.mac H.data.toList) F) := by
  unfold writeFrame at h
  by_cases hsize : 16777216 ≤ frameData.size
  · simp [hsize] at h
  simp only [hsize, ite_false, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  have hz (k : Nat) : (⟨Array.replicate k 0⟩ : ByteArray).size = k := by simp [ByteArray.size]
  refine ⟨_, _, ?_, ?_, ?_, rfl⟩
  · rw [Array.length_toList]; exact (size_crypt _ _ _).trans (size_header _)
  · rw [Array.length_toList]
    refine (size_crypt _ _ _).trans ?_
    have := le_paddedSize frameData.size
    rw [ByteArray.size_append, hz]
    omega
  · rw [crypt_crypt, readSize_header (by omega)]

/-- The first 16 bytes of a Keccak-256 digest: the part an RLPx MAC keeps. -/
def macOf (input : ByteArray) : List UInt8 := (keccak256 input).toList.take BLOCK_SIZE

/-- Two different inputs whose Keccak-256 digests agree on their first 16 bytes. -/
def IsMacCollision (pair : ByteArray × ByteArray) : Prop :=
  pair.1 ≠ pair.2 ∧ macOf pair.1 = macOf pair.2

/--
The bytes that the header MAC of the frame `f` hashes, after the bytes `t`.

The MAC state after `t` absorbs the seed of the header ciphertext.
-/
def headerMacInput (macKey : Aes.Key .aes256) (t : ByteArray) (f : List UInt8) : ByteArray :=
  t ++ macSeed macKey (Hasher.empty.absorb t) (f.take BLOCK_SIZE)

/-- The bytes that the frame MAC of the frame `f` hashes, for a frame ciphertext of `n` bytes. -/
def frameMacInput (macKey : Aes.Key .aes256) (t : ByteArray) (n : Nat) (f : List UInt8) :
    ByteArray :=
  let u := headerMacInput macKey t f ++ ⟨((f.drop (2 * BLOCK_SIZE)).take n).toArray⟩
  u ++ macSeed macKey (Hasher.empty.absorb u) (macDigest (Hasher.empty.absorb u)).toList

/--
The MAC collision behind the frame `f'`, offered in place of the frame `f`.

It compares the inputs of the two header MACs, then the inputs of the two frame MACs.
-/
def findMacCollision (macKey : Aes.Key .aes256) (t f f' : ByteArray) :
    Option (ByteArray × ByteArray) :=
  let x1 := headerMacInput macKey t f.data.toList
  let y1 := headerMacInput macKey t f'.data.toList
  if x1 ≠ y1 ∧ macOf x1 = macOf y1 then some (x1, y1)
  else
    let n := f.size - 3 * BLOCK_SIZE
    let x2 := frameMacInput macKey t n f.data.toList
    let y2 := frameMacInput macKey t n f'.data.toList
    if x2 ≠ y2 ∧ macOf x2 = macOf y2 then some (x2, y2) else none

/-- Every pair that the search returns is a MAC collision. -/
theorem findMacCollision_valid {macKey : Aes.Key .aes256} {t f f' : ByteArray}
    {pair : ByteArray × ByteArray} (h : findMacCollision macKey t f f' = some pair) :
    IsMacCollision pair := by
  unfold findMacCollision at h
  dsimp only at h
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  · cases h

/-- A frame compared with itself has no collision, so the search can fail. -/
theorem findMacCollision_self (macKey : Aes.Key .aes256) (t f : ByteArray) :
    findMacCollision macKey t f f = none := by
  simp [findMacCollision]

/-- The MAC of the state after `u` is the first 16 bytes of `keccak256 u`. -/
theorem macDigest_absorb (u : ByteArray) :
    (macDigest (Hasher.empty.absorb u)).toList = macOf u := by
  rw [macOf, ← digest_absorb_empty]
  apply List.ext_getElem
  · simp only [Vector.length_toList, List.length_take, BLOCK_SIZE]
    rfl
  · intro i h1 h2
    simp [macDigest]

/-- A MAC step from the state after `t` gives the state after `t`, then the seed. -/
theorem macStep_absorb (macKey : Aes.Key .aes256) (t : ByteArray) (f : List UInt8) :
    macStep macKey (Hasher.empty.absorb t) (f.take BLOCK_SIZE) =
      Hasher.empty.absorb (headerMacInput macKey t f) := by
  rw [macStep, absorb_absorb, headerMacInput]

/-- The frame MAC step after the header MAC step absorbs the frame MAC input. -/
theorem frameMacStep_absorb (macKey : Aes.Key .aes256) (t : ByteArray) (n : Nat)
    (f : List UInt8) :
    frameMacStep macKey (Hasher.empty.absorb (headerMacInput macKey t f))
        ⟨((f.drop (2 * BLOCK_SIZE)).take n).toArray⟩ =
      Hasher.empty.absorb (frameMacInput macKey t n f) := by
  simp only [frameMacStep, macStep, absorb_absorb, frameMacInput]

/-- XOR with one key stream is injective on values of its length. -/
theorem zipWith_xor_inj {k v w : List UInt8} (hv : v.length = k.length)
    (hw : w.length = k.length) (h : List.zipWith (· ^^^ ·) k v = List.zipWith (· ^^^ ·) k w) :
    v = w := by
  induction k generalizing v w with
  | nil => simp_all
  | cons a k ih =>
    cases v with
    | nil => simp at hv
    | cons x v =>
      cases w with
      | nil => simp at hw
      | cons y w =>
        simp only [List.zipWith_cons_cons, List.cons.injEq] at h
        have hxy : x = y := by
          have := congrArg (a ^^^ ·) h.1
          simpa [← UInt8.xor_assoc] using this
        rw [hxy, ih (by simpa using hv) (by simpa using hw) h.2]

/-- A list is its four parts of a frame put back together, for any size `n` of the third part. -/
theorem eq_frame_parts {α : Type} (l : List α) (n : Nat) :
    l = l.take BLOCK_SIZE ++ (l.drop BLOCK_SIZE).take BLOCK_SIZE ++
      (l.drop (2 * BLOCK_SIZE)).take n ++ l.drop (2 * BLOCK_SIZE + n) := by
  simp only [BLOCK_SIZE]
  conv => lhs; rw [← List.take_append_drop 16 l]
  conv => lhs; rhs; rw [← List.take_append_drop 16 (l.drop 16)]
  conv => lhs; rhs; rhs; rw [← List.take_append_drop n ((l.drop 16).drop 16)]
  simp [List.drop_drop, List.append_assoc]

/--
A frame that differs from an honest frame outside its MACs is rejected, or the search finds it.

The search names a collision of the first 16 bytes of Keccak-256.

The MAC state of the direction is the state after the bytes `t`.

The changed frame keeps the length and the two MACs of the honest frame.
-/
theorem readFrame_changed {st st' : FrameState} {frameData f : ByteArray}
    (hw : writeFrame st frameData = .ok (f, st')) {t : ByteArray}
    (ht : st.mac = Hasher.empty.absorb t) {f' rest : ByteArray}
    {out : ByteArray × FrameState × ByteArray} (hsize : f'.size = f.size)
    (hmac1 : (f'.data.toList.drop BLOCK_SIZE).take BLOCK_SIZE =
      (f.data.toList.drop BLOCK_SIZE).take BLOCK_SIZE)
    (hmac2 : f'.data.toList.drop (f.size - BLOCK_SIZE) = f.data.toList.drop (f.size - BLOCK_SIZE))
    (hread : readFrame st (f' ++ rest) = .ok out) :
    f' = f ∨ ∃ pair, findMacCollision st.macKey t f f' = some pair ∧ IsMacCollision pair := by
  obtain ⟨H, F, hH, hF, hsz, rfl⟩ := writeFrame_eq_ok hw
  set h1 := macStep st.macKey st.mac H.data.toList with hh1
  set h2 := frameMacStep st.macKey h1 F with hh2
  set n := paddedSize frameData.size with hn
  -- The honest frame, as a list of bytes in four parts.
  set l := (H ++ macBytes h1 ++ F ++ macBytes h2).data.toList with hl
  have hlist : l = H.data.toList ++ (macDigest h1).toList ++ F.data.toList ++
      (macDigest h2).toList := by
    simp [hl, macBytes, ByteArray.data_append, Vector.toList]
  have hM (h : Hasher) : (macDigest h).toList.length = BLOCK_SIZE := by simp [BLOCK_SIZE]
  have hlen : l.length = 3 * BLOCK_SIZE + n := by
    rw [hlist]; simp only [List.length_append, hH, hF, hM]; omega
  have hfsize : (H ++ macBytes h1 ++ F ++ macBytes h2).size = 3 * BLOCK_SIZE + n := by
    rw [← hlen, hl, Array.length_toList]; rfl
  obtain ⟨p1, p2, p3, p4, -, -⟩ := split_frame H.data.toList (macDigest h1).toList F.data.toList
    (macDigest h2).toList [] hH (hM h1) (hM h2)
  simp only [List.append_nil, ← hlist, hF] at p1 p2 p3 p4
  -- The changed frame, as a list of bytes of the same length.
  set g := f'.data.toList with hg
  have hglen : g.length = 3 * BLOCK_SIZE + n := by
    rw [hg, Array.length_toList]; exact hsize.trans hfsize
  -- The reader sees the changed frame, then the bytes after it.
  obtain ⟨hA, -, hC⟩ := readFrame_eq_ok hread
  simp only [ByteArray.data_append, Array.toList_append, ← hg] at hA hC
  have ht1 : (g ++ rest.data.toList).take BLOCK_SIZE = g.take BLOCK_SIZE :=
    List.take_append_of_le_length (by rw [hglen]; omega)
  have ht2 : ((g ++ rest.data.toList).drop BLOCK_SIZE).take BLOCK_SIZE =
      (g.drop BLOCK_SIZE).take BLOCK_SIZE := by
    rw [List.drop_append_of_le_length (by rw [hglen]; omega),
      List.take_append_of_le_length (by simp [hglen]; omega)]
  rw [ht1, ht2, hmac1, p2, ht, macStep_absorb, macDigest_absorb] at hA
  -- The honest header MAC is the MAC of the honest header MAC input.
  have hx1 : (macDigest h1).toList = macOf (headerMacInput st.macKey t l) := by
    rw [hh1, ← p1, ht, macStep_absorb, macDigest_absorb]
  rw [hx1] at hA
  by_cases hx : headerMacInput st.macKey t l = headerMacInput st.macKey t g
  swap
  · -- Two different header MAC inputs with one MAC.
    have hfind : findMacCollision st.macKey t (H ++ macBytes h1 ++ F ++ macBytes h2) f' =
        some (headerMacInput st.macKey t l, headerMacInput st.macKey t g) := by
      simp only [findMacCollision, ← hl, ← hg]
      simp [hx, hA]
    exact Or.inr ⟨_, hfind, findMacCollision_valid hfind⟩
  -- One header MAC input: the header ciphertexts are equal.
  have hhead : g.take BLOCK_SIZE = H.data.toList := by
    rw [← p1]
    have hs := congrArg (fun b : ByteArray => b.data.toList) hx
    simp only [headerMacInput, ByteArray.data_append, Array.toList_append,
      List.append_cancel_left_eq, macSeed] at hs
    refine (zipWith_xor_inj ?_ ?_ hs).symm <;> simp [BLOCK_SIZE, hglen, hlen] <;> omega
  -- So the reader reads the honest frame size, and a frame ciphertext of `n` bytes.
  have hsize' : readSize (crypt st.aesKey st.counter ⟨(g.take BLOCK_SIZE).toArray⟩).data.toList =
      frameData.size := by
    rw [hhead, ByteArray.mk_toArray_toList, hsz]
  rw [ht1, hsize', ← hn, ht, macStep_absorb,
    List.drop_append_of_le_length (by rw [hglen]; omega),
    List.drop_append_of_le_length (by rw [hglen]; omega),
    List.take_append_of_le_length (by simp [hglen]; omega),
    List.take_append_of_le_length (by simp [hglen]; omega),
    frameMacStep_absorb, macDigest_absorb] at hC
  have hgm2 : g.drop (2 * BLOCK_SIZE + n) = (macDigest h2).toList := by
    have hl2 : l.drop (2 * BLOCK_SIZE + n) = (macDigest h2).toList := by
      rw [← p4, List.take_of_length_le (by simp [hlen]; omega)]
    rw [← hl2]
    rw [hfsize, show 3 * BLOCK_SIZE + n - BLOCK_SIZE = 2 * BLOCK_SIZE + n by
      simp [BLOCK_SIZE]; omega] at hmac2
    exact hmac2
  rw [List.take_of_length_le (by simp [hglen]; omega), hgm2] at hC
  -- The honest frame MAC is the MAC of the honest frame MAC input.
  have hx2 : (macDigest h2).toList = macOf (frameMacInput st.macKey t n l) := by
    have hFl : F = ⟨((l.drop (2 * BLOCK_SIZE)).take n).toArray⟩ := by
      rw [p3, ByteArray.mk_toArray_toList]
    rw [hh2, hFl, hh1, ← p1, ht, macStep_absorb, frameMacStep_absorb, macDigest_absorb]
  rw [hx2] at hC
  have hn' : (H ++ macBytes h1 ++ F ++ macBytes h2).size - 3 * BLOCK_SIZE = n := by
    rw [hfsize]; omega
  by_cases hy : frameMacInput st.macKey t n l = frameMacInput st.macKey t n g
  swap
  · -- Two different frame MAC inputs with one MAC.
    have hfind : findMacCollision st.macKey t (H ++ macBytes h1 ++ F ++ macBytes h2) f' =
        some (frameMacInput st.macKey t n l, frameMacInput st.macKey t n g) := by
      simp only [findMacCollision, ← hl, ← hg, hn']
      simp [hx, hy, hC]
    exact Or.inr ⟨_, hfind, findMacCollision_valid hfind⟩
  -- One frame MAC input: the frame ciphertexts are equal, so the frames are equal.
  left
  have hbody : (g.drop (2 * BLOCK_SIZE)).take n = (l.drop (2 * BLOCK_SIZE)).take n := by
    have hs := congrArg (fun b : ByteArray => b.data.toList) hy
    simp only [frameMacInput, ByteArray.data_append, Array.toList_append] at hs
    have hseed (u : ByteArray) (v : List UInt8) :
        (macSeed st.macKey (Hasher.empty.absorb u) v).data.toList.length = min 16 v.length := by
      simp [macSeed]
    obtain ⟨hu, -⟩ := List.append_inj' hs (by simp only [hseed, Vector.length_toList])
    rw [hx] at hu
    simpa using hu.symm
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [← hg, ← hl, eq_frame_parts g n, eq_frame_parts l n, hhead, p1, hmac1, hbody,
    hgm2, ← p4, List.take_of_length_le (l := List.drop (2 * BLOCK_SIZE + n) l)
      (by simp [hlen]; omega)]

/-- Two errors with one code come from one constructor. -/
theorem FrameError.code_injective (e₁ e₂ : FrameError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [FrameError.code] at h; exact absurd h (by decide))

/-! ## The two sides of a session -/

/--
After an honest handshake, the initiator's sending state is the recipient's receiving state.

The initiator's receiving state is the recipient's sending state.
-/
theorem egress_ingress_of_respond {initiator recipient : Keys} {sealingI sealingR : Sealing}
    {auth ack : ByteArray} {secrets : Secrets}
    (hauth : makeAuth initiator (mul recipient.staticKey generator) sealingI = .ok auth)
    (hresp : respond recipient sealingR auth = .ok (ack, secrets)) :
    ∃ mine, finish initiator auth ack = .ok mine ∧ mine.egress = secrets.ingress ∧
      mine.ingress = secrets.egress :=
  ⟨_, finish_respond hauth hresp, rfl, rfl⟩

end EthLib.Networking.Rlpx
