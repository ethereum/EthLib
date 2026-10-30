module

public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.Fp2
public import EthLib.Cryptography.Proofs.Bls.Compress
public import EthLib.Cryptography.Proofs.Bls.G2Equiv
public import EthLib.Cryptography.Proofs.IdLoops
-- The closed infinity check reduces the derived `Except` equality and the range loop.
import all Batteries.Data.Except
import all Init.Data.Range.Basic

/-!
# Proofs: 96-byte `G2` compressed serialization

`G2` holds points on the twist `E' : y^2 = x^3 + 4*(1 + i)` over `Fp2`.

The format is `draft-irtf-cfrg-pairing-friendly-curves-07` Appendix C.

Section C.1 encodes a point, and Section C.2 decodes it.

- Encoding then decoding gives back the same projective point.
- Every decoded point lies on the twist.
- Bad lengths, bad flags, bad infinity encodings and field elements `>= p` are rejected.
- Decoding then encoding gives back the exact 96 input bytes.
- So two different byte strings never decode to the same point.

The last two facts need `y != 0` on the twist.

That holds because `x^3 + 4*(1 + i)` has no root in `Fp2`.
-/

@[expose] public section

deriving instance DecidableEq for EthLib.Cryptography.Bls.G2

namespace EthLib.Cryptography.Bls

namespace Fp2

/-- Boolean equality on `Fp2` is symmetric. -/
theorem beq_symm (a b : Fp2) : (a == b) = (b == a) := by
  rw [Bool.eq_iff_iff, _root_.beq_iff_eq, _root_.beq_iff_eq, eq_comm]

end Fp2

namespace G2

open scoped EthLib.Cryptography.Bls.Fp

/-! ## Projective equality -/

/-- Projective equality on `G2` is reflexive. -/
@[simp] theorem projectiveEq_refl (p : G2) : projectiveEq p p = true := by
  unfold projectiveEq
  by_cases hz : p.z.isZero = true <;> simp [hz]

/-- Projective equality on `G2` is symmetric. -/
theorem projectiveEq_symm (p q : G2) : projectiveEq p q = projectiveEq q p := by
  unfold projectiveEq
  by_cases hp : p.z.isZero = true <;> by_cases hq : q.z.isZero = true
  · simp [hp, hq]
  · simp [hp, hq]
  · simp [hp, hq]
  · rw [ite_eq_right hp, ite_eq_right hq, ite_eq_right hq, ite_eq_right hp]
    -- Both finite: swap the two cross-multiplication tests.
    rw [Fp2.beq_symm (p.x * (q.z * q.z)) (q.x * (p.z * p.z)),
        Fp2.beq_symm (p.y * ((q.z * q.z) * q.z)) (q.y * ((p.z * p.z) * p.z))]

/-- When `p` is at infinity, `projectiveEq p q` holds if and only if `q` is also at infinity. -/
theorem projectiveEq_inf_iff {p q : G2} (hp : p.isInfinity = true) :
    projectiveEq p q = true ↔ q.isInfinity = true := by
  unfold projectiveEq isInfinity at *
  rw [ite_eq_left hp]

@[simp] theorem isInfinity_zero : G2.zero.isInfinity = true := by
  decide

/-! ## Compression and decompression -/

/-- An `Fp2` element encodes as `c1` then `c0`, `48 + 48 = 96` bytes (Section C.1). -/
@[simp] theorem size_fp2ToBytes (x : Fp2) : (G2.fp2ToBytes x).size = 96 := by
  unfold G2.fp2ToBytes
  rw [ByteArray.size_append, Fp.size_toBytesBE, Fp.size_toBytesBE]

private theorem ba_get!_append_left {a b : ByteArray} {i : Nat} (hi : i < a.size) :
    (a ++ b).get! i = a.get! i := by
  show (a ++ b).data[i]! = a.data[i]!
  rw [ByteArray.data_append]
  have hi' : i < (a.data ++ b.data).size := by
    rw [Array.size_append]
    exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)
  rw [getElem!_pos _ i hi', getElem!_pos a.data i hi, Array.getElem_append_left hi]

/-- The first byte is below `0x20`, so its top three bits are free for the flags. -/
theorem fp2ToBytes_head_lt (x : Fp2) : ((fp2ToBytes x).get! 0).toNat < 0x20 := by
  unfold fp2ToBytes
  rw [ba_get!_append_left (by rw [Fp.size_toBytesBE]; decide)]
  exact Fp.toBytesBE_head_lt x.c1

private theorem ba_extract_append_left {a b : ByteArray} (ha : a.size = 48) :
    (a ++ b).extract 0 48 = a := by
  have ha' : a.data.size = 48 := ha
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.data_append, ha',
    Array.extract_empty_of_stop_le_start]

private theorem ba_extract_append_right {a b : ByteArray} (ha : a.size = 48) (hb : b.size = 48) :
    (a ++ b).extract 48 96 = b := by
  have ha' : a.data.size = 48 := ha
  have hb' : b.data.size = 48 := hb
  apply ByteArray.ext
  simp [ByteArray.data_extract, ByteArray.data_append, ha', hb',
    Array.extract_empty_of_stop_le_start]

@[simp] theorem fp2ToBytes_extract_c1 (x : Fp2) :
    (fp2ToBytes x).extract 0 48 = x.c1.toBytesBE :=
  ba_extract_append_left (Fp.size_toBytesBE x.c1)

@[simp] theorem fp2ToBytes_extract_c0 (x : Fp2) :
    (fp2ToBytes x).extract 48 96 = x.c0.toBytesBE :=
  ba_extract_append_right (Fp.size_toBytesBE x.c1) (Fp.size_toBytesBE x.c0)

@[simp] theorem fromBytesBE_fp2ToBytes_c1 (x : Fp2) :
    Fp.fromBytesBE ((fp2ToBytes x).extract 0 48) = .ok x.c1 := by
  rw [fp2ToBytes_extract_c1, Fp.fromBytesBE_toBytesBE]

@[simp] theorem fromBytesBE_fp2ToBytes_c0 (x : Fp2) :
    Fp.fromBytesBE ((fp2ToBytes x).extract 48 96) = .ok x.c0 := by
  rw [fp2ToBytes_extract_c0, Fp.fromBytesBE_toBytesBE]

/-- Two `Fp2` elements with the same 96-byte encoding are equal. -/
theorem fp2ToBytes_injective : Function.Injective fp2ToBytes := by
  intro x y h
  -- Slice the 96 bytes at 48 to recover c1 from [0..48) and c0 from [48..96).
  have hc1 : Fp.fromBytesBE ((fp2ToBytes x).extract 0 48) =
      Fp.fromBytesBE ((fp2ToBytes y).extract 0 48) := by rw [h]
  have hc0 : Fp.fromBytesBE ((fp2ToBytes x).extract 48 96) =
      Fp.fromBytesBE ((fp2ToBytes y).extract 48 96) := by rw [h]
  rw [fromBytesBE_fp2ToBytes_c1, fromBytesBE_fp2ToBytes_c1] at hc1
  rw [fromBytesBE_fp2ToBytes_c0, fromBytesBE_fp2ToBytes_c0] at hc0
  exact Fp2.ext (Except.ok.inj hc0) (Except.ok.inj hc1)

/-- Any point with `z = 0` compresses to `G2.infinityBytes`. -/
theorem compress_inf {p : G2} (h : p.isInfinity = true) :
    G2.compress p = G2.infinityBytes := by
  -- Unfold Id.run and take the early return on p.isInfinity.
  unfold G2.compress
  simp only [Id.run, h, ↓reduceIte]
  rfl

private theorem compress_noninf {p : G2} (hinf : ¬ p.isInfinity = true)
    {xa ya : Fp2} (hpa : p.toAffine = (xa, ya)) :
    G2.compress p =
      (let base := (G2.fp2ToBytes xa).set! 0 ((G2.fp2ToBytes xa).get! 0 ||| 0x80)
       if Fp2.signBit ya then base.set! 0 (base.get! 0 ||| 0x20) else base) := by
  -- Unfold Id.run past the infinity guard and substitute p.toAffine = (xa, ya).
  unfold G2.compress
  simp only [Id.run, hinf, hpa]
  rfl

private theorem ba_size_set! (b : ByteArray) (j : Nat) (v : UInt8) :
    (b.set! j v).size = b.size := Array.size_setIfInBounds

/-- Compression always gives 96 bytes (Section C.1). -/
theorem size_compress (p : G2) : (G2.compress p).size = 96 := by
  by_cases h : p.isInfinity = true
  · rw [compress_inf h]
    decide
  · rcases hpa : p.toAffine with ⟨xa, ya⟩
    rw [compress_noninf h hpa]
    dsimp only
    by_cases hs : Fp2.signBit ya = true
    · rw [ite_eq_left hs, ba_size_set!, ba_size_set!, size_fp2ToBytes]
    · rw [ite_eq_right hs, ba_size_set!, size_fp2ToBytes]

/-- The 96-byte infinity encoding decodes to the zero point. -/
theorem uncompress_infinityBytes : G2.uncompress G2.infinityBytes = .ok G2.zero := by
  decide +kernel

/-! ## Rejection of malformed compressed inputs -/

/-- A fold that clears `ok` on any nonzero byte ends `true` only if every visited byte is zero. -/
private theorem foldl_allZero (b : ByteArray) (s n : Nat) (init : Bool)
    (h : (List.range' s n).foldl
      (fun ok i => if b.get! i ≠ 0 then false else ok) init = true) :
    init = true ∧ ∀ i, s ≤ i → i < s + n → b.get! i = 0 := by
  induction n generalizing s init with
  | zero => exact ⟨h, fun i h1 h2 => by omega⟩
  | succ n ih =>
    -- Peel off index s and apply the induction hypothesis to the tail.
    rw [List.range'_succ, List.foldl_cons] at h
    obtain ⟨hinit, hrest⟩ := ih (s + 1) _ h
    -- If byte s were nonzero, the accumulator would enter the tail as false and stay false.
    have hs : b.get! s = 0 := by
      by_contra hne
      rw [ite_eq_left hne] at hinit
      cases hinit
    refine ⟨by rwa [ite_eq_right (not_not.mpr hs)] at hinit, fun i h1 h2 => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact hs
    · exact hrest i hlt (by omega)

open EthLib.Cryptography.IdLoops in
/-- The imperative `tailAllZero` scan succeeds only if bytes `1` through `b.size - 1` are zero. -/
private theorem tailAllZero_ok (b : ByteArray)
    (h : (Id.run do
      let mut ok := true
      for i in [1 : b.size] do
        if b.get! i ≠ 0 then ok := false
      return ok) = true) :
    ∀ i, 1 ≤ i → i < b.size → b.get! i = 0 := by
  -- Rewrite the Id.run range loop into List.foldl over List.range'.
  dsimp only [Id.run, id_pure, id_bind] at h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  -- Pull ForInStep.yield outside the conditional so forIn_list_yield applies.
  have hbody : (fun (i : Nat) (ok : Bool) =>
      (if b.get! i ≠ 0 then ForInStep.yield false
        else ForInStep.yield ok : Id (ForInStep Bool)))
      = fun i ok => ForInStep.yield (if b.get! i ≠ 0 then false else ok) := by
    funext i ok; split <;> rfl
  change (forIn (m := Id) (List.range' 1 ([1 : b.size].size) 1) true
      (fun i ok => if b.get! i ≠ 0 then ForInStep.yield false else ForInStep.yield ok)) = true at h
  rw [hbody, forIn_list_yield] at h
  -- The range [1 : b.size] covers b.size - 1 indices starting at 1.
  have hsz : [1 : b.size].size = b.size - 1 := by
    simp [Std.Legacy.Range.size]
  rw [hsz] at h
  intro i hi1 hi2
  exact (foldl_allZero b 1 (b.size - 1) true h).2 i hi1 (by omega)

/-- Decoding rejects any input that is not 96 bytes long (Section C.2). -/
theorem uncompress_size_ne {bytes : ByteArray} (h : bytes.size ≠ 96) :
    G2.uncompress bytes = .error .invalidG2Point := by
  unfold G2.uncompress
  simp [h]

/-- Decoding rejects an input whose compression flag `0x80` is clear (Section C.2). -/
theorem uncompress_uncompressed {bytes : ByteArray} (hsz : bytes.size = 96)
    (h : (bytes.get! 0 &&& 0x80) = 0) :
    G2.uncompress bytes = .error .invalidG2Point := by
  unfold G2.uncompress
  simp [hsz, h]

set_option maxRecDepth 4000 in
private theorem head_e0_flags (head : UInt8) (h : (head &&& 0xe0) = 0xe0) :
    (head &&& 0x80) ≠ 0 ∧ (head &&& 0x40) ≠ 0 ∧ (head &&& 0x20) ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases head with ⟨⟨i⟩⟩; revert i h; decide

/-- Decoding rejects an infinity input that also sets the sign bit `0x20` (Section C.2). -/
theorem uncompress_infinity_sign_set {bytes : ByteArray} (hsz : bytes.size = 96)
    (h : (bytes.get! 0 &&& 0xe0) = 0xe0) :
    G2.uncompress bytes = .error .invalidG2Point := by
  -- All three top bits 0x80, 0x40, and 0x20 are set in byte 0.
  obtain ⟨hc, hi, hs⟩ := head_e0_flags (bytes.get! 0) h
  unfold G2.uncompress
  simp [hsz, hc, hi, hs]

set_option maxRecDepth 4000 in
private theorem head_c0_flags (head : UInt8) (h : (head &&& 0xc0) = 0xc0) :
    (head &&& 0x80) ≠ 0 ∧ (head &&& 0x40) ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases head with ⟨⟨i⟩⟩; revert i h; decide

/-- Decoding rejects an infinity input with a nonzero byte after the first (Section C.2). -/
theorem uncompress_infinity_nonzero_tail {bytes : ByteArray} (hsz : bytes.size = 96)
    (hc0 : (bytes.get! 0 &&& 0xc0) = 0xc0)
    {i : Nat} (hi1 : 1 ≤ i) (hi96 : i < 96) (hne : bytes.get! i ≠ 0) :
    G2.uncompress bytes = .error .invalidG2Point := by
  -- Extract the compression and infinity flags from the top two bits of byte 0.
  obtain ⟨hc, hinf⟩ := head_c0_flags (bytes.get! 0) hc0
  -- A nonzero byte at index i forces the tail scan to return false.
  have htail : (Id.run do
      let mut ok := true
      for j in [1 : bytes.size] do
        if bytes.get! j ≠ 0 then ok := false
      return ok) = false := by
    rw [Bool.eq_false_iff]
    intro hok
    exact hne (tailAllZero_ok bytes hok i hi1 (by omega))
  unfold G2.uncompress
  rw [ite_eq_right (by rw [hsz]; decide)]
  dsimp only
  rw [ite_eq_right (by rw [decide_eq_true hc]; decide),
      ite_eq_left hinf]
  -- With !tailAllZero = true, the three-way disjunction in the infinity check is true.
  have hcond :
      (decide ((bytes.get! 0 &&& 0x20) ≠ 0) ||
        decide (bytes.get! 0 ≠ 0xc0) ||
        !(Id.run do
          let mut ok := true
          for j in [1 : bytes.size] do
            if bytes.get! j ≠ 0 then ok := false
          return ok)) = true := by
    rw [htail]
    simp
  exact ite_eq_left hcond

/-- Decoding rejects a finite input whose `c1` bytes are not a canonical `Fp` element (Section C.2). -/
theorem uncompress_noncanonical_c1 {bytes : ByteArray} {e : BlsError}
    (hsz : bytes.size = 96)
    (hc : (bytes.get! 0 &&& 0x80) ≠ 0)
    (hi : (bytes.get! 0 &&& 0x40) = 0)
    (herr : Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 0 48) = .error e) :
    G2.uncompress bytes = .error .invalidG2Point := by
  unfold G2.uncompress
  rw [ite_eq_right (by rw [hsz]; decide)]
  dsimp only
  -- Enter the finite branch and reduce the pair match on the failed c1 decode.
  rw [ite_eq_right (by rw [decide_eq_true hc]; decide),
      ite_eq_right (by rw [hi]; decide), herr]

/-- Decoding rejects a finite input whose `c0` bytes are not a canonical `Fp` element (Section C.2). -/
theorem uncompress_noncanonical_c0 {bytes : ByteArray} {e : BlsError}
    (hsz : bytes.size = 96)
    (hc : (bytes.get! 0 &&& 0x80) ≠ 0)
    (hi : (bytes.get! 0 &&& 0x40) = 0)
    (herr : Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 48 96) = .error e) :
    G2.uncompress bytes = .error .invalidG2Point := by
  unfold G2.uncompress
  rw [ite_eq_right (by rw [hsz]; decide)]
  dsimp only
  -- Enter the finite branch and split on whether c1 succeeded or failed first.
  rw [ite_eq_right (by rw [decide_eq_true hc]; decide),
      ite_eq_right (by rw [hi]; decide), herr]
  cases Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 0 48) <;> rfl

/-! ## Curve membership of decoded points -/

private theorem isOnTwist_of_z_one {x y : Fp2} (h : y * y = x * x * x + bTwist) :
    G2.isOnTwist ⟨x, y, Fp2.one⟩ = true := by
  unfold isOnTwist
  have hinf : (⟨x, y, Fp2.one⟩ : G2).isInfinity = false :=
    show Fp2.one.isZero = false by decide
  rw [ite_eq_right (by rw [hinf]; decide)]
  dsimp only
  have h1 : Fp2.one * Fp2.one = Fp2.one := by decide
  have hb : bTwist * Fp2.one = bTwist := mul_one bTwist
  rw [h1, h1, h1, hb, h]
  exact beq_self_eq_true _

private theorem sq_select_fp2 (yPos : Fp2) (P : Prop) [Decidable P] :
    (if P then yPos else -yPos) * (if P then yPos else -yPos) = yPos * yPos := by
  split
  · rfl
  · exact neg_mul_neg yPos yPos

/-- A decoded point is either infinity or a point on the twist with `z = 1`.

Decoding checks that the point is on the curve (Section C.2).

It does not check that the point is in the subgroup of order `r`.
-/
theorem uncompress_valid {bytes : ByteArray} {p : G2}
    (h : G2.uncompress bytes = .ok p) :
    p = G2.zero ∨ (p.z = Fp2.one ∧ G2.isOnTwist p = true) := by
  rw [uncompress] at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      -- Infinity branch: returns G2.zero when header and tail checks pass.
      · split at h
        · cases h
        · cases h
          exact Or.inl rfl
      -- Finite branch: decodes c1 and c0, takes a square root of x^3 + bTwist, and sets z = 1.
      · cases hc1 : Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 0 48) <;>
          rw [hc1] at h
        · cases h
        · rename_i c1
          cases hc0 : Fp.fromBytesBE ((bytes.set! 0 (bytes.get! 0 &&& 0x1f)).extract 48 96) <;>
              rw [hc0] at h
          · cases h
          · rename_i c0
            dsimp only at h
            cases hsqrt : Fp2.sqrt (⟨c0, c1⟩ * ⟨c0, c1⟩ * ⟨c0, c1⟩ + bTwist) <;>
                rw [hsqrt] at h
            · cases h
            · rename_i yPos
              cases h
              refine Or.inr ⟨rfl, isOnTwist_of_z_one ?_⟩
              rw [sq_select_fp2]
              exact Fp2.sqrt_ok hsqrt

/-- Every point returned by `G2.uncompress` satisfies `G2.isOnTwist`. -/
theorem isOnTwist_of_uncompress {bytes : ByteArray} {p : G2}
    (h : G2.uncompress bytes = .ok p) : G2.isOnTwist p = true := by
  rcases uncompress_valid h with rfl | ⟨_, htwist⟩
  · exact isOnTwist_zero
  · exact htwist

@[simp] theorem compress_zero : G2.compress G2.zero = G2.infinityBytes :=
  compress_inf isInfinity_zero

@[simp] theorem uncompress_compress_zero :
    G2.uncompress (G2.compress G2.zero) = .ok G2.zero := by
  rw [compress_zero]
  exact uncompress_infinityBytes

private theorem ba_get!_set!_self (b : ByteArray) {j : Nat} (v : UInt8)
    (hj : j < b.size) : (b.set! j v).get! j = v := by
  show (b.data.setIfInBounds j v)[j]! = v
  rw [getElem!_pos (b.data.setIfInBounds j v) j
    (by rw [Array.size_setIfInBounds]; exact hj), Array.getElem_setIfInBounds_self]

private theorem ba_get!_set!_ne (b : ByteArray) {i j : Nat} (v : UInt8)
    (hne : i ≠ j) : (b.set! j v).get! i = b.get! i := by
  show (b.data.setIfInBounds j v)[i]! = b.data[i]!
  by_cases hi : i < b.data.size
  · rw [getElem!_pos (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_pos b.data i hi, Array.getElem_setIfInBounds_ne hi (fun hh => hne hh.symm)]
  · rw [getElem!_neg (b.data.setIfInBounds j v) i
        (by rw [Array.size_setIfInBounds]; exact hi),
      getElem!_neg b.data i hi]

private theorem ba_ext {a b : ByteArray} (hsz : a.size = b.size)
    (h : ∀ i, i < a.size → a.get! i = b.get! i) : a = b := by
  apply ByteArray.ext
  apply Array.ext hsz
  intro i hi1 hi2
  have := h i hi1
  rwa [show a.get! i = a.data[i]! from rfl, show b.get! i = b.data[i]! from rfl,
    getElem!_pos a.data i hi1, getElem!_pos b.data i hi2] at this

/-! ## Flags in the compressed header byte

Byte 0 of a compressed `G2` point carries three flags above the five high bits of `x.c1`.

```text
    bit    7            6          5      4 3 2 1 0
         [ compressed | infinity | sign | high bits of x.c1 ]
           0x80         0x40       0x20   0x1f
```

A canonical `x.c1` is below `2^381`, so its top byte is below `0x20` and never overlaps the flags.
-/

set_option maxRecDepth 4000 in
private theorem b0_pos_c (B0 : UInt8) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x80 ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

set_option maxRecDepth 4000 in
private theorem b0_pos_i (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x40 = 0 := by
  -- Check all 256 byte values in the kernel, where B0 >= 0x20 holds vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

set_option maxRecDepth 4000 in
private theorem b0_pos_s (B0 : UInt8) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x20 ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

set_option maxRecDepth 4000 in
private theorem b0_pos_m (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80 ||| 0x20) &&& 0x1f = B0 := by
  -- Check all 256 byte values in the kernel, where B0 >= 0x20 holds vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

set_option maxRecDepth 4000 in
private theorem b0_neg_c (B0 : UInt8) :
    (B0 ||| 0x80) &&& 0x80 ≠ 0 := by
  -- Check all 256 byte values in the kernel.
  rcases B0 with ⟨⟨i⟩⟩; revert i; decide

set_option maxRecDepth 4000 in
private theorem b0_neg_i (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x40 = 0 := by
  -- Check all 256 byte values in the kernel, where B0 >= 0x20 holds vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

set_option maxRecDepth 4000 in
private theorem b0_neg_s (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x20 = 0 := by
  -- Check all 256 byte values in the kernel, where B0 >= 0x20 holds vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

set_option maxRecDepth 4000 in
private theorem b0_neg_m (B0 : UInt8) (hb0 : B0 < 0x20) :
    (B0 ||| 0x80) &&& 0x1f = B0 := by
  -- Check all 256 byte values in the kernel, where B0 >= 0x20 holds vacuously.
  rcases B0 with ⟨⟨i⟩⟩; revert i hb0; decide

/-- `G2.compress p` equals `G2.infinityBytes` if and only if `p` is at infinity.

A finite point keeps the infinity flag `0x40` clear, since its first byte is below `0x20`.
-/
theorem compress_eq_infinityBytes_iff (p : G2) :
    G2.compress p = G2.infinityBytes ↔ p.isInfinity = true := by
  refine ⟨fun h => ?_, compress_inf⟩
  by_contra hinf
  rcases hpa : p.toAffine with ⟨xa, ya⟩
  have hcp := compress_noninf hinf hpa
  set B0 := (fp2ToBytes xa).get! 0 with hB0
  have hb0 : B0 < 0x20 := by
    rw [hB0, UInt8.lt_iff_toNat_lt]
    exact fp2ToBytes_head_lt xa
  have hsz96 : (fp2ToBytes xa).size = 96 := size_fp2ToBytes xa
  -- In the finite branch, bit 0x40 of byte 0 is always 0.
  have hbit : ((G2.compress p).get! 0) &&& 0x40 = 0 := by
    rw [hcp]
    dsimp only
    by_cases hs : Fp2.signBit ya = true
    · rw [ite_eq_left hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz96]; decide),
        ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
      exact b0_pos_i B0 hb0
    · rw [ite_eq_right hs, ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
      exact b0_neg_i B0 hb0
  have hinf_bit : (G2.infinityBytes.get! 0) &&& 0x40 ≠ 0 := by decide
  rw [h] at hbit
  exact hinf_bit hbit

/-! ## Affine normalization and compression round-trip -/

/-- Projecting a point with `z = 1` to affine coordinates leaves `(x, y)` unchanged. -/
@[simp] theorem toAffine_of_z_one (x y : Fp2) :
    (⟨x, y, Fp2.one⟩ : G2).toAffine = (x, y) := by
  unfold toAffine
  have h1z : Fp2.one.isZero = false := by decide
  rw [ite_eq_right (by rw [h1z]; decide)]
  have hinv : Fp2.one.inverse = 1 := by
    have h := Fp2.mul_inverse_cancel (a := 1) (by decide)
    rwa [one_mul] at h
  dsimp only
  rw [hinv, mul_one, mul_one, mul_one, mul_one]

private theorem curve_eq_fp2 (x y z w : Fp2) (hw : z * w = 1)
    (heq : y * y = x * x * x + bTwist * (z * z * z * (z * z * z))) :
    (y * (w * w * w)) * (y * (w * w * w)) =
      (x * (w * w)) * (x * (w * w)) * (x * (w * w)) + bTwist := by
  have h6 : (z * w) ^ 6 = 1 := by rw [hw, one_pow]
  linear_combination w ^ 6 * heq + bTwist * h6

/-- For a finite point on the twist, its affine `y` coordinate squares to `x^3 + bTwist`. -/
theorem affine_sqrt_witness {p : G2} (h : G2.isOnTwist p = true) (hinf : ¬ p.isInfinity = true) :
    (p.toAffine).2 * (p.toAffine).2 =
      (p.toAffine).1 * (p.toAffine).1 * (p.toAffine).1 + bTwist := by
  unfold isOnTwist at h
  rw [ite_eq_right hinf] at h
  have heq : p.y * p.y = p.x * p.x * p.x + bTwist * (p.z * p.z * p.z * (p.z * p.z * p.z)) :=
    eq_of_beq h
  have hzne : p.z ≠ 0 := fun hz0 => hinf (Fp2.isZero_iff.mpr hz0)
  have hw : p.z * p.z.inverse = 1 := Fp2.mul_inverse_cancel hzne
  have hpz : ¬ p.z.isZero = true := hinf
  simp only [G2.toAffine, ite_eq_right hpz]
  exact curve_eq_fp2 p.x p.y p.z p.z.inverse hw heq

private theorem xeq_fp2 (x z w : Fp2) (hw : z * w = 1) :
    x * (w * w) * (z * z) = x * (1 * 1) := by
  linear_combination x * (z * w + 1) * hw

private theorem yeq_fp2 (y z w : Fp2) (hw : z * w = 1) :
    y * (w * w * w) * (z * z * z) = y * (1 * 1 * 1) := by
  linear_combination y * ((z * w) ^ 2 + z * w + 1) * hw

/-- A finite point equals its affine form with `z = 1`, as a projective point. -/
theorem projectiveEq_toAffine {p : G2} (hinf : ¬ p.isInfinity = true) :
    projectiveEq ⟨(p.toAffine).1, (p.toAffine).2, Fp2.one⟩ p = true := by
  have hpz : ¬ p.z.isZero = true := hinf
  have hzne : p.z ≠ 0 := fun hz0 => hinf (Fp2.isZero_iff.mpr hz0)
  have hw : p.z * p.z.inverse = 1 := Fp2.mul_inverse_cancel hzne
  unfold projectiveEq
  rw [ite_eq_right (by decide : ¬ Fp2.one.isZero = true), ite_eq_right hpz]
  dsimp only [G2.toAffine]
  rw [ite_eq_right hpz]
  dsimp only
  -- Reduce both cross-multiplications to z * z.inverse = 1.
  rw [Bool.and_eq_true, _root_.beq_iff_eq, _root_.beq_iff_eq]
  exact ⟨xeq_fp2 p.x p.z p.z.inverse hw, yeq_fp2 p.y p.z p.z.inverse hw⟩

private theorem sqrt_pm_fp2 {ya yPos : Fp2}
    (h : yPos * yPos = ya * ya) : yPos = ya ∨ yPos = -ya := by
  have hfac : (yPos - ya) * (yPos + ya) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

private theorem sign_recovery_fp2 {ya yPos : Fp2}
    (hsq : yPos * yPos = ya * ya) :
    (if Fp2.signBit yPos = Fp2.signBit ya then yPos else -yPos) = ya := by
  rcases sqrt_pm_fp2 hsq with rfl | rfl
  · rw [ite_eq_left rfl]
  · by_cases hya : ya = 0
    · subst hya
      simp [show (-0 : Fp2) = 0 from _root_.neg_zero]
    · rw [Fp2.signBit_neg hya, ite_eq_right (Bool.not_ne_self _), _root_.neg_neg]

private theorem sign_recovery_fp2' {ya yPos : Fp2} {P : Prop} [Decidable P]
    (hsq : yPos * yPos = ya * ya)
    (hP : P ↔ (Fp2.signBit ya = true)) :
    (if (Fp2.signBit yPos = true) = P then yPos else -yPos) = ya := by
  have key : ((Fp2.signBit yPos = true) = P) ↔ (Fp2.signBit yPos = Fp2.signBit ya) := by
    rw [eq_iff_iff, hP]
    by_cases h1 : Fp2.signBit yPos = true <;> by_cases h2 : Fp2.signBit ya = true <;>
      simp_all
  rw [if_congr key rfl rfl]
  exact sign_recovery_fp2 hsq

private theorem uncompress_of_facts {xa ya yPos : Fp2} {cb : ByteArray}
    (hsize : cb.size = 96)
    (hc : (cb.get! 0 &&& 0x80) ≠ 0)
    (hi : (cb.get! 0 &&& 0x40) = 0)
    (hsg : (cb.get! 0 &&& 0x20 ≠ 0) ↔ (Fp2.signBit ya = true))
    (hmaskeq : cb.set! 0 (cb.get! 0 &&& 0x1f) = fp2ToBytes xa)
    (hsqrt : Fp2.sqrt (xa * xa * xa + bTwist) = .ok yPos)
    (hysq : yPos * yPos = ya * ya) :
    G2.uncompress cb = .ok ⟨xa, ya, Fp2.one⟩ := by
  rw [uncompress, ite_eq_right (by rw [hsize]; decide)]
  simp only
  rw [ite_eq_right (by rw [decide_eq_true hc]; decide), ite_eq_right (by rw [hi]; decide),
    hmaskeq, fromBytesBE_fp2ToBytes_c1, fromBytesBE_fp2ToBytes_c0]
  simp only [show (⟨xa.c0, xa.c1⟩ : Fp2) = xa from Fp2.ext rfl rfl, hsqrt]
  rw [sign_recovery_fp2' hysq hsg]

/-- A finite point on the twist decodes back to its affine form with `z = 1`. -/
theorem uncompress_compress_noninf {p : G2} (h : G2.isOnTwist p = true)
    (hinf : ¬ p.isInfinity = true) :
    G2.uncompress (G2.compress p) = .ok ⟨(p.toAffine).1, (p.toAffine).2, Fp2.one⟩ := by
  rcases hpa : p.toAffine with ⟨xa, ya⟩
  set B0 := (fp2ToBytes xa).get! 0 with hB0
  have hb0 : B0 < 0x20 := by
    rw [hB0, UInt8.lt_iff_toNat_lt]; exact fp2ToBytes_head_lt xa
  have hsqw : ya * ya = xa * xa * xa + bTwist := by
    have := affine_sqrt_witness h hinf; rw [hpa] at this; exact this
  obtain ⟨yPos, hsqrt⟩ := Fp2.sqrt_complete hsqw
  have hysq : yPos * yPos = ya * ya := by rw [Fp2.sqrt_ok hsqrt, ← hsqw]
  have hsz96 : (fp2ToBytes xa).size = 96 := size_fp2ToBytes xa
  have hcp := compress_noninf hinf hpa
  have hother : ∀ i, i ≠ 0 → (G2.compress p).get! i = (fp2ToBytes xa).get! i := by
    intro i hi0
    rw [hcp]; dsimp only
    by_cases hs : Fp2.signBit ya
    · rw [ite_eq_left hs, ba_get!_set!_ne _ _ hi0, ba_get!_set!_ne _ _ hi0]
    · rw [ite_eq_right hs, ba_get!_set!_ne _ _ hi0]
  have hsize : (G2.compress p).size = 96 := size_compress p
  by_cases hs : Fp2.signBit ya
  -- Sign bit set: header byte carries 0x80 | 0x20 above the five top bits of xa.c1.
  · have hhead : (G2.compress p).get! 0 = B0 ||| 0x80 ||| 0x20 := by
      rw [hcp]; dsimp only
      rw [ite_eq_left hs, ba_get!_set!_self _ _ (by rw [ba_size_set!, hsz96]; decide),
        ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
    refine uncompress_of_facts hsize (by rw [hhead]; exact b0_pos_c B0)
      (by rw [hhead]; exact b0_pos_i B0 hb0) ?_ ?_ hsqrt hysq
    · rw [hhead]
      exact ⟨fun _ => hs, fun _ => b0_pos_s B0⟩
    · refine ba_ext (by rw [ba_size_set!, hsize, hsz96]) (fun i hi' => ?_)
      rw [ba_size_set!, hsize] at hi'
      by_cases hi0 : i = 0
      · subst hi0
        rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]
        exact b0_pos_m B0 hb0
      · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]
  -- Sign bit clear: header byte carries only 0x80 above the five top bits of xa.c1.
  · have hhead : (G2.compress p).get! 0 = B0 ||| 0x80 := by
      rw [hcp]; dsimp only
      rw [ite_eq_right hs, ba_get!_set!_self _ _ (by rw [hsz96]; decide)]
    refine uncompress_of_facts hsize (by rw [hhead]; exact b0_neg_c B0)
      (by rw [hhead]; exact b0_neg_i B0 hb0) ?_ ?_ hsqrt hysq
    · rw [hhead]
      exact ⟨fun hne => absurd (b0_neg_s B0 hb0) hne, fun hh => absurd hh hs⟩
    · refine ba_ext (by rw [ba_size_set!, hsize, hsz96]) (fun i hi' => ?_)
      rw [ba_size_set!, hsize] at hi'
      by_cases hi0 : i = 0
      · subst hi0
        rw [ba_get!_set!_self _ _ (by rw [hsize]; decide), hhead, ← hB0]
        exact b0_neg_m B0 hb0
      · rw [ba_get!_set!_ne _ _ hi0, hother i hi0]

/-- Encoding then decoding a twist point gives back the same projective point (C.1, C.2).

Infinity decodes to the zero triple.

A finite point decodes to its affine form with `z = 1`.
-/
theorem uncompress_compress {p : G2} (h : G2.isOnTwist p = true) :
    ∃ q, G2.uncompress (G2.compress p) = .ok q ∧ projectiveEq q p = true := by
  by_cases hinf : p.isInfinity = true
  · refine ⟨G2.zero, ?_, ?_⟩
    · rw [compress_inf hinf]; exact uncompress_infinityBytes
    · exact (projectiveEq_inf_iff isInfinity_zero).mpr hinf
  · exact ⟨⟨(p.toAffine).1, (p.toAffine).2, Fp2.one⟩,
      uncompress_compress_noninf h hinf, projectiveEq_toAffine hinf⟩

/-- A point on the twist with `z = 1` comes back as the exact same triple. -/
theorem uncompress_compress_of_z_one {p : G2} (hz : p.z = Fp2.one)
    (h : G2.isOnTwist p = true) :
    G2.uncompress (G2.compress p) = .ok p := by
  rcases p with ⟨x, y, z⟩
  dsimp only at hz
  subst hz
  have hinf : ¬ (⟨x, y, Fp2.one⟩ : G2).isInfinity = true := by
    change ¬ Fp2.one.isZero = true; decide
  have hrt := uncompress_compress_noninf h hinf
  rwa [toAffine_of_z_one] at hrt

/-- Compressing and decompressing `G2.generator` recovers `G2.generator`. -/
@[simp] theorem uncompress_compress_generator :
    G2.uncompress (G2.compress G2.generator) = .ok G2.generator :=
  uncompress_compress_of_z_one rfl isOnTwist_generator

/-! ## Converse decompression round-trip (`compress_uncompress`) -/

private theorem signBit_select_fp2 {yPos : Fp2} (hypos : yPos ≠ 0)
    {P : Prop} [Decidable P] :
    Fp2.signBit (if (Fp2.signBit yPos = true) = P then yPos else -yPos)
      = decide P := by
  -- Negation flips signBit when yPos != 0, so the branch matches P in all four cases.
  by_cases hP : P <;> by_cases hs : Fp2.signBit yPos = true
  · rw [ite_eq_left (by simp [hP, hs]), hs, decide_eq_true hP]
  · rw [ite_eq_right (by simp [hP, hs]), Fp2.signBit_neg hypos,
      Bool.eq_false_iff.mpr hs, Bool.not_false, decide_eq_true hP]
  · rw [ite_eq_right (by simp [hP, hs]), Fp2.signBit_neg hypos, hs,
      Bool.not_true, decide_eq_false hP]
  · rw [ite_eq_left (by simp [hP, hs]), Bool.eq_false_iff.mpr hs, decide_eq_false hP]

set_option maxRecDepth 4000 in
private theorem infinityBytes_get!_pos (i : Fin 96) (hi : 1 ≤ i.val) :
    infinityBytes.get! i.val = 0 := by
  -- Check all 95 trailing indices in the kernel.
  revert hi i; decide

private theorem ba_set!_set!_same (b : ByteArray) (j : Nat) (u v : UInt8) :
    (b.set! j u).set! j v = b.set! j v := by
  refine ba_ext (by rw [ba_size_set!, ba_size_set!, ba_size_set!]) (fun i hi => ?_)
  rw [ba_size_set!, ba_size_set!] at hi
  by_cases hij : i = j
  · subst hij
    rw [ba_get!_set!_self _ _ (by rw [ba_size_set!]; exact hi),
      ba_get!_set!_self _ _ hi]
  · rw [ba_get!_set!_ne _ _ hij, ba_get!_set!_ne _ _ hij, ba_get!_set!_ne _ _ hij]

private theorem ba_set!_get!_self (b : ByteArray) {j : Nat} (hj : j < b.size) :
    b.set! j (b.get! j) = b := by
  refine ba_ext (ba_size_set! b j _) (fun i hi => ?_)
  rw [ba_size_set!] at hi
  by_cases hij : i = j
  · subst hij; exact ba_get!_set!_self b _ hj
  · exact ba_get!_set!_ne b _ hij

set_option maxRecDepth 4000 in
private theorem head_reconstruct (head : UInt8)
    (hc : (head &&& 0x80) ≠ 0) (hi : (head &&& 0x40) = 0) :
    (if (head &&& 0x20) ≠ 0 then (head &&& 0x1f) ||| 0x80 ||| 0x20
     else (head &&& 0x1f) ||| 0x80) = head := by
  -- Check all 256 byte values in the kernel: bits 7=1, 6=0, 5=s, and 4..0 rebuild head.
  rcases head with ⟨⟨i⟩⟩; revert i hc hi; decide

private theorem ba_extract_append_extract {b : ByteArray} (hsz : b.size = 96) :
    b.extract 0 48 ++ b.extract 48 96 = b := by
  have hsz' : b.data.size = 96 := hsz
  apply ByteArray.ext
  simp [← hsz']

private theorem bool_eq_true_of_not_eq_false {ok : Bool} (h : (!ok) = false) :
    ok = true := by
  cases ok <;> first | rfl | contradiction

/-- Decoding then encoding gives back the exact 96 input bytes (C.1, C.2).

```text
    infinity:   [ 0xc0 | 95 zero bytes ]                      checked byte by byte
    finite:     [ 1 0 s c1_top | 47 bytes c1 | 48 bytes c0 ]  c1, c0 < p, s = signBit y
```

- Infinity accepts only `0xc0` followed by 95 zero bytes, matching `G2.infinityBytes`.
- Finite inputs decode canonical `c1` and `c0`.
- Because `yPos != 0`, the selected root reproduces the input sign flag `s`.
-/
theorem compress_uncompress {b : ByteArray} {q : G2}
    (h : G2.uncompress b = .ok q) : G2.compress q = b := by
  rw [uncompress] at h
  split at h
  · cases h
  · rename_i hsz
    have hsz96 : b.size = 96 := by omega
    dsimp only at h
    split at h
    · cases h
    · rename_i hcomp
      -- Header bit 0x80 is set.
      have hc : (b.get! 0 &&& 0x80) ≠ 0 := by
        by_contra h0
        exact hcomp (by simp [h0])
      split at h
      -- Infinity branch: header is 0xc0 and bytes 1..95 are zero.
      · split at h
        · cases h
        · rename_i hflags
          cases h
          rw [compress_inf rfl]
          simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hflags
          obtain ⟨⟨_, hhead⟩, htail⟩ := hflags
          have hhead0 : b.get! 0 = 0xc0 := Classical.not_not.mp (of_decide_eq_false hhead)
          have htail0 : ∀ i, 1 ≤ i → i < b.size → b.get! i = 0 :=
            tailAllZero_ok b (bool_eq_true_of_not_eq_false htail)
          refine ba_ext (by rw [hsz96]; decide) (fun i hi => ?_)
          have hi96 : i < 96 := by simpa [show infinityBytes.size = 96 by decide] using hi
          by_cases hi0 : i = 0
          · subst hi0
            rw [hhead0]
            decide
          · have hi1 : 1 ≤ i := Nat.pos_of_ne_zero hi0
            have hib : i < b.size := by rw [hsz96]; exact hi96
            rw [infinityBytes_get!_pos ⟨i, hi96⟩ hi1, htail0 i hi1 hib]
      -- Finite branch: header bit 0x40 is clear, c1 and c0 are canonical, and yPos != 0.
      · rename_i hinf_flag
        have hi : (b.get! 0 &&& 0x40) = 0 := not_ne_iff.mp hinf_flag
        cases hc1 : Fp.fromBytesBE ((b.set! 0 (b.get! 0 &&& 0x1f)).extract 0 48) <;>
            rw [hc1] at h
        · cases h
        · rename_i c1
          cases hc0 : Fp.fromBytesBE ((b.set! 0 (b.get! 0 &&& 0x1f)).extract 48 96) <;>
              rw [hc0] at h
          · cases h
          · rename_i c0
            dsimp only at h
            cases hsqrt : Fp2.sqrt (⟨c0, c1⟩ * ⟨c0, c1⟩ * ⟨c0, c1⟩ + bTwist) <;>
                rw [hsqrt] at h
            · cases h
            · rename_i yPos
              cases h
              set x : Fp2 := ⟨c0, c1⟩
              set y : Fp2 :=
                if (Fp2.signBit yPos = true) = ((b.get! 0 &&& 0x20) ≠ 0) then yPos else -yPos
              have hqinf : ¬ (⟨x, y, Fp2.one⟩ : G2).isInfinity = true := by
                change ¬ Fp2.one.isZero = true
                decide
              have hpa : (⟨x, y, Fp2.one⟩ : G2).toAffine = (x, y) := toAffine_of_z_one x y
              rw [compress_noninf hqinf hpa]
              dsimp only
              -- Re-encoding x concatenates the canonical 48-byte slices of c1 and c0.
              have hxbytes : fp2ToBytes x = b.set! 0 (b.get! 0 &&& 0x1f) := by
                unfold fp2ToBytes
                dsimp only [x]
                rw [Fp.toBytesBE_fromBytesBE hc1, Fp.toBytesBE_fromBytesBE hc0]
                exact ba_extract_append_extract (by rw [ba_size_set!, hsz96])
              -- Because x^3 + bTwist != 0, the square root yPos cannot be zero.
              have hypos : yPos ≠ 0 := by
                intro hy0
                have hsq := Fp2.sqrt_ok hsqrt
                rw [hy0, Fp2.mul_zero] at hsq
                exact cube_add_bTwist_ne_zero x hsq.symm
              have hsign : Fp2.signBit y = decide ((b.get! 0 &&& 0x20) ≠ 0) :=
                signBit_select_fp2 hypos
              have h0lt : 0 < b.size := by omega
              have hbase :
                  (fp2ToBytes x).set! 0 ((fp2ToBytes x).get! 0 ||| 0x80) =
                    b.set! 0 ((b.get! 0 &&& 0x1f) ||| 0x80) := by
                rw [hxbytes, ba_get!_set!_self b _ h0lt, ba_set!_set!_same]
              by_cases hs : (b.get! 0 &&& 0x20) ≠ 0
              -- Sign flag set: compression sets 0x20 and reconstructs byte 0.
              · have hsy : Fp2.signBit y = true := by rw [hsign, decide_eq_true hs]
                have hrec := head_reconstruct (b.get! 0) hc hi
                rw [ite_eq_left hs] at hrec
                rw [ite_eq_left hsy, hbase, ba_get!_set!_self b _ h0lt,
                  ba_set!_set!_same, hrec, ba_set!_get!_self b h0lt]
              -- Sign flag clear: compression leaves 0x20 clear and reconstructs byte 0.
              · have hsy : ¬ Fp2.signBit y = true := by rw [hsign, decide_eq_false hs]; decide
                have hrec := head_reconstruct (b.get! 0) hc hi
                rw [ite_eq_right hs] at hrec
                rw [ite_eq_right hsy, hbase, hrec, ba_set!_get!_self b h0lt]

/-- Two byte strings that decode to the same point are equal.

So each point on the twist has at most one 96-byte encoding.

In particular, a `G2` signature cannot be re-encoded into a second valid form.
-/
theorem uncompress_injective {b₁ b₂ : ByteArray} {q : G2}
    (h₁ : G2.uncompress b₁ = .ok q) (h₂ : G2.uncompress b₂ = .ok q) : b₁ = b₂ := by
  -- Both byte strings equal G2.compress q.
  rw [← compress_uncompress h₁, compress_uncompress h₂]

end G2

end EthLib.Cryptography.Bls
