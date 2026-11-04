module

public import EthLib.Execution.Evm.Precompiles.Bls12381.Encoding
public import EthLib.Base.Proofs.BigEndian

/-!
# Proofs: `Evm.Precompiles.Bls12381.Encoding`

- The decoder removes exactly the padding that the encoder adds.
- Field elements and affine points on the curve decode back to themselves.
- The point at infinity is all zero bytes, in both directions.
- A decoded field element or G1 point encodes back to its bytes, so that encoding is canonical.
- The padding check and the field check of Amsterdam reject exactly the inputs that Prague's single field check rejects.
- The known answers state a result as an `Except` and check it through its bytes, which the kernel compares fast.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bytesToNat natToBytes)
open EthLib.Cryptography.Bls (Fp Fp2 G1 G2)

/-! ## Padding -/

/-- The decoder gives back the 48 bytes of a padded field element. -/
theorem unpadFp_pad (raw : List UInt8) : unpadFp (zeroPad ++ raw) = .ok raw := by
  simp [unpadFp, zeroPad, PAD_BYTES]

/-- The decoder gives back the 96 bytes of a padded G1 point. -/
theorem unpadG1_padG1 {raw : List UInt8} (hlength : raw.length = 96) : unpadG1 (padG1 raw) = .ok raw := by
  have htake : (raw.take 48).length = 48 := by simp [hlength]
  simp [unpadG1, padG1, zeroPad, PAD_BYTES, unpadFp, htake, bind, Except.bind, pure, Except.pure]
  -- After the first 48 bytes, the other 48 are all that is left.
  rw [List.take_of_length_le (l := List.drop 48 raw) (by simp [hlength]), List.take_append_drop]

/-- The decoder gives back the 192 bytes of a padded G2 point. -/
theorem unpadG2_padG2 {raw : List UInt8} (hlength : raw.length = 192) :
    unpadG2 (padG2 raw) = .ok raw := by
  -- Each of the four padded field elements has 64 bytes.
  have h0 : (zeroPad ++ raw.take 48).length = 64 := by simp [zeroPad, PAD_BYTES, hlength]
  have h1 : (zeroPad ++ (raw.drop 48).take 48).length = 64 := by
    simp [zeroPad, PAD_BYTES, hlength]
  have h2 : (zeroPad ++ (raw.drop 96).take 48).length = 64 := by
    simp [zeroPad, PAD_BYTES, hlength]
  have h3 : (zeroPad ++ raw.drop 144).length = 64 := by simp [zeroPad, PAD_BYTES, hlength]
  have hpad : padG2 raw = (zeroPad ++ raw.take 48) ++ ((zeroPad ++ (raw.drop 48).take 48) ++
      ((zeroPad ++ (raw.drop 96).take 48) ++ (zeroPad ++ raw.drop 144))) := by
    simp only [padG2, List.append_assoc]
  -- The four pieces put back together are the point.
  have hjoin :
      raw.take 48 ++ (raw.drop 48).take 48 ++ (raw.drop 96).take 48 ++ raw.drop 144 = raw := by
    conv => rhs; rw [← List.take_append_drop 48 raw, ← List.take_append_drop 48 (raw.drop 48),
      ← List.take_append_drop 48 ((raw.drop 48).drop 48)]
    simp [List.drop_drop, List.append_assoc]
  -- Dropping two or three whole 64-byte pieces leaves the rest.
  have drop128 : ∀ A B R : List UInt8, A.length = 64 → B.length = 64 →
      (A ++ (B ++ R)).drop 128 = R :=
    fun A B R hA hB => by rw [← List.append_assoc]; exact List.drop_left' (by simp [hA, hB])
  have drop192 : ∀ A B C R : List UInt8, A.length = 64 → B.length = 64 → C.length = 64 →
      (A ++ (B ++ (C ++ R))).drop 192 = R := fun A B C R hA hB hC => by
    rw [← List.append_assoc, ← List.append_assoc]; exact List.drop_left' (by simp [hA, hB, hC])
  rw [hpad]
  unfold unpadG2
  rw [drop128 _ _ _ h0 h1, drop192 _ _ _ _ h0 h1 h2, List.drop_left' h0, List.take_left' h0,
    List.take_left' h1, List.take_left' h2, List.take_of_length_le (Nat.le_of_eq h3)]
  simp only [unpadFp_pad, bind, Except.bind, pure, Except.pure, hjoin]

/-! ## The field check of Prague -/

/-- A padded field element decodes in two steps exactly when it is below the field modulus as one 64-byte integer.

Prague reads the 64 bytes as one integer and rejects it unless it is below the modulus.

Amsterdam first rejects nonzero padding, then reads the 48 bytes.

Nonzero padding makes the 64-byte integer at least `2^384`, above the modulus, so both reject the same inputs. -/
theorem unpadFp_bytesToFieldElement_isOk {padded : List UInt8} (hlength : padded.length = 64) :
    ((unpadFp padded) >>= bytesToFieldElement).toOption.isSome ↔ bytesToNat padded < Fp.modulus := by
  -- The 64 bytes are 16 high bytes, then 48 low bytes.
  have hsplit := EthLib.Base.bytesToNat_append (padded.take 16) (padded.drop 16)
  rw [List.take_append_drop] at hsplit
  have hlow : (padded.drop 16).length = 48 := by simp [hlength]
  have hhigh : (padded.take 16).length = 16 := by simp [hlength]
  have hlt := EthLib.Base.bytesToNat_lt (padded.drop 16)
  rw [hlow] at hlt
  have hmodulus : Fp.modulus < 256 ^ 48 := by decide
  by_cases hpad : padded.take 16 = List.replicate 16 0
  · -- Zero padding: the 64-byte integer is the 48-byte integer.
    have hzero : bytesToNat (padded.take 16) = 0 := by
      rw [hpad]
      rfl
    simp only [unpadFp, PAD_BYTES, hpad, ↓reduceIte, bind, Except.bind, bytesToFieldElement]
    rw [hsplit, hzero, Nat.zero_mul, Nat.zero_add]
    split
    · rename_i hlt'
      simp [Except.toOption, hlt']
    · rename_i hge
      simp [Except.toOption, hge]
  · -- Nonzero padding: the 64-byte integer is at least `2^384`.
    have hpos : 0 < bytesToNat (padded.take 16) := by
      rcases Nat.eq_zero_or_pos (bytesToNat (padded.take 16)) with h | h
      · exfalso
        apply hpad
        have hround := EthLib.Base.natToBytes_bytesToNat (padded.take 16)
        rw [hhigh, h] at hround
        rw [← hround]
        decide
      · exact h
    simp only [unpadFp, PAD_BYTES, hpad, ↓reduceIte, bind, Except.bind, Except.toOption, Option.isSome_none,
      Bool.false_eq_true, false_iff, Nat.not_lt]
    rw [hsplit, hlow]
    calc Fp.modulus ≤ 256 ^ 48 := Nat.le_of_lt hmodulus
      _ ≤ bytesToNat (padded.take 16) * 256 ^ 48 := Nat.le_mul_of_pos_left _ hpos
      _ ≤ _ := Nat.le_add_right _ _

/-! ## Field elements -/

/-- The 48 bytes of a field element decode back to it. -/
theorem bytesToFieldElement_natToBytes (x : Fp) :
    bytesToFieldElement (natToBytes 48 x.val) = .ok x := by
  have hlt : x.val < 256 ^ 48 := Nat.lt_trans x.isLt (by decide)
  simp [bytesToFieldElement, EthLib.Base.bytesToNat_natToBytes_of_lt hlt, x.isLt]

/-- A padded field element decodes back to it. -/
theorem unpadFp_bytesToFieldElement_pad (x : Fp) :
    (unpadFp (zeroPad ++ natToBytes 48 x.val) >>= bytesToFieldElement) = .ok x := by
  simp only [unpadFp_pad, bind, Except.bind, bytesToFieldElement_natToBytes]

/-- A decoded field element encodes back to the 48 bytes it came from. -/
theorem natToBytes_bytesToFieldElement {raw : List UInt8} (hlength : raw.length = 48) {x : Fp}
    (h : bytesToFieldElement raw = .ok x) : natToBytes 48 x.val = raw := by
  simp only [bytesToFieldElement] at h
  split at h
  · cases h
    rw [← hlength]
    exact EthLib.Base.natToBytes_bytesToNat raw
  · cases h

/-- The 96 bytes of an element of `Fp2` decode back to it, `c0` first. -/
theorem bytesToFq2_natToBytes (a : Fp2) :
    bytesToFq2 (natToBytes 48 a.c0.val ++ natToBytes 48 a.c1.val) = .ok a := by
  have hlen := EthLib.Base.natToBytes_length 48 a.c0.val
  simp [bytesToFq2, List.take_left' hlen, List.drop_left' hlen, bytesToFieldElement_natToBytes,
    bind, Except.bind, pure, Except.pure]

/-- A decoded element of `Fp2` encodes back to the 96 bytes it came from. -/
theorem natToBytes_bytesToFq2 {raw : List UInt8} (hlength : raw.length = 96) {a : Fp2}
    (h : bytesToFq2 raw = .ok a) : natToBytes 48 a.c0.val ++ natToBytes 48 a.c1.val = raw := by
  simp only [bytesToFq2, bind, Except.bind, pure, Except.pure] at h
  cases h0 : bytesToFieldElement (raw.take 48) with
  | error => simp [h0] at h
  | ok c0 =>
    cases h1 : bytesToFieldElement (raw.drop 48) with
    | error => simp [h0, h1] at h
    | ok c1 =>
      simp only [h0, h1, Except.ok.injEq] at h
      subst h
      rw [natToBytes_bytesToFieldElement (by simp [hlength]) h0,
        natToBytes_bytesToFieldElement (by simp [hlength]) h1, List.take_append_drop]

/-! ## G1 points -/

/-- A power of one is one. -/
private theorem one_powNat (e : Nat) : Fp.powNat Fp.one e = Fp.one := by
  induction e using Nat.strongRecOn with
  | _ e ih =>
    rw [Fp.powNat]
    split
    · rfl
    · have hone : Fp.one * Fp.one = Fp.one := by decide
      rw [hone, ih (e / 2) (by omega)]
      split <;> first | rfl | exact hone

/-- The affine form of a point with `z = 1` is its `x` and `y`. -/
theorem g1_toAffine_one (x y : Fp) : G1.toAffine ⟨x, y, Fp.one⟩ = (x, y) := by
  have hinv : Fp.one.inverse = Fp.one := one_powNat _
  have hz : Fp.one.isZero = false := by decide
  simp only [G1.toAffine, hz, hinv, Bool.false_eq_true, ↓reduceIte]
  have hone : Fp.one * Fp.one = Fp.one := by decide
  rw [hone, hone]
  exact Prod.ext (Fin.mul_one x) (Fin.mul_one y)

/-- The point at infinity encodes as 96 zero bytes. -/
theorem g1ToBytes_of_isZero {p : G1} (h : p.z.isZero = true) :
    g1ToBytes p = List.replicate 96 0 := by
  simp only [g1ToBytes, G1.toAffine, h, ↓reduceIte]
  rfl

-- The kernel reads 96 bytes one by one, deeper than the default recursion limit.
set_option maxRecDepth 4000 in
/-- 96 zero bytes decode as the point at infinity. -/
theorem bytesToG1_zeros (subgroupCheck : Bool) :
    bytesToG1 (List.replicate 96 0) subgroupCheck = .ok G1.zero := by
  cases subgroupCheck <;> rfl

/-- An affine point on the curve decodes back to itself, with `z = 1`.

With the subgroup check, the point must also be in the subgroup. -/
theorem bytesToG1_affine {x y : Fp} (hon : onCurveG1 x y = true) {subgroupCheck : Bool}
    (hsub : subgroupCheck = true → G1.inSubgroup ⟨x, y, Fp.one⟩ = true) :
    bytesToG1 (natToBytes 48 x.val ++ natToBytes 48 y.val) subgroupCheck = .ok ⟨x, y, Fp.one⟩ := by
  -- `(0, 0)` is not on the curve, so the point is not read as the point at infinity.
  have hne : ¬(x.val = 0 ∧ y.val = 0) := by
    rintro ⟨hx, hy⟩
    have hx' : x = 0 := Fin.ext hx
    have hy' : y = 0 := Fin.ext hy
    subst hx' hy'
    exact absurd hon (by decide)
  have hlen := EthLib.Base.natToBytes_length 48 x.val
  simp only [bytesToG1, List.take_left' hlen, List.drop_left' hlen, bytesToFieldElement_natToBytes,
    bind, Except.bind, pure, Except.pure, hne, hon, ↓reduceIte, Bool.not_true, throw, throwThe,
    MonadExceptOf.throw]
  cases subgroupCheck with
  | false => rfl
  | true => simp [hsub rfl]

/-- A decoded point encodes back to the 96 bytes it came from: the encoding is canonical. -/
theorem g1ToBytes_bytesToG1 {raw : List UInt8} (hlength : raw.length = 96) {subgroupCheck : Bool}
    {p : G1} (h : bytesToG1 raw subgroupCheck = .ok p) : g1ToBytes p = raw := by
  simp only [bytesToG1, bind, Except.bind, pure, Except.pure, throw, throwThe,
    MonadExceptOf.throw] at h
  cases hx : bytesToFieldElement (raw.take 48) with
  | error => simp [hx] at h
  | ok x =>
    cases hy : bytesToFieldElement (raw.drop 48) with
    | error => simp [hx, hy] at h
    | ok y =>
      have hxb := natToBytes_bytesToFieldElement (by simp [hlength]) hx
      have hyb := natToBytes_bytesToFieldElement (by simp [hlength]) hy
      simp only [hx, hy] at h
      split at h
      · -- Both coordinates are zero: the point at infinity, and the bytes are all zero.
        rename_i hzero
        cases h
        rw [g1ToBytes_of_isZero (by decide), ← List.take_append_drop 48 raw, ← hxb, ← hyb]
        have hx0 : x = 0 := Fin.ext hzero.1
        have hy0 : y = 0 := Fin.ext hzero.2
        subst hx0 hy0
        rfl
      · split at h
        · cases h
        · split at h
          · cases h
          · cases h
            simp only [g1ToBytes, g1_toAffine_one]
            rw [hxb, hyb, List.take_append_drop]

/-! ## G2 points -/

-- The kernel compares 192 bytes one by one, deeper than the default recursion limit.
set_option maxRecDepth 8000 in
/-- The point at infinity encodes as 192 zero bytes. -/
theorem g2ToBytes_of_isZero {p : G2} (h : p.z.isZero = true) :
    g2ToBytes p = List.replicate 192 0 := by
  simp only [g2ToBytes, G2.toAffine, h, ↓reduceIte]
  rfl

-- The kernel reads 192 bytes one by one, deeper than the default recursion limit.
set_option maxRecDepth 8000 in
/-- 192 zero bytes decode as the point at infinity. -/
theorem bytesToG2_zeros (subgroupCheck : Bool) :
    bytesToG2 (List.replicate 192 0) subgroupCheck = .ok G2.zero := by
  cases subgroupCheck <;> rfl

/-- An affine point on the twist decodes back to itself, with `z = 1`.

With the subgroup check, the point must also be in the subgroup. -/
theorem bytesToG2_affine {x y : Fp2} (hon : onCurveG2 x y = true) {subgroupCheck : Bool}
    (hsub : subgroupCheck = true → G2.inSubgroup ⟨x, y, Fp2.one⟩ = true) :
    bytesToG2 ((natToBytes 48 x.c0.val ++ natToBytes 48 x.c1.val) ++
      (natToBytes 48 y.c0.val ++ natToBytes 48 y.c1.val)) subgroupCheck = .ok ⟨x, y, Fp2.one⟩ := by
  -- `(0, 0)` is not on the twist, so the point is not read as the point at infinity.
  have hne : ¬(x.c0.val = 0 ∧ x.c1.val = 0 ∧ y.c0.val = 0 ∧ y.c1.val = 0) := by
    rintro ⟨h0, h1, h2, h3⟩
    have hx : x = ⟨0, 0⟩ := by cases x; simp only [Fp2.mk.injEq]; exact ⟨Fin.ext h0, Fin.ext h1⟩
    have hy : y = ⟨0, 0⟩ := by cases y; simp only [Fp2.mk.injEq]; exact ⟨Fin.ext h2, Fin.ext h3⟩
    subst hx hy
    exact absurd hon (by decide)
  have hlen : (natToBytes 48 x.c0.val ++ natToBytes 48 x.c1.val).length = 96 := by
    simp [EthLib.Base.natToBytes_length]
  simp only [bytesToG2, List.take_left' hlen, List.drop_left' hlen, bytesToFq2_natToBytes,
    bind, Except.bind, pure, Except.pure, hne, hon, ↓reduceIte, Bool.not_true, throw, throwThe,
    MonadExceptOf.throw]
  cases subgroupCheck with
  | false => rfl
  | true => simp [hsub rfl]

/-! ## Results -/

/-- A chain of steps that succeeds succeeded at its first step. -/
theorem bind_eq_ok {α β : Type} {x : Except Bls12381Error α} {f : α → Except Bls12381Error β} {y : β}
    (h : x >>= f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-! ## Known answers through bytes -/

/-- A result that the kernel computes as the bytes `out` is `.ok out`. -/
theorem eq_ok_of_kernel {result : Except Bls12381Error ByteArray} {out : ByteArray}
    (h : (result.toOption.map fun bytes => bytes.data.toList) = some out.data.toList) : result = .ok out := by
  cases result with
  | error => simp [Except.toOption] at h
  | ok bytes =>
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at h
    cases bytes; cases out
    simp_all

/-- The error of a result, or `none` when it succeeds. -/
def errorOf (result : Except Bls12381Error ByteArray) : Option Bls12381Error :=
  match result with
  | .error e => some e
  | .ok _ => none

/-- A result whose error the kernel computes as `e` is `.error e`. -/
theorem eq_error_of_kernel {result : Except Bls12381Error ByteArray} {e : Bls12381Error}
    (h : errorOf result = some e) : result = .error e := by
  cases result <;> simp_all [errorOf]

end EthLib.Execution.Evm.Precompiles.Bls12381
