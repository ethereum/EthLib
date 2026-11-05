module

public import EthLib.Cryptography.Bls.G1
public import EthLib.Cryptography.Bls.G2
public import EthLib.Cryptography.Proofs.Bls.BaseFieldMap

/-!
# Proofs: the BLS12-381 curves under a map of base fields

A map of base fields acts on each coordinate of a point of `G1` or `G2`.

When it respects the operations of the base fields, it commutes with each curve operation.

So a computation on one base field gives the same point on the other, once mapped.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls

open EthLib.Cryptography.BaseField (Hom)

variable {F G : Type} [BaseField F] [BaseField G]

namespace G1

/-- The map of base fields, applied to the three coordinates. -/
def map (f : Hom F G) (p : G1 F) : G1 G := ⟨f p.x, f p.y, f p.z⟩

@[simp] private theorem map_x (f : Hom F G) (p : G1 F) : (map f p).x = f p.x := rfl
@[simp] private theorem map_y (f : Hom F G) (p : G1 F) : (map f p).y = f p.y := rfl
@[simp] private theorem map_z (f : Hom F G) (p : G1 F) : (map f p).z = f p.z := rfl

private theorem map_mk (f : Hom F G) (x y z : F) : map f ⟨x, y, z⟩ = ⟨f x, f y, f z⟩ := rfl

theorem map_generator (f : Hom F G) : map f generator = generator := by
  simp only [map, generator, f.map_ofNat, f.map_one]

theorem map_zero (f : Hom F G) : map f zero = zero := by
  simp only [map, zero, f.map_zero, f.map_one]

theorem map_isInfinity (f : Hom F G) (p : G1 F) : (map f p).isInfinity = p.isInfinity := by
  simp only [map, isInfinity, f.map_isZero]

theorem map_double (f : Hom F G) (p : G1 F) : map f p.double = (map f p).double := by
  unfold double map
  simp only [f.map_isZero]
  cases BaseField.isZero p.z
  · simp only [Bool.false_eq_true, ↓reduceIte, f.map_add, f.map_sub, f.map_mul]
  · simp only [↓reduceIte]

theorem map_neg (f : Hom F G) (p : G1 F) : map f (-p) = -map f p := by
  show map f (neg p) = neg (map f p)
  simp only [map, neg, f.map_neg]

theorem map_addGeneral (f : Hom F G) (p q : G1 F) :
    map f (addGeneral p q) = addGeneral (map f p) (map f q) := by
  unfold addGeneral
  simp only [apply_ite (map f), map_double, map_zero, map_mk, map_x, map_y, map_z,
    ← f.map_mul, ← f.map_add, ← f.map_sub, f.map_beq]

theorem map_addMixed (f : Hom F G) (p q : G1 F) :
    map f (addMixed p q) = addMixed (map f p) (map f q) := by
  unfold addMixed
  simp only [apply_ite (map f), map_double, map_zero, map_mk, map_x, map_y, map_z,
    ← f.map_mul, ← f.map_add, ← f.map_sub, f.map_beq]

theorem map_add (f : Hom F G) (p q : G1 F) : map f (p + q) = map f p + map f q := by
  show map f (add p q) = add (map f p) (map f q)
  unfold add
  simp only [apply_ite (map f), map_addMixed, map_addGeneral, map_z, f.map_isZero,
    ← f.map_one, f.map_beq]

private theorem map_add' (f : Hom F G) (p q : G1 F) :
    map f (add p q) = add (map f p) (map f q) :=
  map_add f p q

theorem map_toAffine (f : Hom F G) (p : G1 F) :
    Prod.map f f p.toAffine = (map f p).toAffine := by
  unfold toAffine
  simp only [map, f.map_isZero]
  split
  · simp only [Prod.map, f.map_zero]
  · simp only [Prod.map, f.map_mul, f.map_inverse]

theorem map_mulNat (f : Hom F G) (p : G1 F) (k : Nat) :
    map f (mulNat p k) = mulNat (map f p) k := by
  induction k using Nat.strongRecOn generalizing p with
  | _ k ih =>
    rw [mulNat.eq_1 p k, mulNat.eq_1 (map f p) k]
    split
    · exact map_zero f
    · have h := ih (k / 2) (by omega) p.double
      rw [map_double] at h
      dsimp only
      split
      · rw [← h]
        exact map_add f p _
      · exact h

theorem map_mul (f : Hom F G) (p : G1 F) (s : Fr) : map f (p.mul s) = (map f p).mul s :=
  map_mulNat f p s.val

/-! ### Multi-scalar multiplication

The buckets are arrays of points, and a read out of bounds gives the default point.

So these lemmas assume that the map sends the default point to the default point. -/

theorem map_msmCombine (f : Hom F G) (nW : Nat) (acc : G1 F) (kk : Nat) (S : G1 F) :
    map f (msmCombine nW acc kk S) = msmCombine nW (map f acc) kk (map f S) := by
  unfold msmCombine
  split
  · refine (map_add f _ _).trans ?_
    rw [← List.foldl_hom (map f) (g₁ := fun a (_ : Nat) => double a)
      (g₂ := fun a (_ : Nat) => double a) fun a _ => (map_double f a).symm]
    rfl
  · exact map_add f _ _

section Buckets

variable [Inhabited F] [Inhabited G]

private theorem map_getElem! (f : Hom F G) (hd : map f default = default) (bs : Array (G1 F))
    (i : Nat) : map f bs[i]! = (bs.map (map f))[i]! := by
  by_cases h : i < bs.size
  · rw [getElem!_pos bs i h, getElem!_pos (bs.map (map f)) i (by simpa using h),
      Array.getElem_map]
  · rw [getElem!_neg bs i h, getElem!_neg (bs.map (map f)) i (by simpa using h), hd]

theorem map_msmBuckets (f : Hom F G) (hd : map f default = default) (points : Array (G1 F))
    (vals : Array Nat) (n k : Nat) :
    (msmBuckets points vals n k).map (map f) = msmBuckets (points.map (map f)) vals n k := by
  unfold msmBuckets
  rw [show Array.replicate (1 <<< 8) (zero : G1 G) = (Array.replicate (1 <<< 8) zero).map (map f)
    by rw [Array.map_replicate, map_zero]]
  refine (List.foldl_hom (Array.map (map f)) fun bs j => ?_).symm
  by_cases hc : windowVal vals[j]! k ≠ 0
  · rw [ite_eq_left hc, ite_eq_left hc, Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds,
      Array.map_setIfInBounds, ← map_getElem! f hd, ← map_getElem! f hd]
    exact congrArg _ (map_add f _ _).symm
  · rw [ite_eq_right hc, ite_eq_right hc]

theorem map_msmRunning (f : Hom F G) (hd : map f default = default) (bs : Array (G1 F)) :
    msmRunning (bs.map (map f)) = ⟨map f (msmRunning bs).1, map f (msmRunning bs).2⟩ := by
  unfold msmRunning
  rw [show (⟨zero, zero⟩ : MProd (G1 G) (G1 G)) = ⟨map f zero, map f zero⟩ by rw [map_zero]]
  refine List.foldl_hom (init := (⟨zero, zero⟩ : MProd (G1 F) (G1 F)))
    (fun rp : MProd (G1 F) (G1 F) => (⟨map f rp.1, map f rp.2⟩ : MProd (G1 G) (G1 G)))
    fun rp vv => ?_
  rw [← map_getElem! f hd]
  simp only [map_add']

/-- A fold over a list zipped with its own image, read through a map of the state. -/
private theorem foldl_zip_hom {α β₁ β₂ γ₁ γ₂ : Type} (g : γ₁ → γ₂) (ws : List α)
    (t₁ : α → β₁) (t₂ : α → β₂) (s₁ : γ₁ → α × β₁ → γ₁) (s₂ : γ₂ → α × β₂ → γ₂) (a : γ₁)
    (H : ∀ a w, g (s₁ a (w, t₁ w)) = s₂ (g a) (w, t₂ w)) :
    g ((ws.zip (ws.map t₁)).foldl s₁ a) = (ws.zip (ws.map t₂)).foldl s₂ (g a) := by
  induction ws generalizing a with
  | nil => rfl
  | cons w ws ih => simp only [List.map_cons, List.zip_cons_cons, List.foldl_cons, ih, H]

theorem map_msm (f : Hom F G) (hd : map f default = default) (points : Array (G1 F))
    (scalars : Array Fr) : map f (msm points scalars) = msm (points.map (map f)) scalars := by
  rw [msm, msm, Array.size_map]
  dsimp only
  generalize (if points.size ≤ scalars.size then points.size else scalars.size) = n
  by_cases h0 : n = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    exact map_zero f
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases h1 : msmMaxBits (scalars.map Fr.val) n = 0
  · rw [ite_eq_left h1, ite_eq_left h1]
    exact map_zero f
  rw [ite_eq_right h1, ite_eq_right h1]
  show map f (List.foldl _ zero _) = List.foldl _ zero _
  rw [← map_zero f]
  refine foldl_zip_hom (map f) _ _ _ _ _ _ fun a w => ?_
  rw [map_msmCombine]
  congr 1
  simp only [Task.spawn]
  rw [← map_msmBuckets f hd, map_msmRunning f hd]

end Buckets

end G1

namespace G2

/-- The map of base fields, applied to the three coordinates in `Fp2`. -/
def map (f : Hom F G) (p : G2 F) : G2 G := ⟨p.x.map f, p.y.map f, p.z.map f⟩

@[simp] private theorem map_x (f : Hom F G) (p : G2 F) : (map f p).x = p.x.map f := rfl
@[simp] private theorem map_y (f : Hom F G) (p : G2 F) : (map f p).y = p.y.map f := rfl
@[simp] private theorem map_z (f : Hom F G) (p : G2 F) : (map f p).z = p.z.map f := rfl

private theorem map_mk (f : Hom F G) (x y z : Fp2 F) :
    map f ⟨x, y, z⟩ = ⟨x.map f, y.map f, z.map f⟩ := rfl

theorem map_generator (f : Hom F G) : map f generator = generator := by
  simp only [map, generator, Fp2.map_one]
  simp only [Fp2.map, f.map_ofNat]

theorem map_zero (f : Hom F G) : map f zero = zero := by
  simp only [map, zero, Fp2.map_zero, Fp2.map_one]

theorem map_isInfinity (f : Hom F G) (p : G2 F) : (map f p).isInfinity = p.isInfinity := by
  simp only [map, isInfinity, Fp2.map_isZero]

theorem map_bTwist (f : Hom F G) : (bTwist : Fp2 F).map f = bTwist := by
  simp only [bTwist, Fp2.map, f.map_ofNat]

theorem map_double (f : Hom F G) (p : G2 F) : map f p.double = (map f p).double := by
  unfold double
  simp only [apply_ite (map f), map_mk, map_x, map_y, map_z, Fp2.map_isZero,
    ← Fp2.map_mul, ← Fp2.map_add, ← Fp2.map_sub, ← f.map_ofNat, ← Fp2.map_ofFp]

theorem map_neg (f : Hom F G) (p : G2 F) : map f (-p) = -map f p := by
  show map f (neg p) = neg (map f p)
  simp only [map, neg, Fp2.map_neg]

theorem map_add (f : Hom F G) (p q : G2 F) : map f (p + q) = map f p + map f q := by
  show map f (add p q) = add (map f p) (map f q)
  unfold add
  simp only [apply_ite (map f), map_double, map_zero, map_mk, map_x, map_y, map_z,
    Fp2.map_isZero, ← Fp2.map_mul, ← Fp2.map_add, ← Fp2.map_sub, ← f.map_ofNat,
    ← Fp2.map_ofFp, Fp2.map_beq]

theorem map_toAffine (f : Hom F G) (p : G2 F) :
    Prod.map (Fp2.map f) (Fp2.map f) p.toAffine = (map f p).toAffine := by
  unfold toAffine
  simp only [map, Fp2.map_isZero]
  split
  · simp only [Prod.map, Fp2.map_zero]
  · simp only [Prod.map, Fp2.map_mul, Fp2.map_inverse]

theorem map_mulNat (f : Hom F G) (p : G2 F) (k : Nat) :
    map f (mulNat p k) = mulNat (map f p) k := by
  induction k using Nat.strongRecOn generalizing p with
  | _ k ih =>
    rw [mulNat.eq_1 p k, mulNat.eq_1 (map f p) k]
    split
    · exact map_zero f
    · have h := ih (k / 2) (by omega) p.double
      rw [map_double] at h
      dsimp only
      split
      · rw [← h]
        exact map_add f p _
      · exact h

theorem map_mul (f : Hom F G) (p : G2 F) (s : Fr) : map f (p.mul s) = (map f p).mul s :=
  map_mulNat f p s.val

end G2

end EthLib.Cryptography.Bls
