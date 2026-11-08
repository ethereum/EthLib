module

public import EthLib.Cryptography.Proofs.Bls.G1Order
public import EthLib.Cryptography.Proofs.IdLoops

/-!
# Proofs: the Pippenger multi-scalar multiplication computes `Σ [s_i] P_i`

The proof has two layers.

- The multi-scalar multiplication equals a plain fold, its model.
  Its window sums run as tasks, and reading a task gives its value by definition.
- The model computes `Σ i < n, [scalars[i]] points[i]` in the curve group.
  The proof uses the bucket partition, the running sums, and the base-`2^w` digits of the scalars.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.G1

open EthLib.Cryptography.IdLoops

set_option maxRecDepth 4000

/-! ## The pure model of `msm` -/

/-- One window step of the multi-scalar multiplication, with the window sum computed in place. -/
def msmWindowStep {n nW : Nat} (pts : Vector G1 n) (digits : Vector (Vector (Fin 256) nW) n)
    (acc : G1) (kk : Fin nW) : G1 :=
  msmCombine nW acc kk.val (msmRunning (msmBuckets pts digits kk.rev)).1

/-- The pure model of the multi-scalar multiplication, on vectors of `n` points and values. -/
def msmVecModel {n : Nat} (pts : Vector G1 n) (vals : Vector Nat n) : G1 :=
  if n = 0 then zero
  else if msmMaxBits vals = 0 then zero
  else
    (List.finRange ((msmMaxBits vals + 8 - 1) / 8)).foldl
      (msmWindowStep pts (vals.map (msmDigits ((msmMaxBits vals + 8 - 1) / 8)))) zero

/-- The pure model of `G1.msm`. -/
def msmModel (points : Array G1) (scalars : Array Fr) : G1 :=
  msmVecModel (n := min points.size scalars.size)
    (Vector.ofFn fun j => points[j.val]'(Nat.lt_of_lt_of_le j.isLt (Nat.min_le_left _ _)))
    (Vector.ofFn fun j =>
      (scalars[j.val]'(Nat.lt_of_lt_of_le j.isLt (Nat.min_le_right _ _))).val)

/-! ## `msm` equals its model (mechanical layer) -/

/-- Reading a spawned task gives its value, so the fold over tasks is the fold over values. -/
private theorem foldl_zip_spawn {α : Type} (l : List α) (F : G1 → α → G1 → G1) (G : α → G1)
    (init : G1) :
    (l.zip (l.map fun x => Task.spawn fun _ => G x)).foldl (fun acc w => F acc w.1 w.2.get) init =
      l.foldl (fun acc x => F acc x (G x)) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih => exact ih (F init x (G x))

/-- `msm` computes its model's coordinates: its tasks hold exactly the model's window sums. -/
theorem msm_eq_msmModel (points : Array G1) (scalars : Array Fr) :
    msm points scalars = msmModel points scalars := by
  unfold msm msmModel msmVecModel
  dsimp only
  split_ifs
  · rfl
  · rfl
  · show List.foldl _ zero _ = _
    exact foldl_zip_spawn (List.finRange _) (fun acc kk S => msmCombine _ acc kk.val S)
      (fun kk => (msmRunning (msmBuckets _ _ kk.rev)).1) zero

/-! ## The math layer: `msmModel` computes `Σ [sᵢ]Pᵢ` -/

open Finset

/-- The `maxBits` fold function, named for the induction proofs. -/
private def maxBitsF {n : Nat} (vals : Vector Nat n) (m : Nat) (j : Fin n) : Nat :=
  if vals[j.val] ≠ 0 then
    if vals[j.val].log2 + 1 > m then vals[j.val].log2 + 1 else m
  else m

private theorem msmMaxBits_eq_foldl {n : Nat} (vals : Vector Nat n) :
    msmMaxBits vals = (List.finRange n).foldl (maxBitsF vals) 0 := rfl

private theorem maxBitsF_le {n : Nat} (vals : Vector Nat n) (l : List (Fin n)) :
    ∀ init, init ≤ l.foldl (maxBitsF vals) init := by
  induction l with
  | nil => exact fun _ => Nat.le_refl _
  | cons a l ih =>
    intro init
    refine Nat.le_trans ?_ (ih (maxBitsF vals init a))
    rw [maxBitsF]
    split
    · split
      · exact Nat.le_of_lt (by assumption)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private theorem maxBitsF_bound {n : Nat} (vals : Vector Nat n) (l : List (Fin n)) :
    ∀ init (j : Fin n), j ∈ l → vals[j.val] < 2 ^ (l.foldl (maxBitsF vals) init) := by
  induction l with
  | nil => exact fun _ j hj => absurd hj (List.not_mem_nil)
  | cons a l ih =>
    intro init j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · -- the head: the fold is at least `log2 + 1` (or the value is 0)
      by_cases h0 : vals[j.val] = 0
      · rw [h0]
        exact Nat.two_pow_pos _
      · have hstep : vals[j.val].log2 + 1 ≤ maxBitsF vals init j := by
          rw [maxBitsF, ite_eq_left h0]
          split
          · exact Nat.le_refl _
          · omega
        have hle := Nat.le_trans hstep (maxBitsF_le vals l _)
        calc vals[j.val] < 2 ^ (vals[j.val].log2 + 1) :=
              Nat.lt_log2_self
          _ ≤ 2 ^ (List.foldl (maxBitsF vals) (maxBitsF vals init j) l) :=
              Nat.pow_le_pow_right (by omega) hle
    · exact ih (maxBitsF vals init a) j hj

/-- Every scalar value is below `2 ^ msmMaxBits`. -/
private theorem msmMaxBits_bound {n : Nat} (vals : Vector Nat n) :
    ∀ j (hj : j < n), vals[j] < 2 ^ msmMaxBits vals := by
  intro j hj
  rw [msmMaxBits_eq_foldl]
  exact maxBitsF_bound vals (List.finRange n) 0 ⟨j, hj⟩ (List.mem_finRange _)

/-- The base-`2⁸` digit decomposition that drives the window recomposition.

Shifting eight fewer bits is `256·(shift) + window`. -/
private theorem shift_window (s a : Nat) :
    s >>> a = (1 <<< 8) * (s >>> (a + 8)) + ((s >>> a) &&& (1 <<< 8 - 1)) := by
  rw [Nat.shiftRight_add, show ((1 : Nat) <<< 8 - 1) = 2 ^ 8 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow (s >>> a) 8,
      show ((1 : Nat) <<< 8) = 2 ^ 8 from rfl]
  omega

/-- Iterated doubling is multiplication by `2^m` in the group. -/
private theorem doubleFold_spec {a : G1} (h : Valid a) (m : Nat) :
    Valid ((List.range' 0 m).foldl (fun x _ => double x) a)
    ∧ toPoint ((List.range' 0 m).foldl (fun x _ => double x) a)
        = 2 ^ m • toPoint a := by
  induction m with
  | zero => exact ⟨h, by rw [pow_zero, one_nsmul]; rfl⟩
  | succ m ih =>
    rw [List.range'_1_concat, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    refine ⟨valid_double ih.1, ?_⟩
    rw [toPoint_double ih.1, ih.2, ← two_nsmul, ← mul_nsmul', ← pow_succ']

/-- One step of the bucket fold: the point goes to the bucket of its digit, unless that is 0. -/
private def bucketStep {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (k : Fin nW) (bs : Vector G1 256) (j : Fin n) :
    Vector G1 256 :=
  if (digits[j.val][k.val]).val ≠ 0 then
    bs.set (digits[j.val][k.val]).val (add bs[(digits[j.val][k.val]).val] pts[j.val])
  else bs

private theorem msmBuckets_eq_foldl {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (k : Fin nW) :
    msmBuckets pts digits k
      = (List.finRange n).foldl (bucketStep pts digits k) (Vector.replicate 256 zero) := rfl

/-- The bucket fold over any list of indices: validity, and what each nonzero bucket gains. -/
private theorem bucketFold_spec {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (k : Fin nW)
    (hval : ∀ j (hj : j < n), Valid pts[j]) (l : List (Fin n)) :
    ∀ bs : Vector G1 256, (∀ v (hv : v < 256), Valid bs[v]) →
      (∀ v (hv : v < 256), Valid (l.foldl (bucketStep pts digits k) bs)[v])
      ∧ ∀ v (hv : v < 256), v ≠ 0 →
        toPoint (l.foldl (bucketStep pts digits k) bs)[v]
          = toPoint bs[v] + (l.map fun j =>
              if (digits[j.val][k.val]).val = v then toPoint pts[j.val] else 0).sum := by
  induction l with
  | nil =>
    intro bs hbs
    refine ⟨hbs, fun v hv _ => ?_⟩
    rw [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
  | cons j l ih =>
    intro bs hbs
    -- The one step on `bs`.
    have hstep : (∀ v (hv : v < 256), Valid (bucketStep pts digits k bs j)[v])
        ∧ ∀ v (hv : v < 256), v ≠ 0 →
          toPoint (bucketStep pts digits k bs j)[v]
            = toPoint bs[v]
              + if (digits[j.val][k.val]).val = v then toPoint pts[j.val] else 0 := by
      unfold bucketStep
      by_cases hd : (digits[j.val][k.val]).val ≠ 0
      · rw [ite_eq_left hd]
        refine ⟨fun v hv => ?_, fun v hv _ => ?_⟩
        · by_cases hdv : (digits[j.val][k.val]).val = v
          · rw [Vector.getElem_set, ite_eq_left hdv]
            exact valid_add (hbs _ _) (hval _ _)
          · rw [Vector.getElem_set_ne _ _ hdv]
            exact hbs v hv
        · by_cases hdv : (digits[j.val][k.val]).val = v
          · rw [Vector.getElem_set, ite_eq_left hdv, ite_eq_left hdv,
              toPoint_add (hbs _ _) (hval _ _)]
            simp only [hdv]
          · rw [Vector.getElem_set_ne _ _ hdv, ite_eq_right hdv, add_zero]
      · rw [ite_eq_right hd]
        refine ⟨hbs, fun v hv hv0 => ?_⟩
        rw [ite_eq_right (fun h => hv0 (by rw [← h]; exact not_ne_iff.mp hd)), add_zero]
    obtain ⟨ihv, ihp⟩ := ih (bucketStep pts digits k bs j) hstep.1
    refine ⟨ihv, fun v hv hv0 => ?_⟩
    rw [List.foldl_cons, ihp v hv hv0, hstep.2 v hv hv0, List.map_cons, List.sum_cons, add_assoc]

/-- The buckets of a window: all valid, and bucket `v > 0` sums the points whose digit is `v`. -/
private theorem msmBuckets_spec {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (k : Fin nW)
    (hval : ∀ j (hj : j < n), Valid pts[j]) :
    (∀ v (hv : v < 256), Valid (msmBuckets pts digits k)[v])
    ∧ ∀ v (hv : v < 256), v ≠ 0 →
      toPoint (msmBuckets pts digits k)[v]
        = ∑ j : Fin n, if (digits[j.val][k.val]).val = v then toPoint pts[j.val] else 0 := by
  have hz : ∀ v (hv : v < 256), Valid (Vector.replicate 256 (zero : G1))[v] := fun v hv => by
    rw [Vector.getElem_replicate]
    exact valid_zero
  obtain ⟨hv, hp⟩ := bucketFold_spec pts digits k hval (List.finRange n) _ hz
  refine ⟨fun v hv' => by rw [msmBuckets_eq_foldl]; exact hv v hv', fun v hv' hv0 => ?_⟩
  rw [msmBuckets_eq_foldl, hp v hv' hv0, Vector.getElem_replicate, toPoint_zero, zero_add,
    Fin.sum_univ_def]

/-- The prefix of the running-sum fold, on a total read of the buckets. -/
private def msmRunningT (b : Nat → G1) (t : Nat) : MProd G1 G1 :=
  (List.range t).foldl (fun rp vv =>
    ⟨add rp.1 (add rp.2 (b (255 - vv))), add rp.2 (b (255 - vv))⟩) ⟨zero, zero⟩

/-- Bucket `v`, read as `zero` past the last bucket. -/
private def bucketAt (bs : Vector G1 256) (v : Nat) : G1 :=
  if h : v < 256 then bs[v] else zero

private theorem msmRunning_eq_T (bs : Vector G1 256) :
    msmRunning bs = msmRunningT (bucketAt bs) 255 := by
  unfold msmRunning msmRunningT
  rw [← List.map_coe_finRange_eq_range, List.foldl_map]
  congr 1
  funext rp vv
  rw [bucketAt, dite_eq_left (by omega)]

/-- The running-sum invariant.

After `t` iterations the second component is the plain suffix sum and the first the weighted one.
-/
private theorem msmRunningT_spec (b : Nat → G1) (hval : ∀ v, v < 256 → Valid (b v)) :
    ∀ t, t ≤ 255 →
      Valid (msmRunningT b t).1 ∧ Valid (msmRunningT b t).2
      ∧ toPoint (msmRunningT b t).2 = ∑ v ∈ Ico (256 - t) 256, toPoint (b v)
      ∧ toPoint (msmRunningT b t).1
          = ∑ v ∈ Ico (256 - t) 256, (v - (255 - t)) • toPoint (b v) := by
  intro t
  induction t with
  | zero =>
    intro _
    have hico : Ico (256 - 0) 256 = ∅ := by
      rw [Nat.sub_zero]
      exact Finset.Ico_self _
    rw [show msmRunningT b 0 = ⟨zero, zero⟩ from rfl]
    refine ⟨valid_zero, valid_zero, ?_, ?_⟩ <;>
      rw [hico, Finset.sum_empty] <;> exact toPoint_zero
  | succ t ih =>
    intro ht
    obtain ⟨ihv1, ihv2, ihr, ihp⟩ := ih (by omega)
    have hstep : msmRunningT b (t + 1)
        = ⟨add (msmRunningT b t).1 (add (msmRunningT b t).2 (b (255 - t))),
           add (msmRunningT b t).2 (b (255 - t))⟩ := by
      rw [msmRunningT, msmRunningT, List.range_succ, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
    have hvb : Valid (b (255 - t)) := hval _ (by omega)
    have hvr : Valid (add (msmRunningT b t).2 (b (255 - t))) := valid_add ihv2 hvb
    -- the new suffix sum (second component)
    have hr' : toPoint (add (msmRunningT b t).2 (b (255 - t)))
        = ∑ v ∈ Ico (256 - (t + 1)) 256, toPoint (b v) := by
      rw [toPoint_add ihv2 hvb, ihr,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 256 - (t + 1) < 256)
          (fun v => toPoint (b v)),
        show 256 - (t + 1) + 1 = 256 - t by omega,
        show 256 - (t + 1) = 255 - t from by omega]
      apply add_comm
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hstep]
      exact valid_add ihv1 hvr
    · rw [hstep]
      exact hvr
    · rw [hstep]
      exact hr'
    · rw [hstep]
      show toPoint (add (msmRunningT b t).1 _) = _
      rw [toPoint_add ihv1 hvr, ihp, hr']
      -- Σ (v − c)•b + Σ b = Σ (v − (c−1))•b over the extended interval
      rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : 256 - (t + 1) < 256)
          (fun v => (v - (255 - (t + 1))) • toPoint (b v)),
        show 256 - (t + 1) + 1 = 256 - t by omega,
        show 256 - (t + 1) - (255 - (t + 1)) = 1 by omega,
        one_nsmul]
      have hcongr : ∀ v ∈ Ico (256 - t) 256,
          (v - (255 - (t + 1))) • toPoint (b v)
            = (v - (255 - t)) • toPoint (b v) + toPoint (b v) := by
        intro v hv
        have hv' := Finset.mem_Ico.mp hv
        rw [show v - (255 - (t + 1)) = (v - (255 - t)) + 1 by omega, add_nsmul, one_nsmul]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib,
        Finset.sum_eq_sum_Ico_succ_bot (by omega : 256 - (t + 1) < 256)
          (fun v => toPoint (b v)),
        show 256 - (t + 1) + 1 = 256 - t by omega]
      apply add_left_comm

/-- The running-sum fold computes `Σ_v v·b_v` (first component). -/
private theorem msmRunning_spec (bs : Vector G1 256) (hval : ∀ v (hv : v < 256), Valid bs[v]) :
    Valid (msmRunning bs).1
    ∧ toPoint (msmRunning bs).1 = ∑ v ∈ range 256, v • toPoint (bucketAt bs v) := by
  have hb : ∀ v, v < 256 → Valid (bucketAt bs v) := fun v hv => by
    rw [bucketAt, dite_eq_left hv]
    exact hval v hv
  obtain ⟨hv1, _, _, hp⟩ := msmRunningT_spec (bucketAt bs) hb 255 (Nat.le_refl _)
  refine ⟨by rw [msmRunning_eq_T]; exact hv1, ?_⟩
  rw [msmRunning_eq_T, hp, show 256 - 255 = 1 from rfl, show 255 - 255 = 0 from rfl,
    Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : (0 : Nat) < 256)
      (fun v => v • toPoint (bucketAt bs v)),
    zero_nsmul, zero_add]
  exact Finset.sum_congr rfl fun v _ => by rw [Nat.sub_zero]

/-- Buckets and running sums compute the digit-weighted point sum of a window. -/
private theorem window_sum {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (k : Fin nW)
    (hval : ∀ j (hj : j < n), Valid pts[j]) :
    Valid (msmRunning (msmBuckets pts digits k)).1
    ∧ toPoint (msmRunning (msmBuckets pts digits k)).1
        = ∑ j : Fin n, (digits[j.val][k.val]).val • toPoint pts[j.val] := by
  obtain ⟨hbv, hbp⟩ := msmBuckets_spec pts digits k hval
  obtain ⟨hrv, hrs⟩ := msmRunning_spec _ hbv
  refine ⟨hrv, ?_⟩
  rw [hrs]
  have h1 : ∀ v ∈ range 256,
      v • toPoint (bucketAt (msmBuckets pts digits k) v)
        = ∑ j : Fin n, if (digits[j.val][k.val]).val = v then
            (digits[j.val][k.val]).val • toPoint pts[j.val] else 0 := by
    intro v hv
    have hv' := Finset.mem_range.mp hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [zero_nsmul]
      refine (Finset.sum_eq_zero fun j _ => ?_).symm
      by_cases hj : (digits[j.val][k.val]).val = 0
      · rw [ite_eq_left hj, hj, zero_nsmul]
      · rw [ite_eq_right hj]
    · rw [bucketAt, dite_eq_left hv', hbp v hv' hv0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : (digits[j.val][k.val]).val = v
      · rw [ite_eq_left hj, ite_eq_left hj, hj]
      · rw [ite_eq_right hj, ite_eq_right hj, nsmul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_range.mpr (digits[j.val][k.val]).isLt)]

/-- The sum of window `k`, read as `zero` past the last window. -/
private def windowSum {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (k : Nat) : G1 :=
  if h : k < nW then (msmRunning (msmBuckets pts digits ⟨k, h⟩)).1 else zero

/-- A window sum of the digits of the values is their window-weighted point sum. -/
private theorem windowSum_spec {n : Nat} (pts : Vector G1 n) (vals : Vector Nat n)
    (nW k : Nat) (hk : k < nW) (hval : ∀ j (hj : j < n), Valid pts[j]) :
    Valid (windowSum pts (vals.map (msmDigits nW)) k)
    ∧ toPoint (windowSum pts (vals.map (msmDigits nW)) k)
        = ∑ j : Fin n, windowVal vals[j.val] k • toPoint pts[j.val] := by
  rw [windowSum, dite_eq_left hk]
  obtain ⟨hv, hs⟩ := window_sum pts (vals.map (msmDigits nW)) ⟨k, hk⟩ hval
  refine ⟨hv, hs.trans (Finset.sum_congr rfl fun j _ => ?_)⟩
  rw [Vector.getElem_map, msmDigits, Vector.getElem_ofFn]

/-- Prefix of the outer window fold. -/
private def msmAcc {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) (t : Nat) : G1 :=
  (List.range t).foldl (fun acc kk => msmCombine nW acc kk (windowSum pts digits (nW - 1 - kk)))
    zero

private theorem foldl_msmWindowStep {n nW : Nat} (pts : Vector G1 n)
    (digits : Vector (Vector (Fin 256) nW) n) :
    (List.finRange nW).foldl (msmWindowStep pts digits) zero = msmAcc pts digits nW := by
  rw [msmAcc, ← List.map_coe_finRange_eq_range, List.foldl_map]
  refine congrArg (fun g => List.foldl g zero (List.finRange nW))
    (funext fun acc => funext fun kk => ?_)
  have hrev : kk.rev = ⟨nW - 1 - kk.val, by omega⟩ := Fin.ext (by simp only [Fin.val_rev]; omega)
  rw [msmWindowStep, windowSum, dite_eq_left (by omega), hrev]

/-- The window-recomposition invariant.

After `t` windows, the accumulator holds `Σ_j (sⱼ >>> ((nW − t)·8)) · Pⱼ`. -/
private theorem msmAcc_spec {n : Nat} (pts : Vector G1 n) (vals : Vector Nat n)
    (nW : Nat) (hval : ∀ j (hj : j < n), Valid pts[j])
    (hbound : ∀ j (hj : j < n), vals[j] < 2 ^ (nW * 8)) :
    ∀ t, t ≤ nW →
      Valid (msmAcc pts (vals.map (msmDigits nW)) t)
      ∧ toPoint (msmAcc pts (vals.map (msmDigits nW)) t)
          = ∑ j : Fin n, (vals[j.val] >>> ((nW - t) * 8)) • toPoint pts[j.val] := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨valid_zero, ?_⟩
    rw [show toPoint (msmAcc pts (vals.map (msmDigits nW)) 0) = 0 from toPoint_zero,
      Nat.sub_zero]
    exact (Finset.sum_eq_zero fun j _ => by
      rw [Nat.shiftRight_eq_zero _ _ (hbound j.val j.isLt), zero_nsmul]).symm
  | succ t ih =>
    intro ht
    obtain ⟨ihv, ihsum⟩ := ih (by omega)
    have hstep : msmAcc pts (vals.map (msmDigits nW)) (t + 1)
        = msmCombine nW (msmAcc pts (vals.map (msmDigits nW)) t) t
            (windowSum pts (vals.map (msmDigits nW)) (nW - 1 - t)) := by
      rw [msmAcc, msmAcc, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hwv, hwsum⟩ := windowSum_spec pts vals nW (nW - 1 - t) (by omega) hval
    -- merging one window into the accumulated shifts
    have hmerge : (2 ^ 8)
          • (∑ j : Fin n, (vals[j.val] >>> ((nW - t) * 8)) • toPoint pts[j.val])
        + ∑ j : Fin n, windowVal vals[j.val] (nW - 1 - t) • toPoint pts[j.val]
        = ∑ j : Fin n, (vals[j.val] >>> ((nW - (t + 1)) * 8)) • toPoint pts[j.val] := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_nsmul', ← add_nsmul]
      congr 1
      have hsw := shift_window vals[j.val] ((nW - 1 - t) * 8)
      rw [show ((nW - 1 - t) * 8 + 8) = (nW - t) * 8 from by omega] at hsw
      rw [windowVal, show (nW - (t + 1)) * 8 = (nW - 1 - t) * 8 from by omega]
      omega
    rw [hstep, msmCombine]
    by_cases hd : nW - 1 - t + 1 < nW
    · rw [ite_eq_left hd]
      obtain ⟨hdv, hdsum⟩ := doubleFold_spec ihv 8
      refine ⟨valid_add hdv hwv, ?_⟩
      rw [toPoint_add hdv hwv, hdsum, ihsum, hwsum]
      exact hmerge
    · rw [ite_eq_right hd]
      have ht0 : t = 0 := by omega
      subst ht0
      refine ⟨valid_add ihv hwv, ?_⟩
      rw [toPoint_add ihv hwv, ihsum, hwsum]
      have hzero : ∑ j : Fin n, (vals[j.val] >>> ((nW - 0) * 8)) • toPoint pts[j.val] = 0 :=
        Finset.sum_eq_zero fun j _ => by
          rw [Nat.shiftRight_eq_zero _ _ (by
            rw [Nat.sub_zero]
            exact hbound j.val j.isLt), zero_nsmul]
      rw [hzero, zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      have hsw := shift_window vals[j.val] ((nW - 1 - 0) * 8)
      have h0 : vals[j.val] >>> ((nW - 1 - 0) * 8 + 8) = 0 := by
        rw [show (nW - 1 - 0) * 8 + 8 = nW * 8 from by omega]
        exact Nat.shiftRight_eq_zero _ _ (hbound j.val j.isLt)
      rw [windowVal, show (nW - (0 + 1)) * 8 = (nW - 1 - 0) * 8 from by omega]
      omega

/-- The model on vectors computes `Σ_j [vals[j]] pts[j]` in the curve group. -/
private theorem msmVecModel_spec {n : Nat} (pts : Vector G1 n) (vals : Vector Nat n)
    (hval : ∀ j (hj : j < n), Valid pts[j]) :
    Valid (msmVecModel pts vals)
    ∧ toPoint (msmVecModel pts vals) = ∑ j : Fin n, vals[j.val] • toPoint pts[j.val] := by
  unfold msmVecModel
  split_ifs with h0 h1
  · subst h0
    exact ⟨valid_zero, by rw [toPoint_zero, Fin.sum_univ_zero]⟩
  · refine ⟨valid_zero, ?_⟩
    rw [toPoint_zero]
    refine (Finset.sum_eq_zero fun j _ => ?_).symm
    have hb := msmMaxBits_bound vals j.val j.isLt
    rw [h1, pow_zero] at hb
    rw [show vals[j.val] = 0 from by omega, zero_nsmul]
  · have hbound : ∀ j (hj : j < n),
        vals[j] < 2 ^ (((msmMaxBits vals + 8 - 1) / 8) * 8) := by
      intro j hj
      refine Nat.lt_of_lt_of_le (msmMaxBits_bound vals j hj) ?_
      exact Nat.pow_le_pow_right (by omega) (by omega)
    rw [foldl_msmWindowStep]
    obtain ⟨hv, hsum⟩ := msmAcc_spec pts vals _ hval hbound _ (Nat.le_refl _)
    refine ⟨hv, hsum.trans (Finset.sum_congr rfl fun j _ => ?_)⟩
    rw [Nat.sub_self, Nat.zero_mul, Nat.shiftRight_zero]

/-- **Correctness of the spec's Pippenger MSM**.

For valid points, `msm` computes `Σ_j [scalars[j]] points[j]` in the curve group. -/
theorem toPoint_msm (points : Array G1) (scalars : Array Fr)
    (hval : ∀ j, j < (if points.size ≤ scalars.size then points.size
      else scalars.size) → Valid points[j]!) :
    Valid (msm points scalars)
    ∧ toPoint (msm points scalars)
        = ∑ j ∈ range (if points.size ≤ scalars.size then points.size
            else scalars.size),
            (scalars[j]!).val • toPoint points[j]! := by
  rw [msm_eq_msmModel, ← Nat.min_def]
  rw [← Nat.min_def] at hval
  obtain ⟨hv, hsum⟩ := msmVecModel_spec (n := min points.size scalars.size)
    (Vector.ofFn fun j => points[j.val]'(Nat.lt_of_lt_of_le j.isLt (Nat.min_le_left _ _)))
    (Vector.ofFn fun j =>
      (scalars[j.val]'(Nat.lt_of_lt_of_le j.isLt (Nat.min_le_right _ _))).val)
    (fun j hj => by
      rw [Vector.getElem_ofFn, ← getElem!_pos points j (by omega)]
      exact hval j hj)
  refine ⟨hv, hsum.trans ?_⟩
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn, getElem!_pos scalars j.val (by omega),
    getElem!_pos points j.val (by omega)]

end EthLib.Cryptography.Bls.G1
