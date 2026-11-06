module

public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Dft
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.FourStep
public import EthLib.Cryptography.Proofs.Kzg.SetupLagrange.Roots
public import EthLib.Cryptography.Proofs.Kzg.SetupTorsion.Embedded
public import EthLib.Cryptography.Proofs.Kzg.LagrangeCoefficients

/-!
# Proofs: the Lagrange points of the embedded setup from checks of three rounds

The inverse transform of the 4096 monomial points runs in three rounds of transforms of size 16.

Four tables hold affine points as pairs of naturals.

- Table `M` holds the decoded monomial points, and table `L` the decoded Lagrange points.
- Tables `A` and `B` hold the results of the first two rounds.

The checks test that each string of the setup encodes its table entry.

They also compare each transform of size 16 with the entries of its inputs and outputs.

If all checks pass, each Lagrange point is a combination of the monomial points.

The factors are the coefficients of its basis polynomial.

The tables are arbitrary here, so a wrong table only makes a check fail.
-/

@[expose] public section

namespace EthLib.Cryptography.Kzg.SetupLagrange

open EthLib.Cryptography.Bls (Fr G1)
open scoped EthLib.Cryptography.Bls.Fr
open EthLib.Cryptography.Kzg.Constants
open EthLib.Cryptography.Kzg.SetupTorsion (codes)
open EthLib.Cryptography.Kzg.BitReversal
open Finset

/-! ## Points by position -/

/-- Output `i` of a successful map over an array is the image of input `i`. -/
theorem array_mapM_ok_getElem {ε α β : Type} [Inhabited β] {f : α → Except ε β} {xs : Array α}
    {ys : Array β} (h : xs.mapM f = .ok ys) :
    ys.size = xs.size ∧ ∀ (i : Nat) (hi : i < xs.size), f xs[i] = .ok ys[i]! := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | error e => rw [hl] at h; cases h
  | ok zs =>
    rw [hl] at h
    have hzs : zs.toArray = ys := Except.ok.inj h
    subst hzs
    have hlen := Base.mapM_ok_length hl
    refine ⟨by simpa using hlen, fun i hi => ?_⟩
    have hi' : i < xs.toList.length := by simpa using hi
    have he := Base.mapM_ok_getElem hl i hi'
    rw [getElem!_pos zs.toArray i (by simpa [hlen] using hi)]
    simpa using he

/-- Each string of a decoded list gives the byte string at its position. -/
theorem hexListToBytes_getElem {hex : Array String} {bytes : Array ByteArray}
    (h : TrustedSetup.hexListToBytes hex = .ok bytes) :
    bytes.size = hex.size ∧
      ∀ (i : Nat) (hi : i < hex.size), TrustedSetup.hexToBytes? hex[i] = some bytes[i]! := by
  obtain ⟨hsize, hget⟩ := array_mapM_ok_getElem h
  refine ⟨hsize, fun i hi => ?_⟩
  have he := hget i hi
  split at he
  · rename_i b hb
    rw [hb, Except.ok.inj he]
  · cases he

/-- Each point of a decoded setup decompresses from the bytes at its position.

Lagrange point `i` comes from position `reverseBits i 4096`. -/
theorem ofBytes_getElem {g1LagrangeBytes g1MonomialBytes g2MonomialBytes : Array ByteArray}
    {s : TrustedSetup}
    (h : TrustedSetup.ofBytes g1LagrangeBytes g1MonomialBytes g2MonomialBytes = .ok s)
    (i : Fin FIELD_ELEMENTS_PER_BLOB) :
    G1.uncompress g1MonomialBytes[i.val]! = .ok s.g1Monomial[i] ∧
      G1.uncompress g1LagrangeBytes[reverseBits i.val FIELD_ELEMENTS_PER_BLOB]! =
        .ok s.g1LagrangeBrp[i] := by
  unfold TrustedSetup.ofBytes at h
  dsimp only at h
  cases h₁ : g1LagrangeBytes.mapM fun b =>
      (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁] at h; cases h
  | ok lagrange =>
  cases h₂ : g1MonomialBytes.mapM fun b =>
      (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁, h₂] at h; cases h
  | ok monomial =>
  cases h₃ : g2MonomialBytes.mapM fun b =>
      (Bls.G2.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup with
  | error e => rw [h₁, h₂, h₃] at h; cases h
  | ok monomial2 =>
  rw [h₁, h₂, h₃] at h
  dsimp only [bind, Except.bind] at h
  -- A successful map gives each output from the input at the same position.
  have hpos {xs : Array ByteArray} {ys : Array G1}
      (hm : (xs.mapM fun b =>
        (Bls.G1.uncompress b).mapError fun _ => KzgError.invalidTrustedSetup) = .ok ys)
      (j : Nat) (hj : j < ys.size) : G1.uncompress xs[j]! = .ok ys[j] := by
    obtain ⟨hsize, hget⟩ := array_mapM_ok_getElem hm
    have hj' : j < xs.size := by rw [← hsize]; exact hj
    rw [getElem!_pos xs j hj', ← getElem!_pos ys j hj]
    exact Base.mapError_ok_iff.mp (hget j hj')
  split at h
  · rename_i hl
    split at h
    · rename_i hm
      split at h
      · cases h
        refine ⟨hpos h₂ i.val (by rw [hm]; exact i.isLt), ?_⟩
        have hsz : lagrange.size = 2 ^ 12 := hl
        have hr : reverseBits i.val (2 ^ 12) < lagrange.size := by
          rw [hsz]
          exact reverseBits_lt_two_pow _ _
        have hget : (bitReversalPermutation lagrange)[i.val]'(by
            rw [size_bitReversalPermutation, hl]; exact i.isLt) =
            lagrange[reverseBits i.val (2 ^ 12)] := by
          rw [getElem_bitReversalPermutation, hsz, getElem!_pos lagrange _ hr]
        exact (hpos h₁ _ hr).trans (congrArg Except.ok hget.symm)
      · cases h
    · cases h
  · cases h

/-- A point with coordinates `(x, y, 1)` is the point `(x, y, 1)` of the naturals. -/
theorem eq_affinePoint {q : G1} {x y : Nat}
    (h : G1.TorsionCheck.coords q = (x, y, 1)) : q = affinePoint x y := by
  obtain ⟨qx, qy, qz⟩ := q
  simp only [G1.TorsionCheck.coords, Prod.mk.injEq] at h
  obtain ⟨hx, hy, hz⟩ := h
  have ex : qx = Bls.Fp.ofNat x := Bls.Fp.ext (by
    rw [Bls.Fp.val_ofNat, ← hx, Nat.mod_eq_of_lt (Bls.Fp.val_lt qx)])
  have ey : qy = Bls.Fp.ofNat y := Bls.Fp.ext (by
    rw [Bls.Fp.val_ofNat, ← hy, Nat.mod_eq_of_lt (Bls.Fp.val_lt qy)])
  have ez : qz = Bls.Fp.one := Bls.Fp.ext (by rw [hz, Bls.Fp.one_def, Bls.Fp.val_one])
  rw [ex, ey, ez]
  rfl

/-! ## The checks -/

/-- A table of 4096 affine points, as pairs of naturals read by index. -/
abbrev Table := Nat → Nat × Nat

/-- Entry `n` of a table, as a point of `G1`. -/
def Table.point (t : Table) (n : Nat) : G1 := affinePoint (t n).1 (t n).2

/-- Each list of digit codes encodes its entry of the table, from entry `a` on. -/
def decodeCheck (t : Table) : Nat → List (List Nat) → Bool
  | _, [] => true
  | a, c :: cs => encodes c (t a).1 (t a).2 && decodeCheck t (a + 1) cs

/-- The roots `u^i` of the transforms of size 16. -/
def roots16 : Vector Nat (2 ^ 4) := Vector.ofFn fun i => rootPowNat i.val

/-- The first round at `(j2, j3)`, from `M(256 j1 + 16 j2 + j3)` to `A(256 k1 + 16 j2 + j3)`. -/
def checkA (tM tA : Table) (j2 j3 : Nat) : Bool :=
  dftCheck (k := 4) (Vector.ofFn fun i => tM (256 * i.val + 16 * j2 + j3))
    (Vector.ofFn fun _ => 1) roots16 (Vector.ofFn fun k1 => tA (256 * k1.val + 16 * j2 + j3))

/-- The second round at `(k1, j3)`, from `A(256 k1 + 16 j2 + j3)` to `B(256 k1 + 16 k2 + j3)`. -/
def checkB (tA tB : Table) (k1 j3 : Nat) : Bool :=
  dftCheck (k := 4) (Vector.ofFn fun i => tA (256 * k1 + 16 * i.val + j3))
    (Vector.ofFn fun i => scalarB k1 i.val) roots16
    (Vector.ofFn fun k2 => tB (256 * k1 + 16 * k2.val + j3))

/-- The third round at `(k1, k2)`, from `B(256 k1 + 16 k2 + j3)` to `L(k1 + 16 k2 + 256 k3)`. -/
def checkC (tB tL : Table) (k1 k2 : Nat) : Bool :=
  dftCheck (k := 4) (Vector.ofFn fun i => tB (256 * k1 + 16 * k2 + i.val))
    (Vector.ofFn fun i => scalarC k1 k2 i.val) roots16
    (Vector.ofFn fun k3 => tL (k1 + 16 * k2 + 256 * k3.val))


/-! ## What the checks give -/

theorem decodeCheck_spec {t : Table} :
    ∀ {a : Nat} {cs : List (List Nat)}, decodeCheck t a cs = true →
      ∀ (i : Nat) (hi : i < cs.length), encodes cs[i] (t (a + i)).1 (t (a + i)).2 = true
  | _, [], _, i, hi => absurd hi (Nat.not_lt_zero i)
  | a, c :: cs, h, i, hi => by
    simp only [decodeCheck, Bool.and_eq_true] at h
    cases i with
    | zero => exact h.1
    | succ i =>
      rw [List.getElem_cons_succ, show a + (i + 1) = a + 1 + i by omega]
      exact decodeCheck_spec h.2 i (by simpa using hi)

/-- The checks of the chunks of 16 strings give the check of each string. -/
theorem encodes_of_chunks {t : Table} {hex : Array String} (hsize : hex.size = 4096)
    (h : ∀ c < 256, decodeCheck t (16 * c) (((hex.toList.map codes).drop (16 * c)).take 16) = true)
    {j : Nat} (hj : j < 4096) : encodes (codes hex[j]!) (t j).1 (t j).2 = true := by
  have hc := decodeCheck_spec (h (j / 16) (by omega)) (j % 16)
    (by simp only [List.length_take, List.length_drop, List.length_map, Array.length_toList,
      hsize]; omega)
  rw [show 16 * (j / 16) + j % 16 = j by omega] at hc
  refine Eq.trans ?_ hc
  rw [getElem!_pos hex j (by omega)]
  simp only [List.getElem_take, List.getElem_drop, List.getElem_map, Array.getElem_toList]
  congr 3
  omega

/-- One transform of size 16 that passes its check gives each output as a sum. -/
theorem toPoint_of_roundCheck {ins outs : Nat → Nat × Nat} {tw : Nat → Nat}
    (h : dftCheck (k := 4) (Vector.ofFn fun i => ins i.val) (Vector.ofFn fun i => tw i.val)
      roots16 (Vector.ofFn fun j => outs j.val) = true)
    (htw : ∀ i < 16, tw i < Fr.modulus)
    (htor : ∀ i < 16, Fr.modulus • G1.toPoint (affinePoint (ins i).1 (ins i).2) = 0)
    {j : Nat} (hj : j < 16) :
    G1.toPoint (affinePoint (outs j).1 (outs j).2) =
      ∑ i ∈ range 16, ((zeta ^ 256) ^ (i * j)).val • tw i •
        G1.toPoint (affinePoint (ins i).1 (ins i).2) := by
  have hroots : ∀ (i : Nat) (hi : i < 2 ^ 4), (roots16[i]'hi) < Fr.modulus ∧
      Fr.ofNat (roots16[i]'hi) = (zeta ^ 256) ^ i := by
    intro i hi
    simpa [roots16] using rootPowNat_spec (i := i) hi
  have he := toPoint_of_dftCheck (k := 4) isPrimitiveRoot_root h hroots
    (fun i hi => by simpa using htw i hi) (fun i hi => by simpa using htor i hi) ⟨j, hj⟩
  simp only [Fin.getElem_fin, Vector.getElem_ofFn] at he
  rw [he]
  exact Fin.sum_univ_eq_sum_range
    (fun i => ((zeta ^ 256) ^ (i * j)).val • tw i • G1.toPoint (affinePoint (ins i).1 (ins i).2))
    16

/-- A sum of multiples of points of order dividing `r` has order dividing `r`. -/
theorem modulus_smul_sum {P : Nat → G1.curve.toAffine.Point} {a b : Nat → Nat} {n : Nat}
    (h : ∀ i < n, Fr.modulus • P i = 0) :
    Fr.modulus • ∑ i ∈ range n, a i • b i • P i = 0 := by
  rw [smul_sum]
  refine sum_eq_zero fun i hi => ?_
  rw [smul_comm, smul_comm Fr.modulus (b i), h i (mem_range.mp hi), nsmul_zero, nsmul_zero]

private theorem scalarB_val {k1 j2 : Nat} (hk1 : k1 < 16) (hj2 : j2 < 16) :
    scalarB k1 j2 = ((4096 : Fr)⁻¹ * zeta ^ (16 * j2 * k1)).val := by
  rw [← (scalarB_spec hk1 hj2).2, Fr.val_ofNat_of_lt (scalarB_spec hk1 hj2).1]

private theorem scalarC_val {k1 k2 j3 : Nat} (hk1 : k1 < 16) (hk2 : k2 < 16) (hj3 : j3 < 16) :
    scalarC k1 k2 j3 = (zeta ^ (j3 * (k1 + 16 * k2))).val := by
  rw [← (scalarC_spec hk1 hk2 hj3).2, Fr.val_ofNat_of_lt (scalarC_spec hk1 hk2 hj3).1]

/-! ## The Lagrange points of the embedded setup -/

/-- If the embedded setup decodes and every check passes, each Lagrange point is a sum.

Its terms are the monomial points times the coefficients of its basis polynomial. -/
theorem lagrangeOfMonomial_of_checks {s : TrustedSetup} (hs : TrustedSetup.ofHex = .ok s)
    {tM tA tB tL : Table}
    (hM : ∀ c < 256, decodeCheck tM (16 * c)
      (((TrustedSetupData.g1MonomialHex.toList.map codes).drop (16 * c)).take 16) = true)
    (hL : ∀ c < 256, decodeCheck tL (16 * c)
      (((TrustedSetupData.g1LagrangeHex.toList.map codes).drop (16 * c)).take 16) = true)
    (hA : ∀ j2 < 16, ∀ j3 < 16, checkA tM tA j2 j3 = true)
    (hB : ∀ k1 < 16, ∀ j3 < 16, checkB tA tB k1 j3 = true)
    (hC : ∀ k1 < 16, ∀ k2 < 16, checkC tB tL k1 k2 = true) :
    s.LagrangeOfMonomial := by
  have hMsize : TrustedSetupData.g1MonomialHex.size = 4096 := by decide +kernel
  have hLsize : TrustedSetupData.g1LagrangeHex.size = 4096 := by decide +kernel
  -- Each decoded point is the point of its table entry.
  have hpts (i : Fin FIELD_ELEMENTS_PER_BLOB) : s.g1Monomial[i] = tM.point i ∧
      s.g1LagrangeBrp[i] = tL.point (reverseBits i.val FIELD_ELEMENTS_PER_BLOB) := by
    have h := hs
    unfold TrustedSetup.ofHex at h
    generalize hl : TrustedSetup.hexListToBytes TrustedSetupData.g1LagrangeHex = a at h
    generalize hm : TrustedSetup.hexListToBytes TrustedSetupData.g1MonomialHex = b at h
    generalize TrustedSetup.hexListToBytes TrustedSetupData.g2MonomialHex = c at h
    cases a with
    | error e => cases h
    | ok lb =>
    cases b with
    | error e => cases h
    | ok mb =>
    cases c with
    | error e => cases h
    | ok gb =>
    obtain ⟨hum, hul⟩ := ofBytes_getElem h i
    have hmget := (hexListToBytes_getElem hm).2
    have hlget := (hexListToBytes_getElem hl).2
    have hr : reverseBits i.val FIELD_ELEMENTS_PER_BLOB < 4096 := reverseBits_lt_two_pow i.val 12
    constructor
    · have hd := encodes_of_chunks hMsize hM i.isLt
      rw [getElem!_pos _ i.val (by rw [hMsize]; exact i.isLt)] at hd
      exact eq_affinePoint
        (coords_of_encodes hd (hmget i.val (by rw [hMsize]; exact i.isLt)) hum)
    · have hd := encodes_of_chunks hLsize hL hr
      rw [getElem!_pos _ _ (by rw [hLsize]; exact hr)] at hd
      exact eq_affinePoint (coords_of_encodes hd (hlget _ (by rw [hLsize]; exact hr)) hul)
  -- The monomial points have order dividing `r`.
  have htorM (j : Nat) (hj : j < 4096) : Fr.modulus • G1.toPoint (tM.point j) = 0 := by
    have ht := TrustedSetup.ofHex_torsion hs hj
    rw [getElem!_pos s.g1Monomial.toArray j
      (by simpa using (show j < FIELD_ELEMENTS_PER_BLOB from hj)), Vector.getElem_toArray] at ht
    have hp := (hpts ⟨j, hj⟩).1
    rw [Fin.getElem_fin] at hp
    rwa [hp] at ht
  -- The first round.
  have hAsum : ∀ j2 < 16, ∀ j3 < 16, ∀ k1 < 16,
      G1.toPoint (tA.point (256 * k1 + 16 * j2 + j3)) =
        ∑ j1 ∈ range 16, ((zeta ^ 256) ^ (j1 * k1)).val • (1 : Nat) •
          G1.toPoint (tM.point (256 * j1 + 16 * j2 + j3)) ∧
      Fr.modulus • G1.toPoint (tA.point (256 * k1 + 16 * j2 + j3)) = 0 := by
    intro j2 hj2 j3 hj3 k1 hk1
    have he := toPoint_of_roundCheck (ins := fun i => tM (256 * i + 16 * j2 + j3))
      (outs := fun k1 => tA (256 * k1 + 16 * j2 + j3)) (tw := fun _ => 1) (hA j2 hj2 j3 hj3)
      (fun _ _ => by decide +kernel) (fun i hi => htorM _ (by omega)) hk1
    refine ⟨he, ?_⟩
    rw [Table.point, he]
    exact modulus_smul_sum fun i hi => htorM _ (by omega)
  -- The second round.
  have hBsum : ∀ k1 < 16, ∀ j3 < 16, ∀ k2 < 16,
      G1.toPoint (tB.point (256 * k1 + 16 * k2 + j3)) =
        ∑ j2 ∈ range 16, ((zeta ^ 256) ^ (j2 * k2)).val • scalarB k1 j2 •
          G1.toPoint (tA.point (256 * k1 + 16 * j2 + j3)) ∧
      Fr.modulus • G1.toPoint (tB.point (256 * k1 + 16 * k2 + j3)) = 0 := by
    intro k1 hk1 j3 hj3 k2 hk2
    have htor (i : Nat) (hi : i < 16) := (hAsum i hi j3 hj3 k1 hk1).2
    have he := toPoint_of_roundCheck (ins := fun i => tA (256 * k1 + 16 * i + j3))
      (outs := fun k2 => tB (256 * k1 + 16 * k2 + j3)) (tw := fun i => scalarB k1 i)
      (hB k1 hk1 j3 hj3) (fun i hi => (scalarB_spec hk1 hi).1) htor hk2
    refine ⟨he, ?_⟩
    rw [Table.point, he]
    exact modulus_smul_sum htor
  -- The third round.
  have hCsum : ∀ k1 < 16, ∀ k2 < 16, ∀ k3 < 16,
      G1.toPoint (tL.point (k1 + 16 * k2 + 256 * k3)) =
        ∑ j3 ∈ range 16, ((zeta ^ 256) ^ (j3 * k3)).val • scalarC k1 k2 j3 •
          G1.toPoint (tB.point (256 * k1 + 16 * k2 + j3)) := by
    intro k1 hk1 k2 hk2 k3 hk3
    exact toPoint_of_roundCheck (ins := fun i => tB (256 * k1 + 16 * k2 + i))
      (outs := fun k3 => tL (k1 + 16 * k2 + 256 * k3)) (tw := fun i => scalarC k1 k2 i)
      (hC k1 hk1 k2 hk2) (fun i hi => (scalarC_spec hk1 hk2 hi).1)
      (fun i hi => (hBsum k1 hk1 i hi k2 hk2).2) hk3
  -- The three rounds give the transform of size 4096.
  have htotal : ∀ k1 < 16, ∀ k2 < 16, ∀ k3 < 16,
      G1.toPoint (tL.point (k1 + 16 * k2 + 256 * k3)) =
        ∑ j ∈ range 4096, ((4096 : Fr)⁻¹ * zeta ^ (j * (k1 + 16 * k2 + 256 * k3))).val •
          G1.toPoint (tM.point (j % 4096)) := by
    intro k1 hk1 k2 hk2 k3 hk3
    rw [sum_eq_threeRounds (P := fun j => G1.toPoint (tM.point (j % 4096)))
      (fun j => htorM _ (Nat.mod_lt _ (by decide))) isPrimitiveRoot_zeta.pow_eq_one _ k1 k2 k3,
      hCsum k1 hk1 k2 hk2 k3 hk3]
    refine sum_congr rfl fun j3 hj3 => ?_
    rw [mem_range] at hj3
    rw [scalarC_val hk1 hk2 hj3, (hBsum k1 hk1 j3 hj3 k2 hk2).1]
    congr 2
    refine sum_congr rfl fun j2 hj2 => ?_
    rw [mem_range] at hj2
    rw [scalarB_val hk1 hj2, (hAsum j2 hj2 j3 hj3 k1 hk1).1]
    congr 2
    refine sum_congr rfl fun j1 hj1 => ?_
    rw [mem_range] at hj1
    rw [one_nsmul, Nat.mod_eq_of_lt (by omega)]
  -- Lagrange point `i` is entry `reverseBits i` of the transform.
  intro i
  have hb : reverseBits i.val FIELD_ELEMENTS_PER_BLOB < 4096 := reverseBits_lt_two_pow i.val 12
  have hdig : reverseBits i.val FIELD_ELEMENTS_PER_BLOB =
      reverseBits i.val FIELD_ELEMENTS_PER_BLOB % 16 +
        16 * (reverseBits i.val FIELD_ELEMENTS_PER_BLOB / 16 % 16) +
        256 * (reverseBits i.val FIELD_ELEMENTS_PER_BLOB / 256) := by omega
  rw [(hpts i).2, hdig, htotal _ (by omega) _ (by omega) _ (by omega), ← hdig,
    ← Fin.sum_univ_eq_sum_range (fun j => ((4096 : Fr)⁻¹ *
      zeta ^ (j * reverseBits i.val FIELD_ELEMENTS_PER_BLOB)).val •
        G1.toPoint (tM.point (j % 4096)))]
  refine sum_congr rfl fun j _ => ?_
  rw [coeff_basis i j.isLt, (hpts j).1, Nat.mod_eq_of_lt j.isLt, evalDomain,
    getElem_rootsOfUnityBrp field_elements_per_blob_eq_two_pow, zeta, ← inv_pow, ← pow_mul,
    Nat.mul_comm]
  rfl

end EthLib.Cryptography.Kzg.SetupLagrange
