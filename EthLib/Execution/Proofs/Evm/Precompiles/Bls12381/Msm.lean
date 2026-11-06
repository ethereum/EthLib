module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Evm.Precompiles.Bls12381.G2
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Group
import EthLib.Base.Proofs.MapM

/-!
# Proofs: G1MSM and G2MSM of EIP-2537 compute multi-scalar multiplication

- The sum of an MSM succeeds exactly when every point decodes with the subgroup check.
- Its result maps to the sum of `m_i • P_i` on the curve, and every `P_i` lies in the subgroup.
- Each scalar `m_i` is the integer of its 32 bytes, not reduced modulo the subgroup order.

EIP-2537 does not require a scalar to be below the subgroup order.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bytesToNat mapM_cons_ok mapM_ok_mem)
open EthLib.Cryptography.Bls (G1 G2)

/-! ## G1 -/

/-- The fold of G1MSM from any start succeeds exactly when every point decodes.

Its result adds each product to the start, in order. -/
private theorem foldlM_g1Msm_eq_ok_iff (pairs : List (List UInt8 × List UInt8)) (acc q : G1) :
    pairs.foldlM (init := acc) (fun sum (raw, scalar) => do
        let point ← bytesToG1 raw true
        return G1.add sum (G1.mulNat point (bytesToNat scalar))) = .ok q ↔
      ∃ points, pairs.mapM (fun pair => bytesToG1 pair.1 true) = .ok points ∧
        q = (List.zipWith (fun P pair => G1.mulNat P (bytesToNat pair.2)) points pairs).foldl
          G1.add acc := by
  induction pairs generalizing acc with
  | nil => simp [pure, Except.pure, eq_comm]
  | cons pair pairs ih =>
    obtain ⟨raw, scalar⟩ := pair
    rw [List.foldlM_cons]
    simp only [mapM_cons_ok]
    cases hp : bytesToG1 raw true with
    | error e => simp [bind, Except.bind]
    | ok P =>
      change List.foldlM _ (acc.add (P.mulNat (bytesToNat scalar))) pairs = _ ↔ _
      rw [ih]
      constructor
      · rintro ⟨points, hm, rfl⟩
        exact ⟨P :: points, ⟨P, points, rfl, hm, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, rest, hy, hm, rfl⟩, rfl⟩
        cases hy
        exact ⟨rest, hm, rfl⟩

/-- G1MSM's sum succeeds exactly when every point decodes with the subgroup check.

Its result adds `m_i • P_i` in order, from the point at infinity. -/
theorem g1Msm_eq_ok_iff {pairs : List (List UInt8 × List UInt8)} {q : G1} :
    g1Msm pairs = .ok q ↔
      ∃ points, pairs.mapM (fun pair => bytesToG1 pair.1 true) = .ok points ∧
        q = (List.zipWith (fun P pair => G1.mulNat P (bytesToNat pair.2)) points pairs).foldl
          G1.add G1.zero :=
  foldlM_g1Msm_eq_ok_iff pairs G1.zero q

/-- Adding multiples of valid points to a valid start adds their multiples on the curve. -/
private theorem toPoint_foldl_g1 (n : List UInt8 × List UInt8 → Nat) :
    ∀ (points : List G1) (pairs : List (List UInt8 × List UInt8)) (acc : G1), G1.Valid acc →
      (∀ P ∈ points, G1.Valid P) →
      G1.toPoint ((List.zipWith (fun P pair => G1.mulNat P (n pair)) points pairs).foldl
          G1.add acc) =
        G1.toPoint acc + (List.zipWith (fun P pair => n pair • G1.toPoint P) points pairs).sum
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | P :: points, pair :: pairs, acc, hacc, hpoints => by
    have hP := hpoints P List.mem_cons_self
    have hmul := G1.valid_mulNat hP (n pair)
    simp only [List.zipWith_cons_cons, List.foldl_cons, List.sum_cons]
    rw [toPoint_foldl_g1 n points pairs _ (G1.valid_add hacc hmul)
        fun Q hQ => hpoints Q (List.mem_cons_of_mem P hQ),
      G1.toPoint_add hacc hmul, G1.toPoint_mulNat hP, add_assoc]

/-- A successful G1MSM sum maps to the sum of `m_i • P_i` on the curve.

`P_i` is the `i`-th point, decoded with the subgroup check.

`m_i` is the integer of the `i`-th scalar bytes, not reduced modulo the subgroup order. -/
theorem toPoint_of_g1Msm_eq_ok {pairs : List (List UInt8 × List UInt8)} {points : List G1}
    {q : G1} (hdec : pairs.mapM (fun pair => bytesToG1 pair.1 true) = .ok points)
    (h : g1Msm pairs = .ok q) :
    G1.toPoint q =
      (List.zipWith (fun P pair => bytesToNat pair.2 • G1.toPoint P) points pairs).sum := by
  obtain ⟨points', hdec', rfl⟩ := g1Msm_eq_ok_iff.mp h
  rw [hdec] at hdec'
  cases hdec'
  rw [toPoint_foldl_g1 _ points pairs G1.zero G1.valid_zero, G1.toPoint_zero, zero_add]
  intro P hP
  obtain ⟨_, _, hpair⟩ := mapM_ok_mem hdec P hP
  exact valid_of_bytesToG1_eq_ok hpair

/-- Every point that G1MSM decodes lies in the subgroup. -/
theorem inSubgroup_of_mem_g1Msm {pairs : List (List UInt8 × List UInt8)} {points : List G1}
    (hdec : pairs.mapM (fun pair => bytesToG1 pair.1 true) = .ok points) {P : G1}
    (hP : P ∈ points) : G1.inSubgroup P = true := by
  obtain ⟨_, _, hpair⟩ := mapM_ok_mem hdec P hP
  exact inSubgroup_of_bytesToG1_eq_ok hpair

/-- The G1MSM sum of the generator with any scalar is that multiple of the generator.

The scalar is not reduced, so a scalar above the subgroup order still gives its multiple. -/
theorem toPoint_g1Msm_generator (scalar : List UInt8) :
    ∃ q, g1Msm [(g1ToBytes G1.generator, scalar)] = .ok q ∧
      G1.toPoint q = bytesToNat scalar • G1.toPoint G1.generator := by
  obtain ⟨g, hg, hgt⟩ := bytesToG1_g1ToBytes G1.valid_generator (subgroupCheck := true)
    fun _ => (G1.inSubgroup_iff_modulus_smul_eq_zero G1.valid_generator).mpr
      G1.modulus_smul_generator
  have hdec : [(g1ToBytes G1.generator, scalar)].mapM (fun pair => bytesToG1 pair.1 true) =
      .ok [g] := by
    simp [hg, bind, Except.bind, pure, Except.pure]
  have h := g1Msm_eq_ok_iff.mpr ⟨[g], hdec, rfl⟩
  refine ⟨_, h, ?_⟩
  rw [toPoint_of_g1Msm_eq_ok hdec h]
  simp [hgt]

/-! ## G2 -/

/-- The fold of G2MSM from any start succeeds exactly when every point decodes.

Its result adds each product to the start, in order. -/
private theorem foldlM_g2Msm_eq_ok_iff (pairs : List (List UInt8 × List UInt8)) (acc q : G2) :
    pairs.foldlM (init := acc) (fun sum (raw, scalar) => do
        let point ← bytesToG2 raw true
        return G2.add sum (G2.mulNat point (bytesToNat scalar))) = .ok q ↔
      ∃ points, pairs.mapM (fun pair => bytesToG2 pair.1 true) = .ok points ∧
        q = (List.zipWith (fun P pair => G2.mulNat P (bytesToNat pair.2)) points pairs).foldl
          G2.add acc := by
  induction pairs generalizing acc with
  | nil => simp [pure, Except.pure, eq_comm]
  | cons pair pairs ih =>
    obtain ⟨raw, scalar⟩ := pair
    rw [List.foldlM_cons]
    simp only [mapM_cons_ok]
    cases hp : bytesToG2 raw true with
    | error e => simp [bind, Except.bind]
    | ok P =>
      change List.foldlM _ (acc.add (P.mulNat (bytesToNat scalar))) pairs = _ ↔ _
      rw [ih]
      constructor
      · rintro ⟨points, hm, rfl⟩
        exact ⟨P :: points, ⟨P, points, rfl, hm, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨y, rest, hy, hm, rfl⟩, rfl⟩
        cases hy
        exact ⟨rest, hm, rfl⟩

/-- G2MSM's sum succeeds exactly when every point decodes with the subgroup check.

Its result adds `m_i • P_i` in order, from the point at infinity. -/
theorem g2Msm_eq_ok_iff {pairs : List (List UInt8 × List UInt8)} {q : G2} :
    g2Msm pairs = .ok q ↔
      ∃ points, pairs.mapM (fun pair => bytesToG2 pair.1 true) = .ok points ∧
        q = (List.zipWith (fun P pair => G2.mulNat P (bytesToNat pair.2)) points pairs).foldl
          G2.add G2.zero :=
  foldlM_g2Msm_eq_ok_iff pairs G2.zero q

/-- Adding multiples of valid points to a valid start adds their multiples on the curve. -/
private theorem toPoint_foldl_g2 (n : List UInt8 × List UInt8 → Nat) :
    ∀ (points : List G2) (pairs : List (List UInt8 × List UInt8)) (acc : G2), G2.Valid acc →
      (∀ P ∈ points, G2.Valid P) →
      G2.toPoint ((List.zipWith (fun P pair => G2.mulNat P (n pair)) points pairs).foldl
          G2.add acc) =
        G2.toPoint acc + (List.zipWith (fun P pair => n pair • G2.toPoint P) points pairs).sum
  | [], _, _, _, _ => by simp
  | _ :: _, [], _, _, _ => by simp
  | P :: points, pair :: pairs, acc, hacc, hpoints => by
    have hP := hpoints P List.mem_cons_self
    have hmul := G2.valid_mulNat hP (n pair)
    simp only [List.zipWith_cons_cons, List.foldl_cons, List.sum_cons]
    rw [toPoint_foldl_g2 n points pairs _ (G2.valid_add hacc hmul)
        fun Q hQ => hpoints Q (List.mem_cons_of_mem P hQ),
      G2.toPoint_add hacc hmul, G2.toPoint_mulNat hP, add_assoc]

/-- A successful G2MSM sum maps to the sum of `m_i • P_i` on the curve.

`P_i` is the `i`-th point, decoded with the subgroup check.

`m_i` is the integer of the `i`-th scalar bytes, not reduced modulo the subgroup order. -/
theorem toPoint_of_g2Msm_eq_ok {pairs : List (List UInt8 × List UInt8)} {points : List G2}
    {q : G2} (hdec : pairs.mapM (fun pair => bytesToG2 pair.1 true) = .ok points)
    (h : g2Msm pairs = .ok q) :
    G2.toPoint q =
      (List.zipWith (fun P pair => bytesToNat pair.2 • G2.toPoint P) points pairs).sum := by
  obtain ⟨points', hdec', rfl⟩ := g2Msm_eq_ok_iff.mp h
  rw [hdec] at hdec'
  cases hdec'
  rw [toPoint_foldl_g2 _ points pairs G2.zero G2.valid_zero, G2.toPoint_zero, zero_add]
  intro P hP
  obtain ⟨_, _, hpair⟩ := mapM_ok_mem hdec P hP
  exact valid_of_bytesToG2_eq_ok hpair

/-- Every point that G2MSM decodes lies in the subgroup. -/
theorem inSubgroup_of_mem_g2Msm {pairs : List (List UInt8 × List UInt8)} {points : List G2}
    (hdec : pairs.mapM (fun pair => bytesToG2 pair.1 true) = .ok points) {P : G2}
    (hP : P ∈ points) : G2.inSubgroup P = true := by
  obtain ⟨_, _, hpair⟩ := mapM_ok_mem hdec P hP
  exact inSubgroup_of_bytesToG2_eq_ok hpair

/-- The G2MSM sum of the generator with any scalar is that multiple of the generator.

The scalar is not reduced, so a scalar above the subgroup order still gives its multiple. -/
theorem toPoint_g2Msm_generator (scalar : List UInt8) :
    ∃ q, g2Msm [(g2ToBytes G2.generator, scalar)] = .ok q ∧
      G2.toPoint q = bytesToNat scalar • G2.toPoint G2.generator := by
  obtain ⟨g, hg, hgt⟩ := bytesToG2_g2ToBytes G2.valid_generator (subgroupCheck := true)
    fun _ => G2.inSubgroup_generator
  have hdec : [(g2ToBytes G2.generator, scalar)].mapM (fun pair => bytesToG2 pair.1 true) =
      .ok [g] := by
    simp [hg, bind, Except.bind, pure, Except.pure]
  have h := g2Msm_eq_ok_iff.mpr ⟨[g], hdec, rfl⟩
  refine ⟨_, h, ?_⟩
  rw [toPoint_of_g2Msm_eq_ok hdec h]
  simp [hgt]

end EthLib.Execution.Evm.Precompiles.Bls12381
