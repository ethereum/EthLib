module

public import EthLib.Execution.Evm.Precompiles.Bls12381.G1
public import EthLib.Execution.Evm.Precompiles.Bls12381.G2
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G1
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.G2
import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.Group
import EthLib.Cryptography.Proofs.Bls.PairingCongr
public import EthLib.Execution.Proofs.Evm.Precompiles.Bls12381.RoundTrip

/-!
# Proofs: G1MSM and G2MSM of EIP-2537 compute multi-scalar multiplication

- G1MSM and G2MSM check that every decoded point lies in the subgroup of prime order.
- Both read each 32-byte scalar as a big-endian integer without reducing it.
- Both return the encoding of the sum of `m • P` over their decoded pairs, in the subgroup.
- Both succeed on every non-empty list of encoded subgroup points and scalars, with enough gas.
-/

@[expose] public section

namespace EthLib.Execution.Evm.Precompiles.Bls12381

open EthLib.Base (bind_ok_iff bytesToNat bytesToNat_natToBytes_of_lt mapM_cons_ok natToBytes
  natToBytes_length)
open EthLib.Cryptography.Bls (Fr G1 G2)

/-- The 160-byte encoding of one G1MSM pair: a padded G1 point, then a 32-byte scalar. -/
def g1MsmPairBytes (p : G1) (m : Nat) : List UInt8 := padG1 (g1ToBytes p) ++ natToBytes 32 m

/-- The 288-byte encoding of one G2MSM pair: a padded G2 point, then a 32-byte scalar. -/
def g2MsmPairBytes (p : G2) (m : Nat) : List UInt8 := padG2 (g2ToBytes p) ++ natToBytes 32 m

/-- The sum of `[m] P` over a list of G1 pairs, accumulated from `G1.zero` as `g1Msm` does. -/
def g1MsmPoints (ps : List (G1 × Nat)) : G1 :=
  ps.foldl (fun s (p, m) => G1.add s (G1.mulNat p m)) G1.zero

/-- The sum of `[m] P` over a list of G2 pairs, accumulated from `G2.zero` as `g2Msm` does. -/
def g2MsmPoints (ps : List (G2 × Nat)) : G2 :=
  ps.foldl (fun s (p, m) => G2.add s (G2.mulNat p m)) G2.zero

private structure MsmSpec (P Pt : Type) [AddCommMonoid Pt] where
  (V : P → Prop) (sub : P → Bool) (pt : P → Pt) (z : P) (add : P → P → P) (mul : P → Nat → P)
  (dec : List UInt8 → Bool → Except Bls12381Error P) (enc pad : P → List UInt8)
  (unpad : List UInt8 → Except Bls12381Error (List UInt8)) (pLen : Nat) (msmGas : Nat → Nat)
  (msm : List (List UInt8 × List UInt8) → Except Bls12381Error P)
  (call : ByteArray → Nat → Except Bls12381Error ByteArray)
  (hz : V z) (hpz : pt z = 0) (hadd : ∀ {p q}, V p → V q → V (add p q))
  (hpadd : ∀ {p q}, V p → V q → pt (add p q) = pt p + pt q)
  (hmul : ∀ {p}, V p → ∀ m, V (mul p m)) (hpmul : ∀ {p}, V p → ∀ m, pt (mul p m) = m • pt p)
  (hsub : ∀ {p}, V p → (sub p = true ↔ Fr.modulus • pt p = 0))
  (hdec : ∀ {r b p}, dec r b = .ok p → V p ∧ (b = true → sub p = true))
  (hrt : ∀ {p}, V p → sub p → ∃ q, dec (enc p) true = .ok q ∧ pt q = pt p)
  (hcg : ∀ {p q}, V p → V q → pt p = pt q → pad p = pad q)
  (hlen : ∀ p, (pad p).length = pLen) (hun : ∀ p, unpad (pad p) = .ok (enc p))
  (hmsm : ∀ ps, msm ps = ps.foldlM (init := z) fun s (r, sc) => do
    return add s (mul (← dec r true) (bytesToNat sc)))
  (hcall : ∀ d g, call d g = do
    if d.size = 0 ∨ d.size % (pLen + 32) ≠ 0 then throw (.invalidInputLength d.size)
    let k := d.size / (pLen + 32)
    if g < msmGas k then throw (.outOfGas (msmGas k) g)
    let ps ← (chunks (pLen + 32) k d.data.toList).mapM fun c => do
      return (← unpad (c.take pLen), c.drop pLen)
    return ⟨(pad (← msm ps)).toArray⟩)

private noncomputable def g1Spec : MsmSpec G1 G1.curve.toAffine.Point :=
  ⟨G1.Valid, G1.inSubgroup, G1.toPoint, G1.zero, G1.add, G1.mulNat, bytesToG1, g1ToBytes,
    padG1 ∘ g1ToBytes, unpadG1, 128, bls12G1MsmGas, g1Msm, bls12G1Msm, G1.valid_zero,
    G1.toPoint_zero, G1.valid_add, G1.toPoint_add, G1.valid_mulNat, G1.toPoint_mulNat,
    G1.inSubgroup_iff_modulus_smul_eq_zero, bytesToG1_valid,
    fun hp hs => bytesToG1_g1ToBytes hp fun _ => hs,
    fun hp hq h => by simp [g1ToBytes, (G1.toAffine_congr hp hq h).2], length_padG1_g1ToBytes,
    fun _ => unpadG1_padG1 (by simp [g1ToBytes, natToBytes_length]), fun _ => rfl, fun _ _ => rfl⟩

private noncomputable def g2Spec : MsmSpec G2 G2.curve.toAffine.Point :=
  ⟨G2.Valid, G2.inSubgroup, G2.toPoint, G2.zero, G2.add, G2.mulNat, bytesToG2, g2ToBytes,
    padG2 ∘ g2ToBytes, unpadG2, 256, bls12G2MsmGas, g2Msm, bls12G2Msm, G2.valid_zero,
    G2.toPoint_zero, G2.valid_add, G2.toPoint_add, G2.valid_mulNat, G2.toPoint_mulNat,
    G2.inSubgroup_iff_modulus_smul_eq_zero, bytesToG2_valid,
    fun hp hs => bytesToG2_g2ToBytes hp fun _ => hs,
    fun hp hq h => by simp [g2ToBytes, (G2.toAffine_congr hp hq h).2], length_padG2_g2ToBytes,
    fun _ => unpadG2_padG2 (by simp [g2ToBytes, natToBytes_length]), fun _ => rfl, fun _ _ => rfl⟩

private theorem points_ok {P Pt} [AddCommMonoid Pt] (C : MsmSpec P Pt) {ps : List (P × Nat)}
    (hp : ∀ pm ∈ ps, C.V pm.1 ∧ C.sub pm.1 = true) :
    let s := ps.foldl (fun s (p, m) => C.add s (C.mul p m)) C.z
    C.V s ∧ C.sub s = true ∧ C.pt s = (ps.map fun (p, m) => m • C.pt p).sum := by
  suffices ∀ {ps : List (P × Nat)} {a : P}, C.V a → C.sub a → (∀ pm ∈ ps, C.V pm.1 ∧ C.sub pm.1) →
      let s := ps.foldl (fun s (p, m) => C.add s (C.mul p m)) a
      C.V s ∧ C.sub s ∧ C.pt s = C.pt a + (ps.map fun (p, m) => m • C.pt p).sum by
    simpa [C.hpz] using this C.hz ((C.hsub C.hz).mpr (by simp [C.hpz])) hp
  intro ps
  induction ps with
  | nil => exact fun hv hs _ => ⟨hv, hs, by simp⟩
  | cons pm rest ih =>
    intro a hv hs hps
    rcases pm with ⟨p, m⟩
    have ⟨hvp, hsp⟩ := hps (p, m) List.mem_cons_self
    have hvm := C.hmul hvp m
    have h1 := (C.hpadd hv hvm).trans (by rw [C.hpmul hvp m])
    obtain ⟨hv', hs', hpt⟩ := ih (C.hadd hv hvm) ((C.hsub (C.hadd hv hvm)).mpr (by
      rw [h1, nsmul_add, (C.hsub hv).mp hs, smul_comm, (C.hsub hvp).mp hsp, nsmul_zero, add_zero]))
      fun q hq => hps q (.tail _ hq)
    exact ⟨hv', hs', by rw [List.foldl_cons, hpt, h1, List.map_cons, List.sum_cons, add_assoc]⟩

private theorem msm_ok {P Pt} [AddCommMonoid Pt] (C : MsmSpec P Pt)
    (ps : List (List UInt8 × List UInt8)) (sum : P) :
    C.msm ps = .ok sum ↔
      ∃ ds : List (P × Nat),
        (ps.mapM fun (r, sc) => do return (← C.dec r true, bytesToNat sc)) = .ok ds ∧
        sum = ds.foldl (fun s (p, m) => C.add s (C.mul p m)) C.z ∧
        ∀ pm ∈ ds, C.V pm.1 ∧ C.sub pm.1 = true := by
  rw [C.hmsm]
  suffices ∀ a, List.foldlM (fun s (r, sc) => do
      return C.add s (C.mul (← C.dec r true) (bytesToNat sc))) a ps = .ok sum ↔
    ∃ ds : List (P × Nat),
      (ps.mapM fun (r, sc) => do return (← C.dec r true, bytesToNat sc)) = .ok ds ∧
      sum = ds.foldl (fun s (p, m) => C.add s (C.mul p m)) a ∧
      ∀ pm ∈ ds, C.V pm.1 ∧ C.sub pm.1 = true from this C.z
  induction ps with
  | nil =>
    intro a
    refine ⟨fun h => ⟨[], rfl, (Except.ok.inj h).symm, by simp⟩, fun ⟨_, h1, h2, _⟩ => ?_⟩
    cases h1
    exact congrArg Except.ok h2.symm
  | cons pm rest ih =>
    intro a
    rcases pm with ⟨r, sc⟩
    rw [List.foldlM_cons]
    simp_rw [mapM_cons_ok, bind_ok_iff]
    cases hp : C.dec r true with
    | error => simp
    | ok p =>
      have hvp : C.V p ∧ C.sub p = true := ⟨(C.hdec hp).1, (C.hdec hp).2 rfl⟩
      simpa [pure, Except.pure, hvp] using ih (C.add a (C.mul p (bytesToNat sc)))

private theorem call_iff {P Pt} [AddCommMonoid Pt] (C : MsmSpec P Pt) (d : ByteArray)
    (g : Nat) (o : ByteArray) :
    C.call d g = .ok o ↔
      d.size ≠ 0 ∧ d.size % (C.pLen + 32) = 0 ∧ C.msmGas (d.size / (C.pLen + 32)) ≤ g ∧ ∃ ps s,
        ((chunks (C.pLen + 32) (d.size / (C.pLen + 32)) d.data.toList).mapM fun c => do
          return (← C.unpad (c.take C.pLen), c.drop C.pLen)) = .ok ps ∧
        C.msm ps = .ok s ∧ o = ⟨(C.pad s).toArray⟩ := by
  rw [C.hcall]
  by_cases hs : d.size = 0 ∨ d.size % (C.pLen + 32) ≠ 0
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hs)]
    rcases hs with h | h <;> simp [h, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hs)]
    dsimp only
    have ⟨hne, hm⟩ := (not_or.mp hs).imp id Decidable.not_not.mp
    by_cases hg : g < C.msmGas (d.size / (C.pLen + 32))
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hg)]
      simp [hne, hm, Nat.not_le.mpr hg, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hg)]
      simp only [bind_ok_iff, pure, Except.pure]
      simp [hne, hm, Nat.not_lt.mp hg, eq_comm]

private theorem encode_ok {P Pt} [AddCommMonoid Pt] (C : MsmSpec P Pt) {ps : List (P × Nat)}
    (hne : ps ≠ []) (hp : ∀ pm ∈ ps, C.V pm.1 ∧ C.sub pm.1 = true ∧ pm.2 < 256 ^ 32) {gas : Nat}
    (hgas : C.msmGas ps.length ≤ gas) :
    C.call ⟨((ps.map fun (p, m) => C.pad p ++ natToBytes 32 m).flatten).toArray⟩ gas =
      .ok ⟨(C.pad (ps.foldl (fun s (p, m) => C.add s (C.mul p m)) C.z)).toArray⟩ := by
  have ⟨qs, hqs, hqv, hmap⟩ : ∃ qs : List (P × Nat),
      ((ps.map fun (p, m) => (C.enc p, natToBytes 32 m)).mapM fun (r, sc) => do
        return (← C.dec r true, bytesToNat sc)) = .ok qs ∧ (∀ qm ∈ qs, C.V qm.1 ∧ C.sub qm.1) ∧
      (qs.map fun (p, m) => m • C.pt p) = ps.map fun (p, m) => m • C.pt p := by
    clear hne hgas
    induction ps with
    | nil => exact ⟨[], rfl, by simp, rfl⟩
    | cons pm rest ih =>
      rcases pm with ⟨p, m⟩
      obtain ⟨hpv, hs, hm⟩ := hp (p, m) List.mem_cons_self
      obtain ⟨q, hq, hqt⟩ := C.hrt hpv hs
      obtain ⟨qs, hpq, hqv, hmp⟩ := ih fun r hr => hp r (.tail _ hr)
      exact ⟨(q, bytesToNat (natToBytes 32 m)) :: qs, mapM_cons_ok.mpr ⟨_, _,
        bind_ok_iff.mpr ⟨q, hq, rfl⟩, hpq, rfl⟩, List.forall_mem_cons.mpr
        ⟨⟨(C.hdec hq).1, (C.hdec hq).2 rfl⟩, hqv⟩,
        by simp [bytesToNat_natToBytes_of_lt hm, hqt, hmp]⟩
  obtain ⟨hv1, -, hpt1⟩ := points_ok C hqv
  obtain ⟨hv2, -, hpt2⟩ := points_ok C fun pm hpm => ⟨(hp pm hpm).1, (hp pm hpm).2.1⟩
  -- Each decoded point may differ from the given one, but the final sums have one affine form.
  rw [← C.hcg hv1 hv2 (by rw [hpt1, hpt2, hmap])]
  let d : ByteArray := ⟨((ps.map fun (p, m) => C.pad p ++ natToBytes 32 m).flatten).toArray⟩
  have ⟨hln, hup⟩ : d.data.toList.length = ps.length * (C.pLen + 32) ∧
      ((chunks (C.pLen + 32) ps.length d.data.toList).mapM fun c => do
        return (← C.unpad (c.take C.pLen), c.drop C.pLen)) =
      .ok (ps.map fun (p, m) => (C.enc p, natToBytes 32 m)) := by
    change ((ps.map _).flatten).length = _ ∧ ((chunks _ _ ((ps.map _).flatten)).mapM _) = _
    clear * -
    induction ps with
    | nil => exact ⟨by simp, rfl⟩
    | cons pm xs ih =>
      rcases pm with ⟨p, m⟩
      obtain ⟨hl, hup⟩ := ih
      have hx : (C.pad p ++ natToBytes 32 m).length = C.pLen + 32 := by
        simp [C.hlen, natToBytes_length]
      refine ⟨by rw [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        Nat.succ_mul, Nat.add_comm, hx, hl], ?_⟩
      rw [List.map_cons, List.flatten_cons, List.length_cons, chunks, List.take_left' hx,
        List.drop_left' hx]
      exact mapM_cons_ok.mpr ⟨_, _, bind_ok_iff.mpr ⟨_,
        by simpa [List.take_left' (C.hlen p)] using C.hun p,
        by simp [List.drop_left' (C.hlen p), pure, Except.pure]⟩, hup, rfl⟩
  have hsz : d.size = ps.length * (C.pLen + 32) := by
    simpa only [Array.length_toList, ByteArray.size] using hln
  have hdv : d.size / (C.pLen + 32) = ps.length := hsz ▸ Nat.mul_div_cancel _ (by omega)
  exact (call_iff C d gas _).mpr ⟨hsz ▸ Nat.mul_ne_zero (Nat.ne_of_gt
    (List.length_pos_iff.mpr hne)) (by omega), hsz ▸ Nat.mul_mod_left _ _, hdv ▸ hgas, _, _,
    hdv ▸ hup, (msm_ok C _ _).mpr ⟨qs, hqs, rfl, hqv⟩, rfl⟩

/-! ## G1MSM and G2MSM -/

/-- `g1Msm` checks that every point lies in the subgroup, and returns their scalar-multiple sum. -/
theorem g1Msm_toPoint {pairs : List (List UInt8 × List UInt8)} {sum : G1}
    (h : g1Msm pairs = .ok sum) : ∃ decoded : List (G1 × Nat),
      (pairs.mapM fun (raw, scalar) => do return (← bytesToG1 raw true, bytesToNat scalar)) =
        .ok decoded ∧ G1.Valid sum ∧ G1.inSubgroup sum = true ∧
      G1.toPoint sum = (decoded.map fun (p, m) => m • G1.toPoint p).sum := by
  obtain ⟨ds, hd, hs, hv⟩ := (msm_ok g1Spec pairs sum).mp h
  exact ⟨ds, hd, hs ▸ points_ok g1Spec hv⟩

/-- G1MSM succeeds on a non-empty multiple of 160 bytes, with at least its price in gas. -/
theorem bls12G1Msm_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12G1Msm data gas = .ok out ↔ data.size ≠ 0 ∧ data.size % LENGTH_PER_PAIR_G1 = 0 ∧
      bls12G1MsmGas (data.size / LENGTH_PER_PAIR_G1) ≤ gas ∧ ∃ pairs sum,
        ((chunks LENGTH_PER_PAIR_G1 (data.size / LENGTH_PER_PAIR_G1) data.data.toList).mapM
          fun pair => do return (← unpadG1 (pair.take 128), pair.drop 128)) = .ok pairs ∧
        g1Msm pairs = .ok sum ∧ out = ⟨(padG1 (g1ToBytes sum)).toArray⟩ :=
  call_iff g1Spec data gas out

/-- A call of G1MSM that succeeds returns the encoding of the subgroup sum of its decoded pairs. -/
theorem bls12G1Msm_toPoint {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12G1Msm data gas = .ok out) : data.size ≠ 0 ∧ data.size % LENGTH_PER_PAIR_G1 = 0 ∧
      bls12G1MsmGas (data.size / LENGTH_PER_PAIR_G1) ≤ gas ∧ ∃ pairs decoded sum,
        ((chunks LENGTH_PER_PAIR_G1 (data.size / LENGTH_PER_PAIR_G1) data.data.toList).mapM
          fun pair => do return (← unpadG1 (pair.take 128), pair.drop 128)) = .ok pairs ∧
        (pairs.mapM fun (raw, scalar) => do return (← bytesToG1 raw true, bytesToNat scalar)) =
          .ok decoded ∧ g1Msm pairs = .ok sum ∧ out = ⟨(padG1 (g1ToBytes sum)).toArray⟩ ∧
        G1.Valid sum ∧ G1.inSubgroup sum = true ∧
        G1.toPoint sum = (decoded.map fun (p, m) => m • G1.toPoint p).sum := by
  obtain ⟨h1, h2, h3, ps, s, hp, hs, ho⟩ := (bls12G1Msm_eq_ok_iff data gas out).mp h
  obtain ⟨ds, hd, hv, hsub, hpt⟩ := g1Msm_toPoint hs
  exact ⟨h1, h2, h3, ps, ds, s, hp, hd, hs, ho, hv, hsub, hpt⟩

/-- `g2Msm` checks that every point lies in the subgroup, and returns their scalar-multiple sum. -/
theorem g2Msm_toPoint {pairs : List (List UInt8 × List UInt8)} {sum : G2}
    (h : g2Msm pairs = .ok sum) : ∃ decoded : List (G2 × Nat),
      (pairs.mapM fun (raw, scalar) => do return (← bytesToG2 raw true, bytesToNat scalar)) =
        .ok decoded ∧ G2.Valid sum ∧ G2.inSubgroup sum = true ∧
      G2.toPoint sum = (decoded.map fun (p, m) => m • G2.toPoint p).sum := by
  obtain ⟨ds, hd, hs, hv⟩ := (msm_ok g2Spec pairs sum).mp h
  exact ⟨ds, hd, hs ▸ points_ok g2Spec hv⟩

/-- G2MSM succeeds on a non-empty multiple of 288 bytes, with at least its price in gas. -/
theorem bls12G2Msm_eq_ok_iff (data : ByteArray) (gas : Nat) (out : ByteArray) :
    bls12G2Msm data gas = .ok out ↔ data.size ≠ 0 ∧ data.size % LENGTH_PER_PAIR_G2 = 0 ∧
      bls12G2MsmGas (data.size / LENGTH_PER_PAIR_G2) ≤ gas ∧ ∃ pairs sum,
        ((chunks LENGTH_PER_PAIR_G2 (data.size / LENGTH_PER_PAIR_G2) data.data.toList).mapM
          fun pair => do return (← unpadG2 (pair.take 256), pair.drop 256)) = .ok pairs ∧
        g2Msm pairs = .ok sum ∧ out = ⟨(padG2 (g2ToBytes sum)).toArray⟩ :=
  call_iff g2Spec data gas out

/-- A call of G2MSM that succeeds returns the encoding of the subgroup sum of its decoded pairs. -/
theorem bls12G2Msm_toPoint {data : ByteArray} {gas : Nat} {out : ByteArray}
    (h : bls12G2Msm data gas = .ok out) : data.size ≠ 0 ∧ data.size % LENGTH_PER_PAIR_G2 = 0 ∧
      bls12G2MsmGas (data.size / LENGTH_PER_PAIR_G2) ≤ gas ∧ ∃ pairs decoded sum,
        ((chunks LENGTH_PER_PAIR_G2 (data.size / LENGTH_PER_PAIR_G2) data.data.toList).mapM
          fun pair => do return (← unpadG2 (pair.take 256), pair.drop 256)) = .ok pairs ∧
        (pairs.mapM fun (raw, scalar) => do return (← bytesToG2 raw true, bytesToNat scalar)) =
          .ok decoded ∧ g2Msm pairs = .ok sum ∧ out = ⟨(padG2 (g2ToBytes sum)).toArray⟩ ∧
        G2.Valid sum ∧ G2.inSubgroup sum = true ∧
        G2.toPoint sum = (decoded.map fun (p, m) => m • G2.toPoint p).sum := by
  obtain ⟨h1, h2, h3, ps, s, hp, hs, ho⟩ := (bls12G2Msm_eq_ok_iff data gas out).mp h
  obtain ⟨ds, hd, hv, hsub, hpt⟩ := g2Msm_toPoint hs
  exact ⟨h1, h2, h3, ps, ds, s, hp, hd, hs, ho, hv, hsub, hpt⟩

/-! ## Every list of subgroup points and scalars -/

/-- On valid subgroup points, `g1MsmPoints` is valid, in the subgroup, and maps to their sum. -/
theorem g1MsmPoints_toPoint {pairs : List (G1 × Nat)}
    (hpairs : ∀ pm ∈ pairs, G1.Valid pm.1 ∧ G1.inSubgroup pm.1 = true) :
    G1.Valid (g1MsmPoints pairs) ∧ G1.inSubgroup (g1MsmPoints pairs) = true ∧
      G1.toPoint (g1MsmPoints pairs) = (pairs.map fun (p, m) => m • G1.toPoint p).sum :=
  points_ok g1Spec hpairs

/-- G1MSM on non-empty encoded subgroup pairs, with enough gas, encodes their subgroup sum. -/
theorem bls12G1Msm_g1ToBytes {pairs : List (G1 × Nat)} (hne : pairs ≠ [])
    (hpairs : ∀ pm ∈ pairs, G1.Valid pm.1 ∧ G1.inSubgroup pm.1 = true ∧ pm.2 < 256 ^ 32)
    {gas : Nat} (hgas : bls12G1MsmGas pairs.length ≤ gas) :
    bls12G1Msm ⟨((pairs.map fun (p, m) => g1MsmPairBytes p m).flatten).toArray⟩ gas =
      .ok ⟨(padG1 (g1ToBytes (g1MsmPoints pairs))).toArray⟩ :=
  encode_ok g1Spec hne hpairs hgas

/-- On valid subgroup points, `g2MsmPoints` is valid, in the subgroup, and maps to their sum. -/
theorem g2MsmPoints_toPoint {pairs : List (G2 × Nat)}
    (hpairs : ∀ pm ∈ pairs, G2.Valid pm.1 ∧ G2.inSubgroup pm.1 = true) :
    G2.Valid (g2MsmPoints pairs) ∧ G2.inSubgroup (g2MsmPoints pairs) = true ∧
      G2.toPoint (g2MsmPoints pairs) = (pairs.map fun (p, m) => m • G2.toPoint p).sum :=
  points_ok g2Spec hpairs

/-- G2MSM on non-empty encoded subgroup pairs, with enough gas, encodes their subgroup sum. -/
theorem bls12G2Msm_g2ToBytes {pairs : List (G2 × Nat)} (hne : pairs ≠ [])
    (hpairs : ∀ pm ∈ pairs, G2.Valid pm.1 ∧ G2.inSubgroup pm.1 = true ∧ pm.2 < 256 ^ 32)
    {gas : Nat} (hgas : bls12G2MsmGas pairs.length ≤ gas) :
    bls12G2Msm ⟨((pairs.map fun (p, m) => g2MsmPairBytes p m).flatten).toArray⟩ gas =
      .ok ⟨(padG2 (g2ToBytes (g2MsmPoints pairs))).toArray⟩ :=
  encode_ok g2Spec hne hpairs hgas

/-! ## The generators -/

/-- G1MSM succeeds on `[(g_1, 2), (g_1, 3)]`, with gas equal to its price.

Its output decodes to `2 • g_1 + 3 • g_1`. -/
theorem exists_bls12G1Msm_ok :
    let pairs : List (G1 × Nat) := [(G1.generator, 2), (G1.generator, 3)]
    let data : ByteArray := ⟨((pairs.map fun (p, m) => g1MsmPairBytes p m).flatten).toArray⟩
    ∃ out raw q, bls12G1Msm data (bls12G1MsmGas 2) = .ok out ∧
      unpadG1 out.data.toList = .ok raw ∧ bytesToG1 raw true = .ok q ∧
      G1.toPoint q = (2 : Nat) • G1.toPoint G1.generator + (3 : Nat) • G1.toPoint G1.generator := by
  have hsg := (G1.inSubgroup_iff_modulus_smul_eq_zero G1.valid_generator).mpr
    G1.modulus_smul_generator
  have hp : ∀ pm ∈ [(G1.generator, 2), (G1.generator, 3)],
      G1.Valid pm.1 ∧ G1.inSubgroup pm.1 = true ∧ pm.2 < 256 ^ 32 := by
    simp [G1.valid_generator, hsg]
  obtain ⟨hv, hs, hpt⟩ := g1MsmPoints_toPoint fun pm h => ⟨(hp pm h).1, (hp pm h).2.1⟩
  obtain ⟨q, hq, hqt⟩ := bytesToG1_g1ToBytes hv fun _ => hs
  refine ⟨_, _, q, bls12G1Msm_g1ToBytes (by decide) hp (Nat.le_refl _),
    unpadG1_padG1 (by simp [g1ToBytes, natToBytes_length]), hq, ?_⟩
  rw [hqt, hpt]
  simp

/-- G2MSM succeeds on `[(g_2, 2), (g_2, 3)]`, with gas equal to its price.

Its output decodes to `2 • g_2 + 3 • g_2`. -/
theorem exists_bls12G2Msm_ok :
    let pairs : List (G2 × Nat) := [(G2.generator, 2), (G2.generator, 3)]
    let data : ByteArray := ⟨((pairs.map fun (p, m) => g2MsmPairBytes p m).flatten).toArray⟩
    ∃ out raw q, bls12G2Msm data (bls12G2MsmGas 2) = .ok out ∧
      unpadG2 out.data.toList = .ok raw ∧ bytesToG2 raw true = .ok q ∧
      G2.toPoint q = (2 : Nat) • G2.toPoint G2.generator + (3 : Nat) • G2.toPoint G2.generator := by
  have hp : ∀ pm ∈ [(G2.generator, 2), (G2.generator, 3)],
      G2.Valid pm.1 ∧ G2.inSubgroup pm.1 = true ∧ pm.2 < 256 ^ 32 := by
    simp [G2.valid_generator, G2.inSubgroup_generator]
  obtain ⟨hv, hs, hpt⟩ := g2MsmPoints_toPoint fun pm h => ⟨(hp pm h).1, (hp pm h).2.1⟩
  obtain ⟨q, hq, hqt⟩ := bytesToG2_g2ToBytes hv fun _ => hs
  refine ⟨_, _, q, bls12G2Msm_g2ToBytes (by decide) hp (Nat.le_refl _),
    unpadG2_padG2 (by simp [g2ToBytes, natToBytes_length]), hq, ?_⟩
  rw [hqt, hpt]
  simp

end EthLib.Execution.Evm.Precompiles.Bls12381
