module

public import EthLib.Cryptography.Secp256k1.Recovery
public import EthLib.Cryptography.Proofs.Secp256k1.Ecdsa
public import EthLib.Cryptography.Proofs.Secp256k1.Encoding

/-!
# Proofs: public key recovery

- `verify_recover`: a recovered key verifies the signature.
- `recover_sign`: recovery returns the key of the signer, with the parity of `R` as the id.
- `recover_of_verify`: every key that verifies a signature is recovered by one of the two ids, when `r + n >= p`.
- `recover_neg_s`: replacing `s` by `n - s` swaps the two ids, the malleability EIP-2 removes.
- `recover_ne`: the two ids give two different keys.

The bound `r + n >= p` of `recover_of_verify` covers every `r` but the smallest `p - n`, about `2^128` of the `2^256`.

Below it, `R` could have `x = r + n`, which only the ids 2 and 3 reach, and Ethereum does not use them.
-/

@[expose] public section

namespace EthLib.Cryptography.Secp256k1

namespace Ecdsa

open Point

/-- A field element below `n` read back as an integer, since `n < p`. -/
private theorem val_ofNat_of_lt {r : Nat} (hr : r < Fn.modulus) : (Fin.ofNat Fp.modulus r : Fp).val = r :=
  Nat.mod_eq_of_lt (Nat.lt_trans hr (by decide))

/-- A nonzero scalar is a unit in `ZMod n`. -/
private theorem toZMod_ne_zero {a : Fn} (h : a ≠ 0) : Fn.toZMod a ≠ 0 :=
  fun h0 => h (Fn.toZMod.injective (h0.trans (map_zero _).symm))

/-- The point recovery computes, in the group: `r^(-1) s R - r^(-1) e G`. -/
private theorem toPoint_recovered (rInv sF e : Fn) {R : Point} (hR : R.isOnCurve = true) :
    toPoint (mul (rInv * sF) R + mul (-(rInv * e)) generator)
      = (Fn.toZMod rInv * Fn.toZMod sF) • toPoint R - (Fn.toZMod rInv * Fn.toZMod e) • toPoint generator := by
  rw [toPoint_add (isOnCurve_mul _ hR) (isOnCurve_mul _ isOnCurve_generator), toPoint_mul' _ hR,
    toPoint_mul' _ isOnCurve_generator, map_mul, map_neg, map_mul, neg_smul, sub_eq_add_neg]

/-- `recover` in steps: the ranges, then the point `R`, then the key. -/
private theorem recover_eq (hash : Vector UInt8 32) (r s : Nat) (id : Fin 2) (hr : 0 < r ∧ r < Fn.modulus)
    (hs : 0 < s ∧ s < Fn.modulus) :
    recover hash r s id = (decompress (Fin.ofNat _ r) (id == 1)).bind fun R =>
      if mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) R + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator
          = .infinity then .error .pointAtInfinity
      else .ok (mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) R
        + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator) := by
  rw [recover, dite_eq_left hr, dite_eq_left hs]
  rfl

/-- A recovery fails outside the ranges `[1, n - 1]`. -/
theorem recover_range {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : (0 < r ∧ r < Fn.modulus) ∧ (0 < s ∧ s < Fn.modulus) := by
  unfold recover at h
  split at h
  · split at h
    · exact ⟨by assumption, by assumption⟩
    · cases h
  · cases h

/-- A recovered key is on the curve and is not `O`. -/
theorem recover_valid {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : q.isOnCurve = true ∧ q ≠ .infinity := by
  obtain ⟨hr, hs⟩ := recover_range h
  rw [recover_eq hash r s id hr hs] at h
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rw [hd] at h; cases h
  | ok R =>
    rw [hd] at h
    simp only [Except.bind] at h
    obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
    split_ifs at h with hne
    obtain rfl := Except.ok.inj h
    exact ⟨isOnCurve_add (isOnCurve_mul _ hc) (isOnCurve_mul _ isOnCurve_generator), hne⟩

/-- Soundness of recovery: a recovered key verifies the signature. -/
theorem verify_recover {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : verify q hash r s = true := by
  obtain ⟨hr, hs⟩ := recover_range h
  obtain ⟨hqc, hqi⟩ := recover_valid h
  rw [recover_eq hash r s id hr hs] at h
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rw [hd] at h; cases h
  | ok R =>
    rw [hd] at h
    simp only [Except.bind] at h
    obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
    split_ifs at h with hne
    obtain rfl := Except.ok.inj h
    · rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left ⟨hqi, hqc⟩]
      dsimp only
      have hG := isOnCurve_generator
      -- The verifier rebuilds `R`: `e s^(-1) G + r s^(-1) (r^(-1) s R - r^(-1) e G) = R`.
      have hrebuilt : toPoint (mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨s, hs.2⟩) generator
          + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) (mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) (.affine (Fin.ofNat _ r) y)
            + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator))
          = toPoint (.affine (Fin.ofNat _ r) y) := by
        have hr0 : Fn.toZMod ⟨r, hr.2⟩ ≠ 0 := toZMod_ne_zero (fun h0 => by
          have := congrArg Fin.val h0; simp at this; omega)
        have hs0 : Fn.toZMod ⟨s, hs.2⟩ ≠ 0 := toZMod_ne_zero (fun h0 => by
          have := congrArg Fin.val h0; simp at this; omega)
        rw [toPoint_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc), toPoint_mul' _ hG, toPoint_mul' _ hqc,
          toPoint_recovered _ _ _ hc]
        simp only [map_mul, Fn.toZMod_inv, smul_sub, smul_smul]
        -- Collect the two coefficients: `0` on `G`, `1` on `R`.
        have hA : Fn.toZMod (Fin.ofNat _ (hashToInt hash)) * (Fn.toZMod ⟨s, hs.2⟩)⁻¹
            = Fn.toZMod ⟨r, hr.2⟩ * (Fn.toZMod ⟨s, hs.2⟩)⁻¹
              * ((Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod (Fin.ofNat _ (hashToInt hash))) := by
          field_simp
        have hB : Fn.toZMod ⟨r, hr.2⟩ * (Fn.toZMod ⟨s, hs.2⟩)⁻¹ * ((Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod ⟨s, hs.2⟩) = 1 := by
          field_simp
        rw [hA, hB, one_smul]
        abel
      split
      · rename_i heq
        rw [heq, toPoint_infinity] at hrebuilt
        exact absurd ((toPoint_eq_zero hc).mp hrebuilt.symm) (by simp)
      · rename_i x' y' heq
        rw [heq] at hrebuilt
        have := (toPoint_inj (heq ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)) hc).mp hrebuilt
        cases this
        simp only [beq_iff_eq]
        rw [val_ofNat_of_lt hr.2, Nat.mod_eq_of_lt hr.2]

/-- Recovery returns `q` once `R` is found and the computed key is `q`, in the group. -/
private theorem recover_of_decompress {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2}
    (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus) {R q : Point}
    (hd : decompress (Fin.ofNat _ r) (id == 1) = .ok R) (hq : q.isOnCurve = true) (hqi : q ≠ .infinity)
    (heq : (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod ⟨s, hs.2⟩) • toPoint R
      - (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod (Fin.ofNat _ (hashToInt hash))) • toPoint generator = toPoint q) :
    recover hash r s id = .ok q := by
  obtain ⟨y, rfl, hc, -⟩ := decompress_eq_ok_iff.mp hd
  have hpt : mul (Fn.inv ⟨r, hr.2⟩ * ⟨s, hs.2⟩) (.affine (Fin.ofNat _ r) y)
      + mul (-(Fn.inv ⟨r, hr.2⟩ * Fin.ofNat _ (hashToInt hash))) generator = q :=
    (toPoint_inj (isOnCurve_add (isOnCurve_mul _ hc) (isOnCurve_mul _ isOnCurve_generator)) hq).mp
      ((toPoint_recovered _ _ _ hc).trans heq)
  rw [recover_eq hash r s id hr hs, hd]
  simp only [Except.bind]
  rw [hpt, ite_eq_right hqi]

/-- `d G` is not `O` when `d != 0`, since `G` has order `n`. -/
theorem mul_generator_ne_infinity {d : Fn} (hd : d ≠ 0) : mul d generator ≠ .infinity := by
  intro h
  have h0 := congrArg toPoint h
  rw [toPoint_mul' d isOnCurve_generator, toPoint_infinity, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact toZMod_ne_zero hd h0
  · exact toPoint_generator_ne_zero h0

/-- The recovery id of a point: the parity of its `y`. -/
def parityId (y : Fp) : Fin 2 := if y.val % 2 = 1 then 1 else 0

private theorem parityId_beq (y : Fp) : (parityId y == 1) = decide (y.val % 2 = 1) := by
  unfold parityId
  split <;> simp_all

/-- Completeness of recovery: the signer's key comes back.

The signer has the key `d` and the nonce `k`, and `R = k G` has coordinates `(x, y)` with `x < n`.

Then `r = x`, `s = k^(-1) (e + r d)`, and the id is the parity of `y`. -/
theorem recover_sign (d k : Fn) (hash : Vector UInt8 32) (hd : d ≠ 0) {x y : Fp}
    (hR : mul k generator = .affine x y) (hx : x.val < Fn.modulus) (hx0 : x.val ≠ 0)
    (hs : k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d) ≠ 0) :
    recover hash x.val (k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d)).val (parityId y)
      = .ok (mul d generator) := by
  set sig := k.inv * (Fin.ofNat _ (hashToInt hash) + Fin.ofNat _ x.val * d) with hsig
  have hG := isOnCurve_generator
  have hrr : 0 < x.val ∧ x.val < Fn.modulus := ⟨Nat.pos_of_ne_zero hx0, hx⟩
  have hss : 0 < sig.val ∧ sig.val < Fn.modulus := ⟨Nat.pos_of_ne_zero (fun h => hs (Fin.ext h)), sig.isLt⟩
  have hk : k ≠ 0 := by
    rintro rfl
    apply hs
    apply Fn.toZMod.injective
    rw [hsig, map_mul, Fn.toZMod_inv, map_zero, inv_zero, zero_mul]
  -- `R` is the point with `x` and the parity of `y`.
  have hxx : (Fin.ofNat _ x.val : Fp) = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
  have hd' : decompress (Fin.ofNat _ x.val) (parityId y == 1) = .ok (.affine x y) := by
    rw [hxx, parityId_beq]
    exact decompress_eq_ok_iff.mpr ⟨y, rfl, hR ▸ isOnCurve_mul k hG, rfl⟩
  refine recover_of_decompress hrr hss hd' (isOnCurve_mul d hG) (mul_generator_ne_infinity hd) ?_
  -- `r^(-1) (s k G - e G) = r^(-1) (r d) G = d G`, since `s k = e + r d`.
  rw [← hR, toPoint_mul' k hG, toPoint_mul' d hG, smul_smul, ← sub_smul, Fin.eta sig hss.2]
  refine congrArg (· • toPoint generator) ?_
  have hr' : Fn.toZMod ⟨x.val, hrr.2⟩ = Fn.toZMod (Fin.ofNat _ x.val) :=
    congrArg Fn.toZMod (Fin.ext (Nat.mod_eq_of_lt hx).symm)
  have hr0 : Fn.toZMod (Fin.ofNat Fn.modulus x.val) ≠ 0 := by
    rw [← hr']
    exact toZMod_ne_zero (fun h0 => hx0 (by have h1 := congrArg Fin.val h0; rwa [Fin.val_zero] at h1))
  have hk0 := toZMod_ne_zero hk
  simp only [Fn.toZMod_inv, hr', hsig, map_mul, map_add]
  field_simp
  ring

/-- What a valid signature gives: the ranges, a valid key, and the rebuilt point `R` with `x_R mod n = r`. -/
theorem verify_rebuilt {q : Point} {hash : Vector UInt8 32} {r s : Nat} (hv : verify q hash r s = true) :
    ∃ (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus), q ≠ .infinity ∧ q.isOnCurve = true ∧
      ∃ x y : Fp, mul (Fin.ofNat _ (hashToInt hash) * Fn.inv ⟨s, hs.2⟩) generator
        + mul ((⟨r, hr.2⟩ : Fn) * Fn.inv ⟨s, hs.2⟩) q = .affine x y ∧ x.val % Fn.modulus = r := by
  obtain ⟨hr, hs⟩ := verify_range hv
  have hq : q ≠ .infinity ∧ q.isOnCurve = true := by
    by_cases hi : q = .infinity
    · subst hi; rw [verify_infinity] at hv; cases hv
    · cases hc : q.isOnCurve
      · rw [verify_of_not_isOnCurve hc] at hv; cases hv
      · exact ⟨hi, rfl⟩
  refine ⟨hr, hs, hq.1, hq.2, ?_⟩
  rw [verify, dite_eq_left hr, dite_eq_left hs, ite_eq_left hq] at hv
  dsimp only at hv
  split at hv
  · cases hv
  · rename_i x y hR
    exact ⟨x, y, hR, by simpa using hv⟩

/-- Completeness of recovery: a key that verifies a signature is recovered by one of the two ids.

The bound `p <= r + n` makes `x_R = r`: the other candidate `r + n` is not below `p`. -/
theorem recover_of_verify {q : Point} {hash : Vector UInt8 32} {r s : Nat} (hv : verify q hash r s = true)
    (hp : Fp.modulus ≤ r + Fn.modulus) : ∃ id : Fin 2, recover hash r s id = .ok q := by
  obtain ⟨hr, hs, hqi, hqc, x, y, hR, hx⟩ := verify_rebuilt hv
  have hG := isOnCurve_generator
  have hr0 : Fn.toZMod ⟨r, hr.2⟩ ≠ 0 :=
    toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
  have hs0 : Fn.toZMod ⟨s, hs.2⟩ ≠ 0 :=
    toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
  -- `x_R = r`, since `x_R = r mod n` and `x_R < p <= r + n`.
  have hxr : x.val = r := by
    have hdiv := Nat.mod_add_div x.val Fn.modulus
    have hlt := x.isLt
    by_cases h0 : x.val / Fn.modulus = 0
    · rw [h0, Nat.mul_zero, Nat.add_zero] at hdiv
      omega
    · have := Nat.le_mul_of_pos_right Fn.modulus (Nat.pos_of_ne_zero h0)
      omega
  have hxx : (Fin.ofNat _ r : Fp) = x := Fin.ext (by rw [Fin.val_ofNat, ← hxr, Nat.mod_eq_of_lt x.isLt])
  have hRc : (Point.affine x y).isOnCurve = true := hR ▸ isOnCurve_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc)
  refine ⟨parityId y, recover_of_decompress (R := .affine x y) hr hs ?_ hqc hqi ?_⟩
  · rw [hxx, parityId_beq]
    exact decompress_eq_ok_iff.mpr ⟨y, rfl, hRc, rfl⟩
  · -- `r^(-1) (s R - e G) = Q`, since `s R = e G + r Q`.
    rw [← hR, toPoint_add (isOnCurve_mul _ hG) (isOnCurve_mul _ hqc), toPoint_mul' _ hG, toPoint_mul' _ hqc]
    simp only [map_mul, Fn.toZMod_inv, smul_add, smul_smul]
    have hA : (Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod ⟨s, hs.2⟩ * (Fn.toZMod (Fin.ofNat _ (hashToInt hash))
        * (Fn.toZMod ⟨s, hs.2⟩)⁻¹) = (Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod (Fin.ofNat _ (hashToInt hash)) := by
      field_simp
    have hB : (Fn.toZMod ⟨r, hr.2⟩)⁻¹ * Fn.toZMod ⟨s, hs.2⟩ * (Fn.toZMod ⟨r, hr.2⟩ * (Fn.toZMod ⟨s, hs.2⟩)⁻¹) = 1 := by
      field_simp
    rw [hA, hB, one_smul]
    abel

/-- What a recovery gives: the point `R` with `x = r` and the parity of the id, and the key `r^(-1) (s R - e G)`. -/
private theorem recover_spec {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) :
    ∃ (hr : 0 < r ∧ r < Fn.modulus) (hs : 0 < s ∧ s < Fn.modulus) (y : Fp),
      decompress (Fin.ofNat _ r) (id == 1) = .ok (.affine (Fin.ofNat _ r) y)
      ∧ (Point.affine (Fin.ofNat _ r) y).isOnCurve = true ∧ decide (y.val % 2 = 1) = (id == 1)
      ∧ toPoint q = (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod ⟨s, hs.2⟩) • toPoint (.affine (Fin.ofNat _ r) y)
        - (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod (Fin.ofNat _ (hashToInt hash))) • toPoint generator := by
  obtain ⟨hr, hs⟩ := recover_range h
  rw [recover_eq hash r s id hr hs] at h
  cases hd : decompress (Fin.ofNat _ r) (id == 1) with
  | error e => rw [hd] at h; cases h
  | ok R =>
    rw [hd] at h
    simp only [Except.bind] at h
    obtain ⟨y, rfl, hc, hpar⟩ := decompress_eq_ok_iff.mp hd
    split_ifs at h
    obtain rfl := Except.ok.inj h
    refine ⟨hr, hs, y, rfl, hc, hpar, ?_⟩
    exact toPoint_recovered (Fn.inv ⟨r, hr.2⟩) ⟨s, hs.2⟩ (Fin.ofNat _ (hashToInt hash)) hc

/-- A point of the curve has `y != 0`: `-7` is not a cube. -/
private theorem y_ne_zero {x y : Fp} (h : (Point.affine x y).isOnCurve = true) : y ≠ 0 := by
  rintro rfl
  have h0 := (isOnCurve_affine x 0).mp h
  exact cube_ne_neg_seven (Fp.toZMod x) (by rw [Fp.toZMod_zero] at h0; linear_combination -h0)

/-- `n - s` is `-s` mod `n`. -/
private theorem toZMod_sub_eq_neg {s : Nat} (hs : 0 < s ∧ s < Fn.modulus) (hs' : Fn.modulus - s < Fn.modulus) :
    Fn.toZMod ⟨Fn.modulus - s, hs'⟩ = -Fn.toZMod ⟨s, hs.2⟩ := by
  rw [← Fn.toZMod_neg]
  exact congrArg Fn.toZMod (Fin.ext (by simp only [Fin.neg_def]; exact (Nat.mod_eq_of_lt hs').symm))

/-- Replacing `s` by `n - s` swaps the recovery ids, and the key stays the same.

This is the malleability EIP-2 removes: the flipped signature, with the flipped id, still names the sender. -/
theorem recover_neg_s {hash : Vector UInt8 32} {r s : Nat} {id : Fin 2} {q : Point}
    (h : recover hash r s id = .ok q) : recover hash r (Fn.modulus - s) (1 - id) = .ok q := by
  obtain ⟨hqc, hqi⟩ := recover_valid h
  obtain ⟨hr, hs, y, -, hc, hpar, hq⟩ := recover_spec h
  have hs' : 0 < Fn.modulus - s ∧ Fn.modulus - s < Fn.modulus := by omega
  -- The other id picks `-R = (x, -y)`, whose `y` has the other parity.
  have hflip : ((1 - id) == 1) = !(id == 1) := by fin_cases id <;> rfl
  have hneg := Fp.val_neg_mod_two (y_ne_zero hc)
  have hd : decompress (Fin.ofNat _ r) ((1 - id) == 1) = .ok (.affine (Fin.ofNat _ r) (-y)) := by
    refine decompress_eq_ok_iff.mpr ⟨-y, rfl, isOnCurve_neg hc, ?_⟩
    rw [hflip, ← hpar]
    have h2 := Nat.mod_two_eq_zero_or_one y.val
    have h2' := Nat.mod_two_eq_zero_or_one (-y).val
    rcases h2 with h2 | h2 <;> simp [h2] <;> omega
  refine recover_of_decompress hr hs' hd hqc hqi ?_
  -- `(-s) (-R) = s R`.
  rw [hq, show (Point.affine (Fin.ofNat _ r) (-y)) = -(Point.affine (Fin.ofNat _ r) y) from rfl, toPoint_neg hc,
    toZMod_sub_eq_neg hs hs'.2, smul_neg, mul_neg, neg_smul, neg_neg]

/-- The two recovery ids give two different keys.

Their difference is `2 r^(-1) s R`, which is not `O`: `R` is not `O`, and `2 r^(-1) s != 0` mod `n`. -/
theorem recover_ne {hash : Vector UInt8 32} {r s : Nat} {q0 q1 : Point} (h0 : recover hash r s 0 = .ok q0)
    (h1 : recover hash r s 1 = .ok q1) : q0 ≠ q1 := by
  obtain ⟨hr, hs, y0, -, hc0, hpar0, hq0⟩ := recover_spec h0
  obtain ⟨hr', hs', y1, -, hc1, hpar1, hq1⟩ := recover_spec h1
  intro heq
  subst heq
  -- `y1 = -y0`: same `x`, other parity.
  have hy : y1 = -y0 := by
    rcases Fp.eq_or_eq_neg_of_mul_self (((isOnCurve_affine _ _).mp hc1).trans ((isOnCurve_affine _ _).mp hc0).symm)
      with h | h
    · have := Fp.toZMod.injective h
      subst this
      simp at hpar0 hpar1
      omega
    · exact Fp.toZMod.injective (h.trans (Fp.toZMod_neg y0).symm)
  subst hy
  rw [show (Point.affine (Fin.ofNat _ r) (-y0)) = -(Point.affine (Fin.ofNat _ r) y0) from rfl, toPoint_neg hc0,
    hq0] at hq1
  -- The two keys agree only if `2 r^(-1) s R = O`.
  have h2 : ((2 : ZMod Fn.modulus) * (Fn.toZMod (Fn.inv ⟨r, hr.2⟩) * Fn.toZMod ⟨s, hs.2⟩))
      • toPoint (.affine (Fin.ofNat _ r) y0) = 0 := by
    rw [mul_smul, two_smul]
    rw [smul_neg] at hq1
    linear_combination (norm := module) hq1
  rcases smul_eq_zero.mp h2 with h2 | h2
  · have hr0 : Fn.toZMod ⟨r, hr.2⟩ ≠ 0 :=
      toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
    have hs0 : Fn.toZMod ⟨s, hs.2⟩ ≠ 0 :=
      toZMod_ne_zero (fun h0 => by have h1 := congrArg Fin.val h0; simp at h1; omega)
    rw [Fn.toZMod_inv] at h2
    simp only [mul_eq_zero, inv_eq_zero, hr0, hs0, or_false] at h2
    exact absurd h2 (by decide)
  · exact absurd ((toPoint_eq_zero hc0).mp h2) (by simp)

end Ecdsa

end EthLib.Cryptography.Secp256k1
