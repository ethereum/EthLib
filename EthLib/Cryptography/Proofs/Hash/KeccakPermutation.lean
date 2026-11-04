module

public import EthLib.Cryptography.Proofs.Hash.Keccak
public import Mathlib.Tactic

/-!
# Proofs: Keccak-f[1600] is a permutation

FIPS 202 §3 builds Keccak-f[1600] from five step mappings, each invertible.

This file proves each of them injective, then the whole permutation bijective.

Rho, pi, chi and iota act on single lanes or rows, so a check per bit settles them.

Theta is the hard case: it adds to each lane the parities of two columns.

On column parities it is the map `c ↦ c + y c + z y⁻¹ c` over GF(2).

Here `y` moves each column parity to the next column, and `z` rotates a lane by one bit.

Squaring is additive over GF(2), so 64 applications give `1 + y⁶⁴ + z⁶⁴ y⁻⁶⁴`.

As `z⁶⁴ = 1` and `y⁵ = 1`, that is `1 + y + y⁴`, which mixes columns without rotating.

It is injective, so theta is too.
-/

@[expose] public section

namespace EthLib.Cryptography.Hash.Keccak

/-! ## Rotations -/

/-- Bit `i` of a lane rotated by `n` is bit `i - n` of the lane, mod 64. -/
theorem getLsbD_rotl (v n : UInt64) (hn : n.toNat ≤ 64) (i : Nat) (hi : i < 64) :
    (rotl v n).toBitVec.getLsbD i = v.toBitVec.getLsbD ((i + 64 - n.toNat % 64) % 64) := by
  unfold rotl
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    BitVec.getLsbD_or]
  simp [hi]
  rw [show (18446744073709551616 - n.toNat) % 64 = (64 - n.toNat % 64) % 64 by omega]
  generalize hk : n.toNat % 64 = k
  have k64 : k < 64 := by omega
  by_cases h0 : k = 0
  · subst h0
    simp [Nat.mod_eq_of_lt hi, BitVec.getLsbD_eq_getElem, hi]
  by_cases hlt : i < k
  · rw [Nat.mod_eq_of_lt (by omega : 64 - k < 64), Nat.mod_eq_of_lt (by omega : i + 64 - k < 64)]
    rw [show 64 - k + i = i + 64 - k by omega]
    simp [hlt]
  · rw [Nat.mod_eq_of_lt (by omega : 64 - k < 64), BitVec.getLsbD_of_ge _ _ (by omega)]
    rw [show (i + 64 - k) % 64 = i - k by omega]
    simp [hlt, BitVec.getLsbD_eq_getElem, (by omega : i - k < 64)]

/-- Two lanes are equal when all their 64 bits are. -/
theorem lane_ext {v w : UInt64} (h : ∀ i < 64, v.toBitVec.getLsbD i = w.toBitVec.getLsbD i) :
    v = w :=
  UInt64.toBitVec_inj.1 (BitVec.eq_of_getLsbD_eq h)

/-- A rotation by at most 64 bits loses no bit. -/
theorem rotl_injective {n : UInt64} (hn : n.toNat ≤ 64) : Function.Injective (rotl · n) := by
  intro v w h
  refine lane_ext fun i hi => ?_
  -- Bit `i` of the lane is bit `i + n` of its rotation.
  have := congrArg (fun u : UInt64 => u.toBitVec.getLsbD ((i + n.toNat) % 64)) h
  simp only [getLsbD_rotl _ _ hn _ (Nat.mod_lt _ (by omega))] at this
  rwa [show ((i + n.toNat) % 64 + 64 - n.toNat % 64) % 64 = i by omega] at this

/-- A rotation distributes over XOR. -/
theorem rotl_xor (v w n : UInt64) (hn : n.toNat ≤ 64) :
    rotl (v ^^^ w) n = rotl v n ^^^ rotl w n :=
  lane_ext fun i hi => by
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor, getLsbD_rotl _ _ hn _ hi]

/-- Two rotations by `s` make one rotation by `2s`. -/
theorem rotl_rotl (v s : UInt64) (hs : s.toNat ≤ 32) : rotl (rotl v s) s = rotl v (s + s) := by
  have hss : (s + s).toNat = s.toNat + s.toNat := by
    rw [UInt64.toNat_add]
    omega
  refine lane_ext fun i hi => ?_
  rw [getLsbD_rotl _ _ (by omega) _ hi, getLsbD_rotl _ _ (by omega) _ (Nat.mod_lt _ (by omega)),
    getLsbD_rotl _ _ (by omega) _ hi, hss]
  congr 1
  omega

/-- A rotation by 64 bits is the identity. -/
theorem rotl_sixtyFour (v : UInt64) : rotl v 64 = v :=
  lane_ext fun i hi => by
    rw [getLsbD_rotl _ _ (by decide) _ hi]
    congr 1
    simp only [UInt64.reduceToNat]
    omega

/-! ## XOR of lanes -/

/-- Three pairs cancel in a sum of nine lanes. -/
theorem xor_three_pairs (a b c d e f : UInt64) :
    (a ^^^ b ^^^ c) ^^^ (b ^^^ d ^^^ e) ^^^ (c ^^^ e ^^^ f) = a ^^^ d ^^^ f :=
  lane_ext fun i _ => by
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    generalize a.toBitVec.getLsbD i = a'
    generalize b.toBitVec.getLsbD i = b'
    generalize c.toBitVec.getLsbD i = c'
    generalize d.toBitVec.getLsbD i = d'
    generalize e.toBitVec.getLsbD i = e'
    generalize f.toBitVec.getLsbD i = f'
    revert a' b' c' d' e' f'
    decide

/-- XOR one lane into all five lanes of a column, and the column's parity changes by it once. -/
theorem xor_five (a b c d e t : UInt64) :
    (a ^^^ t) ^^^ (b ^^^ t) ^^^ (c ^^^ t) ^^^ (d ^^^ t) ^^^ (e ^^^ t) =
      (a ^^^ b ^^^ c ^^^ d ^^^ e) ^^^ t :=
  lane_ext fun i _ => by
    simp only [UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    generalize a.toBitVec.getLsbD i = a'
    generalize b.toBitVec.getLsbD i = b'
    generalize c.toBitVec.getLsbD i = c'
    generalize d.toBitVec.getLsbD i = d'
    generalize e.toBitVec.getLsbD i = e'
    generalize t.toBitVec.getLsbD i = t'
    revert a' b' c' d' e' t'
    decide

/-! ## Lanes -/

/-- Each lane of a state built from lanes is the lane it was given. -/
theorem lane_ofLanes (f : Fin 5 → Fin 5 → UInt64) (x y : Fin 5) :
    (State.ofLanes f).lane x y = f x y := by
  fin_cases x <;> fin_cases y <;> rfl

/-- A state is the state built from its own lanes. -/
theorem ofLanes_lane (A : State) : State.ofLanes A.lane = A := by
  cases A
  rfl

/-- Two states with the same lanes are equal. -/
theorem State.ext_lane {A B : State} (h : ∀ x y, A.lane x y = B.lane x y) : A = B := by
  rw [← ofLanes_lane A, ← ofLanes_lane B]
  exact congrArg State.ofLanes (funext fun x => funext (h x))

/-- Two states built from lanes are equal only when their lanes are. -/
theorem ofLanes_inj {f g : Fin 5 → Fin 5 → UInt64} (h : State.ofLanes f = State.ofLanes g)
    (x y : Fin 5) : f x y = g x y := by
  rw [← lane_ofLanes f, ← lane_ofLanes g, h]

/-! ## Rho, pi, chi and iota -/

/-- Each rotation offset is at most 64. -/
theorem RHO_le (k : Nat) (hk : k < LANES) : (RHO[k]'hk).toNat ≤ 64 := by
  simp only [LANES] at hk
  revert k
  decide

/-- Rho is injective. -/
theorem rho_injective : Function.Injective rho := by
  intro A B h
  rw [rho_eq, rho_eq] at h
  exact State.ext_lane fun x y => rotl_injective (RHO_le _ _) (ofLanes_inj h x y)

/-- Pi is injective: output lane `(x, y)` reads input lane `(x + 3y, x)`, one to one. -/
theorem pi_injective : Function.Injective pi := by
  intro A B h
  rw [pi_eq, pi_eq] at h
  refine State.ext_lane fun u v => ?_
  -- Lane `(u, v)` moves to `(v, 2 (u - v))`, since `3 * 2 = 1` mod 5.
  have hinv : v + 3 * (2 * (u - v)) = u := by
    revert u v
    decide
  have := ofLanes_inj h v (2 * (u - v))
  rwa [hinv] at this

/-- Chi on one bit of a row of five lanes is injective. -/
theorem chi_bits_injective (p q : Fin 5 → Bool)
    (h : ∀ x, (p x ^^ (!p (x + 1) && p (x + 2))) = (q x ^^ (!q (x + 1) && q (x + 2)))) :
    p = q := by
  revert p q
  decide

/-- Chi is injective: it acts on each row of five lanes bit by bit, and is injective there. -/
theorem chi_injective : Function.Injective chi := by
  intro A B h
  rw [chi_eq, chi_eq] at h
  refine State.ext_lane fun x y => lane_ext fun i hi => ?_
  -- One bit of one row: five equations between two words of five bits.
  have row := chi_bits_injective (fun x => (A.lane x y).toBitVec.getLsbD i)
    (fun x => (B.lane x y).toBitVec.getLsbD i) fun x => by
      have := congrArg (fun u : UInt64 => u.toBitVec.getLsbD i) (ofLanes_inj h x y)
      simpa [UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not, hi] using this
  exact congrFun row x

/-- Iota is injective: it XORs a constant into one lane. -/
theorem iota_injective (ir : Fin ROUNDS) : Function.Injective (iota ir) := by
  intro A B h
  rw [iota_eq, iota_eq] at h
  refine State.ext_lane fun x y => ?_
  have := ofLanes_inj h x y
  split at this
  · exact (UInt64.xor_left_inj _).1 this
  · exact this

/-! ## Theta -/

/-- A map on column parities: `c[x] + c[x + α] + rot(c[x + β], s)`.

Theta acts on column parities as the case `α = -1`, `β = 1`, `s = 1`. -/
def columnStep (α β : Fin 5) (s : UInt64) (c : Fin 5 → UInt64) : Fin 5 → UInt64 :=
  fun x => c x ^^^ c (x + α) ^^^ rotl (c (x + β)) s

/-- Applying the map twice doubles the offsets and the rotation, as squaring over GF(2) does. -/
theorem columnStep_columnStep (α β : Fin 5) (s : UInt64) (hs : s.toNat ≤ 32)
    (c : Fin 5 → UInt64) :
    columnStep α β s (columnStep α β s c) = columnStep (α + α) (β + β) (s + s) c := by
  funext x
  simp only [columnStep]
  rw [rotl_xor _ _ _ (by omega), rotl_xor _ _ _ (by omega), rotl_rotl _ _ hs,
    add_assoc x α α, add_assoc x β β, add_right_comm x β α]
  exact xor_three_pairs _ _ _ _ _ _

/-- If the square of the map is injective, so is the map. -/
theorem columnStep_injective_of_sq {α β : Fin 5} {s : UInt64} (hs : s.toNat ≤ 32)
    (h : Function.Injective (columnStep (α + α) (β + β) (s + s))) :
    Function.Injective (columnStep α β s) := fun c d hcd =>
  h (by rw [← columnStep_columnStep _ _ _ hs, ← columnStep_columnStep _ _ _ hs, hcd])

/-- The map `1 + y + y⁴` on one bit of each column parity is injective. -/
theorem mix_bits_injective (p q : Fin 5 → Bool)
    (h : ∀ x, (p x ^^ p (x + 1) ^^ p (x + 4)) = (q x ^^ q (x + 1) ^^ q (x + 4))) : p = q := by
  revert p q
  decide

/-- The 64th power of theta's map on column parities is injective. -/
theorem columnStep_sixtyFour_injective : Function.Injective (columnStep 1 4 64) := by
  intro c d h
  funext x
  refine lane_ext fun i hi => ?_
  have bits := mix_bits_injective (fun x => (c x).toBitVec.getLsbD i)
    (fun x => (d x).toBitVec.getLsbD i) fun x => by
      have := congrArg (fun u : UInt64 => u.toBitVec.getLsbD i) (congrFun h x)
      simpa [columnStep, rotl_sixtyFour, UInt64.toBitVec_xor] using this
  exact congrFun bits x

/-- Theta's map on column parities is injective, through six squarings. -/
theorem columnStep_theta_injective : Function.Injective (columnStep 4 1 1) :=
  columnStep_injective_of_sq (by decide) <| columnStep_injective_of_sq (by decide) <|
    columnStep_injective_of_sq (by decide) <| columnStep_injective_of_sq (by decide) <|
    columnStep_injective_of_sq (by decide) <| columnStep_injective_of_sq (by decide) <|
    columnStep_sixtyFour_injective

/-- The column parities after theta are theta's map applied to the parities before. -/
theorem column_theta (A : State) :
    (theta A).column = columnStep 4 1 1 A.column := by
  funext x
  rw [theta_eq]
  simp only [State.column, lane_ofLanes]
  rw [xor_five, show x - 1 = x + 4 by revert x; decide, ← UInt64.xor_assoc]
  rfl

/-- Theta is injective. -/
theorem theta_injective : Function.Injective theta := by
  intro A B h
  -- The column parities agree, since theta's map on them is injective.
  have hc : A.column = B.column :=
    columnStep_theta_injective (by rw [← column_theta, ← column_theta, h])
  rw [theta_eq, theta_eq, hc] at h
  exact State.ext_lane fun x y => (UInt64.xor_left_inj _).1 (ofLanes_inj h x y)

/-! ## The permutation -/

/-- One round is injective. -/
theorem round_injective (ir : Fin ROUNDS) : Function.Injective (round ir) :=
  (iota_injective ir).comp (chi_injective.comp (pi_injective.comp
    (rho_injective.comp theta_injective)))

/-- The rounds from any index on are injective. -/
theorem roundsFrom_injective (i : Nat) : Function.Injective (keccakF.roundsFrom i) := by
  intro A B h
  rw [keccakF.roundsFrom, keccakF.roundsFrom] at h
  split at h
  · exact round_injective _ (roundsFrom_injective (i + 1) h)
  · exact h
termination_by ROUNDS - i

/-- Keccak-f[1600] is injective. -/
theorem keccakF_injective : Function.Injective keccakF :=
  roundsFrom_injective 0

instance : Finite State :=
  have : Finite UInt64 := Finite.of_injective UInt64.toFin fun _ _ => UInt64.toFin_inj.mp
  Finite.of_injective State.lane fun _ _ h => State.ext_lane fun x y => congrFun (congrFun h x) y

/-- Keccak-f[1600] is a permutation of the 2^1600 states, as FIPS 202 §3 states. -/
theorem keccakF_bijective : Function.Bijective keccakF :=
  Finite.injective_iff_bijective.mp keccakF_injective

end EthLib.Cryptography.Hash.Keccak
