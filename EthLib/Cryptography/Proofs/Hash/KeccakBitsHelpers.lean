module

public import EthLib.Cryptography.Proofs.Hash.KeccakBitsRefinement

/-!
# Keccak bit-model helper contracts

FIPS 202 section 3.2 specifies the rho walk and round-constant register.
The linear-index helpers define wrapping for all natural indices.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

/-- The rho walk applies the coordinate recurrence at every step. -/
theorem rhoPosition_succ (steps : Nat) : rhoPosition (steps + 1) =
    ((rhoPosition steps).2, (2 * (rhoPosition steps).1 + 3 * (rhoPosition steps).2) % 5) := by
  simp [rhoPosition, List.range_succ, List.foldl_append]
/-- Every rho walk position has bounded coordinates. -/
theorem rhoPosition_bounds (steps : Nat) : (rhoPosition steps).1 < 5 ∧ (rhoPosition steps).2 < 5 := by
  induction steps with
  | zero => decide
  | succ n ih =>
    rw [show n + 1 = Nat.succ n by rfl] at *
    rw [show rhoPosition (Nat.succ n) = ((rhoPosition n).2, (2 * (rhoPosition n).1 + 3 * (rhoPosition n).2) % 5) by
      simp [rhoPosition, List.range_succ, List.foldl_append]]
    exact ⟨ih.2, Nat.mod_lt _ (by decide)⟩
/-- The register update gives each of its eight output bits. -/
theorem registerStep_bit (r : Register) (i : Fin 8) : registerStep r i =
    match i.val with
    | 0 => r 7
    | 1 => r 0
    | 2 => r 1
    | 3 => r 2
    | 4 => Bool.xor (r 3) (r 7)
    | 5 => Bool.xor (r 4) (r 7)
    | 6 => Bool.xor (r 5) (r 7)
    | _ => r 6 := by
  match i with
  | ⟨0, _⟩ => simp [registerStep]
  | ⟨1, _⟩ => simp [registerStep]
  | ⟨2, _⟩ => simp [registerStep]
  | ⟨3, _⟩ => simp [registerStep]
  | ⟨4, _⟩ => simp [registerStep]
  | ⟨5, _⟩ => simp [registerStep]
  | ⟨6, _⟩ => simp [registerStep]
  | ⟨7, _⟩ => simp [registerStep]
  | ⟨n+8, h⟩ => omega
/-- The round-constant bit repeats after 255 indices. -/
theorem rc_periodic (t : Nat) : rc (t + 255) = rc t := by
  simp [rc]
/-- Linear state indices wrap after 1600 bits. -/
theorem stateBit_periodic (a : State) (i : Nat) : stateBit a (i + 1600) = stateBit a i := by
  unfold stateBit xy zcoord
  congr 1 <;> apply Fin.ext <;> simp only <;> omega
/-- Output byte indices wrap after 200 bytes. -/
theorem outputByte_periodic (a : State) (i : Nat) : outputByte a (i + 200) = outputByte a i := by
  have period (j : Nat) : stateBit a (j + 1600) = stateBit a j := by
    unfold stateBit xy zcoord
    congr 1 <;> apply Fin.ext <;> simp only <;> omega
  have same : (fun n j => if stateBit a (8 * (i + 200) + j) then n + 2 ^ j else n) =
      (fun n j => if stateBit a (8 * i + j) then n + 2 ^ j else n) := by
    funext n j
    have index : 8 * (i + 200) + j = (8 * i + j) + 1600 := by omega
    rw [index, period]
  unfold outputByte
  rw [same]

/-- Constant bits repeat after 255 round indices, including outside Keccak-f. -/
theorem roundConstantBit_periodic (ir : Nat) (z : Fin 64) : roundConstantBit (ir + 255) z = roundConstantBit ir z := by
  have h (j : Nat) : rc (j + 7 * (ir + 255)) = rc (j + 7 * ir) := by
    simp [rc, Nat.mul_add, Nat.add_mod]
  unfold roundConstantBit
  have funcs : (fun b j => if z.val = 2 ^ j - 1 then rc (j + 7 * (ir + 255)) else b) =
      (fun b j => if z.val = 2 ^ j - 1 then rc (j + 7 * ir) else b) := by
    funext b j
    rw [h]
  rw [funcs]
/-- The extended Iota mapping repeats after 255 rounds. -/
theorem iota_periodic (ir : Nat) (a : State) : iota (ir + 255) a = iota ir a := by
  funext x y z
  simp [iota, roundConstantBit_periodic]
/-- The extended round mapping repeats after 255 rounds. -/
theorem round_periodic (ir : Nat) (a : State) : round (ir + 255) a = round ir a := by
  unfold round
  funext x y z
  simp [iota, roundConstantBit_periodic]

/-- All natural round indices use only the seven FIPS constant-bit positions. -/
theorem roundConstantBit_spec (ir : Nat) (z : Fin 64) : roundConstantBit ir z =
    if z.val = 63 then rc (6 + 7*ir) else
    if z.val = 31 then rc (5 + 7*ir) else
    if z.val = 15 then rc (4 + 7*ir) else
    if z.val = 7 then rc (3 + 7*ir) else
    if z.val = 3 then rc (2 + 7*ir) else
    if z.val = 1 then rc (1 + 7*ir) else
    if z.val = 0 then rc (7*ir) else false := by
  simp only [roundConstantBit, List.range_succ, List.range_zero, List.foldl_append,
    List.foldl_cons, List.foldl_nil, Nat.reducePow, Nat.reduceSub, Nat.zero_add]

end EthLib.Cryptography.Hash.KeccakBits
