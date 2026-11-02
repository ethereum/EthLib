module

public import EthLib.Cryptography.Proofs.Hash.KeccakBits

/-!
# Keccak bit permutation refinement

FIPS 202 section 3.3 composes the five step mappings into a round.
Section 3.4 applies all 24 rounds in order.
-/

@[expose] public section
namespace EthLib.Cryptography.Hash.KeccakBits

private theorem fold_refine {A B C : Type} (f : A → B) (left : A → C → A) (right : B → C → B)
    (step : ∀ a c, f (left a c) = right (f a) c) (xs : List C) (a : A) :
    f (xs.foldl left a) = xs.foldl right (f a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, step]
/-- One independent bit round agrees with one lane round. -/
theorem round_ofLanes (a : Keccak.State) (ir : Fin 24) :
    ofLanes (Keccak.round ir a) = round ir.val (ofLanes a) := by
  simp only [Keccak.round, round, iota_ofLanes, chi_ofLanes, pi_ofLanes,
    rho_ofLanes, theta_ofLanes]
/-- All 24 independent bit rounds agree with Keccak-f for every lane state. -/
theorem permutation_ofLanes (a : Keccak.State) : ofLanes (Keccak.keccakF a) = permutation (ofLanes a) := by
  have rounds : (List.finRange 24).map Fin.val = List.range 24 := by decide
  simp only [Keccak.keccakF, Keccak.ROUNDS, permutation, ← rounds, List.foldl_map]
  exact fold_refine ofLanes (fun (state : Keccak.State) (ir : Fin 24) => Keccak.round ir state)
    (fun state ir => round ir.val state) round_ofLanes _ _

/-- A proved absorption correspondence is enough for a complete transition.

The premise concerns one block and does not assume a hash equality.
-/
theorem absorb_transition_of_absorb (a : Keccak.State) (bytes : List UInt8) (bits : Block)
    (absorption : ofLanes (Keccak.Internal.absorbBlock a bytes) = absorb (ofLanes a) bits) :
    ofLanes (Keccak.keccakF (Keccak.Internal.absorbBlock a bytes)) =
      permutation (absorb (ofLanes a) bits) := by
  rw [permutation_ofLanes, absorption]

/-- Local absorption correspondences compose across every finite list of block pairs. -/
theorem absorb_fold_of_absorb (blocks : List (List UInt8 × Block)) (initial : Keccak.State)
    (absorption : ∀ a pair, pair ∈ blocks →
      ofLanes (Keccak.Internal.absorbBlock a pair.1) = absorb (ofLanes a) pair.2) :
    ofLanes (blocks.foldl (fun a pair => Keccak.keccakF (Keccak.Internal.absorbBlock a pair.1)) initial) =
      blocks.foldl (fun a pair => permutation (absorb a pair.2)) (ofLanes initial) := by
  apply absorb_fold_of_step
  intro a pair member
  exact absorb_transition_of_absorb a pair.1 pair.2 (absorption a pair member)

/-- Each padding bit is one exactly at the first or final position. -/
theorem padding_get (length i : Nat) (h : i < (padding length).length) :
    (padding length)[i] = (decide (i = 0) || decide (i + 1 = (padding length).length)) := by
  cases i with
  | zero => simp [padding]
  | succ j =>
    let n := (1088 - ((length + 2) % 1088)) % 1088
    have bound : j < n + 1 := by simp only [padding_length] at h; dsimp [n]; omega
    simp only [padding_length]
    unfold padding
    change (List.replicate n false ++ [true])[j]'(by simp; omega) =
      (decide (j + 1 = 0) || decide (j + 1 + 1 = n + 2))
    by_cases hj : j < n
    · simp [hj]
      omega
    · have eq : j = n := by omega
      subst j
      simp

end EthLib.Cryptography.Hash.KeccakBits
