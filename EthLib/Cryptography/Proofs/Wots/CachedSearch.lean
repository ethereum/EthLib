module

public import EthLib.Cryptography.Wots
public import VCVio.OracleComp.QueryTracking.RandomOracle.AcceptedScan

/-!
# The first codeword from an ordered scan

Each trial obtains a full hash word and decodes it once.

An accepted scan can return that same word to the caller that needs the decoded codeword.
-/

public section

namespace EthLib.Cryptography.Wots

open OracleSpec OracleComp AcceptedScan

/-- Decoding the selected answer of VCVio's scan gives the result of the library search.

The equation holds for any hash handler and retains the effects of every attempted trial. -/
theorem findFirst_eq_scanWithAnswer {m : Type → Type} [Monad m] [LawfulMonad m] {A X Y D : Type}
    [DecidableEq Y] (read : A → m Y) (encode : X → A) (trial : Nat → X)
    (decode : Y → Option D) (accepted : Finset Y) (valid : ∀ y, y ∈ accepted ↔ (decode y).isSome)
    (c fuel : Nat) :
    findFirst trial (fun x => decode <$> read (encode x)) c fuel =
      (fun result : Option (X × Y) => result.bind fun pair =>
        (decode pair.2).map fun d => (pair.1, d)) <$>
        simulateQ (spec := A →ₒ Y) read (scanWithAnswer accepted encode
          ((List.range' c fuel).map trial)) := by
  induction fuel generalizing c with
  | zero => simp [findFirst, scanWithAnswer]
  | succ n ih =>
    simp only [findFirst, List.range'_succ, List.map_cons, scanWithAnswer, simulateQ_bind,
      simulateQ_spec_query, bind_map_left, map_bind]
    apply bind_congr
    intro word
    cases hd : decode word with
    | none =>
      have no : word ∉ accepted := fun h => by simpa [hd] using (valid word).mp h
      simpa [no, hd] using ih (c + 1)
    | some d =>
      have yes : word ∈ accepted := (valid word).mpr (by simp [hd])
      simp [yes, hd]

/-- Forgetting the decoded value retains exactly the position selected by the scan. -/
theorem findFirst_position_eq_scan {m : Type → Type} [Monad m] [LawfulMonad m] {A X Y D : Type}
    [DecidableEq Y] (read : A → m Y) (encode : X → A) (trial : Nat → X)
    (decode : Y → Option D) (accepted : Finset Y) (valid : ∀ y, y ∈ accepted ↔ (decode y).isSome)
    (c fuel : Nat) :
    Option.map Prod.fst <$> findFirst trial (fun x => decode <$> read (encode x)) c fuel =
      simulateQ (spec := A →ₒ Y) read (scan accepted encode ((List.range' c fuel).map trial)) := by
  induction fuel generalizing c with
  | zero => simp [findFirst]
  | succ n ih =>
    simp only [findFirst, List.range'_succ, List.map_cons, scan_cons, simulateQ_bind,
      simulateQ_spec_query, bind_map_left, map_bind]
    apply bind_congr
    intro word
    cases hd : decode word with
    | none =>
      have no : word ∉ accepted := fun h => by simpa [hd] using (valid word).mp h
      simpa [no] using ih (c + 1)
    | some d =>
      have yes : word ∈ accepted := (valid word).mpr (by simp [hd])
      simp [yes]

end EthLib.Cryptography.Wots
