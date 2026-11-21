module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticePrice

/-!
# Charge each WOTS+C key once at the first attempt

A saved entry keeps the full message table as it stood before the search.

Later queries cannot change this charge.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open Constants HashSig OracleComp OracleSpec EarlierDigest EarlierDigest.Ledger
open scoped ENNReal Classical

/-- Price of the first search at a key, measured just before its low randomizer lookup. -/
noncomputable def keyPrice (pp : PublicParam) (k : Key) (s : Entry) : ℝ≥0∞ :=
  searchMass pp 0 MAX_RANDOMIZER_TRIALS k s + validCount pp k s

/-- Only keys already booked at least once contribute. -/
noncomputable def savedPrice (pp : PublicParam) (saved : Snapshots) : ℝ≥0∞ :=
  ∑ k ∈ allKeys, (saved k).elim 0 (keyPrice pp k)

@[simp] theorem savedPrice_empty (pp : PublicParam) : savedPrice pp (fun _ => none) = 0 := by
  simp [savedPrice]

/-- Booking a key adds its incoming price exactly once, independently of every later lookup. -/
theorem savedPrice_begin (pp : PublicParam) (saved : Snapshots) (k : Key) (now : Entry) :
    savedPrice pp (begin saved k now) = savedPrice pp saved +
      (if saved k = none then keyPrice pp k now else 0) := by
  classical
  have same (i : Key) :
      ((begin saved k now) i).elim 0 (keyPrice pp i) =
        (saved i).elim 0 (keyPrice pp i) +
          (if i = k ∧ saved k = none then keyPrice pp k now else 0) := by
    by_cases eq : i = k
    · subst i
      cases held : saved k <;> simp [begin, entry, held]
    · simp [begin, eq]
  simp only [savedPrice, same, Finset.sum_add_distrib]
  by_cases held : saved k = none <;> simp [held]

/-- Every booked term is already among the search masses and valid words of the physical price. -/
theorem savedPrice_le (pp : PublicParam) (h : History) :
    savedPrice pp h.2 ≤ total allKeys (searchMass pp 0 MAX_RANDOMIZER_TRIALS) h +
      (initialCount allKeys (validCount pp) h.2 h.1 : ℝ≥0∞) := by
  simp only [savedPrice, total, initialCount, Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  cases held : h.2 k <;> simp [entry, held, keyPrice]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
