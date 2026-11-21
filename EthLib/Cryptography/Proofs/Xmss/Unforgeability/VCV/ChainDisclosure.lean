module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerHonest
public import VCVio.OracleComp.QueryTracking.RandomOracle.Undisclosed
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.LayerGraphLeaf

/-!
# The positions before a disclosed WOTS+C value

At each signed chain the verifier receives the value at the digit selected by the signer.

Releasing that value discloses no smaller position.

For each smaller nonzero position, the predecessor belongs to the same hidden prefix.

See the leanXMSS draft, section "WOTS+C".
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainDisclosure

open EthLib.Cryptography OracleComp OracleSpec Constants TwoLayerGraph
open ChainGraph (Public Word)

private def coordinates : Cell → Option (Layer × UInt32 × Fin V × Nat)
  | .inl (l, e, i) => some (l, e, i, 0)
  | .inr (.inl (l, .chain e i j)) => some (l, e, i, j.val + 1)
  | _ => none

private theorem coordinates_at (l : Layer) (e : UInt32) (i : Fin V) (d : Fin CHAIN_LENGTH) :
    coordinates (inLayer l (LayerGraph.position e i d.val)) = some (l, e, i, d.val) := by
  cases d with
  | mk d bounded =>
    cases d with
    | zero => rfl
    | succ n =>
      change some (l, e, i, n % 3 + 1) = some (l, e, i, n + 1)
      rw [Nat.mod_eq_of_lt (by change n + 1 < 4 at bounded; omega)]

/-- All positions before the released digit at each of the 58 chains of this OTS key. -/
def prefixCells (l : Layer) (e : UInt32) (digits : Vector (Fin CHAIN_LENGTH) V) : Set Cell :=
  {c | ∃ (i : Fin V) (d : Fin CHAIN_LENGTH), d < digits[i] ∧
    c = inLayer l (LayerGraph.position e i d.val)}

/-- A signature releases a value outside its protected chain prefix.

Releases at another layer, another index or a later position also lie outside the prefix. -/
theorem release_outside {l l' : Layer} {e e' : UInt32} (digits : Vector (Fin CHAIN_LENGTH) V)
    (i : Fin V) (d : Fin CHAIN_LENGTH) (safe : l' = l → e' = e → digits[i] ≤ d) :
    inLayer l' (LayerGraph.position e' i d.val) ∉ prefixCells l e digits := by
  rintro ⟨j, earlier, less, same⟩
  have eqn := congrArg coordinates same
  rw [coordinates_at, coordinates_at] at eqn
  simp only [Option.some.injEq, Prod.mk.injEq] at eqn
  obtain ⟨sameLayer, sameEpoch, sameIndex, sameDigit⟩ := eqn
  have bound := safe sameLayer sameEpoch
  rw [sameIndex] at bound
  exact (Nat.not_lt_of_ge bound) (sameDigit.symm ▸ less)

/-- Every nonzero position in a protected chain prefix has a predecessor in the same prefix. -/
theorem prefix_child (pp : PublicParam) (l : Layer) (e : UInt32)
    (digits : Vector (Fin CHAIN_LENGTH) V) :
    ∀ k, .inr k ∈ prefixCells l e digits → ∃ c ∈ (graph pp).ch k, c ∈ prefixCells l e digits := by
  rintro k ⟨i, ⟨d, bounded⟩, less, same⟩
  cases d with
  | zero => cases same
  | succ n =>
    have hn : n < 3 := by change n + 1 < 4 at bounded; omega
    let j : Fin (CHAIN_LENGTH - 1) := ⟨n, hn⟩
    have step : k = .inl (l, .chain e i j) := by
      change Sum.inr k = Sum.inr (Sum.inl (l, LayerGraph.Role.chain e i (Fin.ofNat 3 n))) at same
      have fin : Fin.ofNat 3 n = j := Fin.ext (Nat.mod_eq_of_lt hn)
      rw [fin] at same
      exact Sum.inr.inj same
    subst k
    refine ⟨inLayer l (LayerGraph.position e i n), ?_, i, ⟨n, by omega⟩, ?_, rfl⟩
    · change _ ∈ [inLayer l (LayerGraph.chainCell e i j)]
      rw [LayerGraph.chainCell_eq]
      exact List.mem_singleton_self _
    · change n < digits[i].val
      change n + 1 < digits[i].val at less
      omega

/-- An eager release of a signed digit may be followed by any number of ordinary public probes.

A smaller position stays hidden if the caller never reads it directly. -/
theorem smaller_positions_stay_undisclosed (pp : PublicParam) (l : Layer) (e : UInt32)
    (digits : Vector (Fin CHAIN_LENGTH) V) {α : Type}
    (oa : OracleComp (Public.withLabels Start Row Word) α)
    (avoid : AllQueriesSatisfy oa (CanonicalGraph.AvoidsDirectRead
      (pub := Public) (R := Word) (prefixCells l e digits)))
    {s : Honest.SharedState × List Cell} (cold : ∀ c ∈ prefixCells l e digits, s.1.2 c = none)
    {z} (run : z ∈ support ((simulateQ (graph pp).deferredImpl oa).run s)) :
    ∀ c ∈ prefixCells l e digits, z.2.1.2 c = none := by
  exact (graph pp).stays_undisclosed (prefix_child pp l e digits) avoid cold run

end EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainDisclosure
