module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphRisk
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerSeedInputs

/-!
# Disjoint physical inputs for the two-layer graph, message trials and seed guesses

The leanXMSS draft assigns each kind of hash call an address type in "Hashing and parameters".

The types distinguish messages, chains, leaves, internal nodes and PRF calls.

A public hash cache counts each byte string once, across either half and all request repetitions.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig OracleComp OracleSpec TwoLayerGraph SecretEncoding.Residual
open ChainGraph (Word Public)
open scoped ENNReal Classical

/-- Occupied inputs at a genuine layer, epoch, message and randomizer address.

Both halves of an input count as one physical word.
-/
@[expose] def messageInputs (pp : PublicParam) (c : Public.QueryCache) : Set HashInput :=
  {b | b ∈ TwoLayerGraph.physicalInputs c ∧
      ∃ (l : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer),
    (thInput pp (addrMsg l e) (msg ++ packBytes rho)).data.toList = b}

/-- The three charges use pairwise disjoint ordinary hash inputs. -/
theorem input_classes (pp : PublicParam) (c : Public.QueryCache) :
    Disjoint (addressedInputs pp c) (messageInputs pp c) ∧
      Disjoint (addressedInputs pp c) (seedInputs c) ∧
        Disjoint (messageInputs pp c) (seedInputs c) := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · rintro _ graphHit ⟨_, l, e, msg, rho, rfl⟩
    exact other_address_not_charged pp pp c .msg (Or.inr (Or.inr (Or.inr rfl))) _ _ _ _ graphHit
  · intro b graphHit seedHit
    exact (seedInputs_subset_other pp c seedHit).2 graphHit
  · rintro b ⟨_, l, e, msg, rho, rfl⟩ seedHit
    exact message_not_seed pp c l e msg rho seedHit

/-- A cache pays for its addressed graph inputs, trials and seed guesses simultaneously. -/
theorem joint_footprint (pp : PublicParam) (c : Public.QueryCache) :
    (addressedInputs pp c).encard + (messageInputs pp c).encard + (seedInputs c).encard ≤
      (TwoLayerGraph.physicalInputs c).encard := by
  obtain ⟨gm, gs, ms⟩ := input_classes pp c
  rw [← Set.encard_union_eq gm, ← Set.encard_union_eq (Disjoint.sup_left gs ms)]
  apply Set.encard_le_encard
  rintro b ((graphHit | trial) | seed)
  · exact addressed_subset pp c graphHit
  · exact trial.1
  · exact seed.1

attribute [local irreducible] continuation

/-- The joint count is bounded on every actual native deferred path, including refusal or conflict.
-/
theorem charged_path (A : Adversary) (left : Nat) (w : HashOutput) (obs : Option Outcome)
    (extra : ResidualCache (parameterOfWord w)) (st : Footprint.State Row) (pending : List Cell)
    (run : let pp := parameterOfWord w
      ((obs, extra), st, pending) ∈ support (Footprint.coldRun (graph pp) pp
        (WeightedCap.capCompOpt paidFee left (continuation A pp))
        (localState _ _ (toKeyedState pp (afterWord w))))) :
    let pp := parameterOfWord w
    (addressedInputs pp st.1).encard + (messageInputs pp st.1).encard + (seedInputs st.1).encard
      ≤ left :=
  (joint_footprint (parameterOfWord w) st.1).trans
      (Footprint.actual_deferred A left w obs extra st pending run).2

/-- Keep the charge of the graph on its actual addressed inputs.

An additional event may depend on the filled state and an independent final draw.

Its own cache-dependent charge enters the same cutoff as the graph potential.
-/
theorem prEvent_addressed_joint {S α : Type} (pp : PublicParam)
    (ms : ProbComp S) (H : S → Footprint.State Row → Prop)
    (c : Public.QueryCache → ℝ≥0∞) (hc : ∀ st : Footprint.State Row,
      Pr{let s ← ms}[H s st] ≤ c st.1)
    (body : OracleComp (Public.withLabels Start Row Word) α)
    (paired : ∀ z ∈ support ((simulateQ (graph pp).deferredImpl body).run ((∅, ∅), [])),
      PairedPresence z.2.1) (B : ℝ≥0∞) (finite : B ≠ ⊤) :
    Pr{let z ← (graph pp).deferredFillDraw ms body}[
      ((graph pp).Conflict z.2.1 ∨ OffPath pp z.2.1 ∨ H z.2.2 z.2.1) ∧
      2 * ((addressedInputs pp z.2.1.1).encard : ℝ≥0∞) / Nat.card Word + c z.2.1.1 ≤ B] ≤ B := by
  let f := subgraph pp
  let nk := TwoLayerGraph.keys pp
  have empty : ¬((lowGraph pp).Conflict (f.project (∅, ∅)) ∨ nk.TCHazard (f.project (∅, ∅))) := by
    change ¬((lowGraph pp).Conflict (∅, ∅) ∨ nk.TCHazard (∅, ∅))
    exact not_or.mpr ⟨(lowGraph pp).not_conflict_empty, CanonicalGraph.NodeKeys.not_tcHazard_empty⟩
  have charged := (f.isCharged nk.isCharged).prEvent_deferredFillDraw_and_le empty
    (fun cache => 2 * ((addressedInputs pp cache).encard : ℝ≥0∞) / Nat.card Word)
    (potential_le_addressed pp) ms H c hc body B finite
  refine (prEvent_mono_of_support _ _ _ ?_).trans charged
  rintro z hz ⟨hit, bill⟩
  obtain ⟨before, filled, _⟩ := (graph pp).mem_support_deferredFillDraw_iff.mp hz
  have together := paired _ before
  have stable := RelabelState.fst_eq_of_mem_support_endFill filled
  have finalPresence : PairedPresence z.2.1 := by simpa only [PairedPresence, stable] using together
  exact ⟨hit.elim (fun conflict => Or.inl (Or.inl (lowConflict pp _ finalPresence conflict)))
    (fun other => other.elim (fun off => Or.inl (Or.inr (lowCollision pp _ off))) Or.inr), bill⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
