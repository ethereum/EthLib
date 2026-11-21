module

public import VCVio.OracleComp.QueryTracking.RandomOracle.HiddenSeed.Reindex
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainStarts
import all EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainStarts
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PaidSources
public import VCVio.OracleComp.QueryTracking.RandomOracle.PairedValue.Derivations

/-!
# Private labels of the chain starts

The leanXMSS draft, section "WOTS+C", takes the starts of chains 2j and 2j+1 from one PRF word.

The fixed public parameter, layer, epoch, pair address and empty suffix identify that word.

Its low and high tags distinguish the two starts.

The complement contains every other private query in the source game.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
open Constants HashSig

/-- Both layers use the same chain-start index type, including the full 32-bit epoch. -/
abbrev StartKey := Layer × UInt32 × Fin V

/-- The physical label of a private word that supplies two chain starts. -/
@[expose] def startLabel (pp : PublicParam) (key : StartKey) : PrfInput :=
  (pp, addrPrf key.1 key.2.1 (ChainGraph.pairIndex key.2.2), ByteArray.empty)

/-- The parity of the chain index selects the same half that the library collector reads. -/
@[expose] def taggedStart (pp : PublicParam) (key : StartKey) : PrfInput ⊕ PrfInput :=
  if key.2.2.val % 2 = 0 then .inl (startLabel pp key) else .inr (startLabel pp key)

private theorem tagged_physical (pp : PublicParam) (key : StartKey) :
    (taggedStart pp key).elim id id = startLabel pp key := by
  unfold taggedStart
  split <;> rfl

private theorem tagged_parity (pp : PublicParam) (key : StartKey) :
    (taggedStart pp key).isLeft = decide (key.2.2.val % 2 = 0) := by
  unfold taggedStart
  split <;> simp_all

/-- The encoded layer, epoch, pair address and tag recover the complete chain index. -/
theorem taggedStart_injective (pp : PublicParam) : Function.Injective (taggedStart pp) := by
  rintro ⟨l, epoch, i⟩ ⟨l', epoch', j⟩ same
  have phys := congrArg (Sum.elim id id) same
  rw [tagged_physical, tagged_physical] at phys
  obtain ⟨rfl, rfl, pair⟩ := addrPrf_inj.mp (congrArg (fun a : PrfInput => a.2.1) phys)
  have quot : i.val / 2 = j.val / 2 := by exact congrArg Fin.val pair
  have tags := congrArg Sum.isLeft same
  rw [tagged_parity, tagged_parity] at tags
  have parity : i.val % 2 = 0 ↔ j.val % 2 = 0 := by simpa using tags
  have eq : i = j := Fin.ext (by omega)
  cases eq
  rfl

/-- At fixed pp, unused private labels belong to a disjoint second table. -/
abbrev OtherPrivate (pp : PublicParam) := (Set.range (taggedStart pp))ᶜ

/-- Combine the two layers' chain starts and every residual query into the exact private key set. -/
noncomputable def privateKeyEquiv (pp : PublicParam) :
    StartKey ⊕ OtherPrivate pp ≃ PrfInput ⊕ PrfInput := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective (taggedStart pp) (taggedStart_injective pp))
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (taggedStart pp)))

@[simp] theorem privateKeyEquiv_start (pp : PublicParam) (k : StartKey) :
    privateKeyEquiv pp (.inl k) = taggedStart pp k := by
  classical
  simp [privateKeyEquiv]

@[simp] theorem privateKeyEquiv_other (pp : PublicParam) (k : OtherPrivate pp) :
    privateKeyEquiv pp (.inr k) = k.val := by
  classical
  simp [privateKeyEquiv]

/-- The two rows of the j-th physical word are exactly the two adjoining chain starts. -/
theorem privateKeyEquiv_pair (pp : PublicParam) (l : Layer) (e : UInt32) (j : Fin (V / 2)) :
    let lab : PrfInput := (pp, addrPrf l e j, ByteArray.empty)
    (privateKeyEquiv pp).symm (.inl lab) = .inl (l, e, ChainGraph.indexAt j 0) ∧
    (privateKeyEquiv pp).symm (.inr lab) = .inl (l, e, ChainGraph.indexAt j 1) := by
  intro lab
  have pair (h : Fin 2) : ChainGraph.pairIndex (ChainGraph.indexAt j h) = j := Fin.ext (by
    change (2 * j.val + h.val) / 2 = j.val
    omega)
  constructor
  · apply (privateKeyEquiv pp).injective
    simp [taggedStart, startLabel, lab, pair]
    change (2 * j.val + _) % 2 = _
    omega
  · apply (privateKeyEquiv pp).injective
    simp [taggedStart, startLabel, lab, pair]
    change (2 * j.val + _) % 2 = _
    omega

open OracleSpec OracleComp HashSig RandomOraclePairedValue

/-- Public 128-bit hash rows have a separate port for the experiment's client charge. -/
abbrev KeyBackend := PairedHashWord.HalfSpec + Tick

/-- Keep the raw hashes and ticks and arrange every private half by its chain or residual key. -/
@[expose] noncomputable def toKeyedState (pp : PublicParam)
    (s : SecretEncoding.SplitCache Backend PrfInput HashOutput) :
    SecretEncoding.SplitCache KeyBackend (StartKey ⊕ OtherPrivate pp) (BitVec digestBits) :=
  SecretEncoding.reindexState KeyBackend (privateKeyEquiv pp).symm
    (Derivations.splitState Tick PairedHashWord.halves s)

/-- Both halves of a private PRF word populate the two chain starts at the actual pair address. -/
theorem toKeyedState_pair (pp : PublicParam)
    (s : SecretEncoding.SplitCache Backend PrfInput HashOutput)
    (l : Layer) (e : UInt32) (j : Fin (V / 2)) :
    let k : PrfInput := (pp, addrPrf l e j, ByteArray.empty)
    (toKeyedState pp s).2 (.inl (l, e, ChainGraph.indexAt j 0)) =
        (s.2 k).map (fun w => (PairedHashWord.halves w).1) ∧
    (toKeyedState pp s).2 (.inl (l, e, ChainGraph.indexAt j 1)) =
        (s.2 k).map (fun w => (PairedHashWord.halves w).2) := by
  intro k
  obtain ⟨low, high⟩ := privateKeyEquiv_pair pp l e j
  rw [← low, ← high]
  apply And.intro
  · exact SecretEncoding.reindexState_apply KeyBackend (privateKeyEquiv pp).symm
      (Derivations.splitState Tick PairedHashWord.halves s) (Sum.inl k)
  · exact SecretEncoding.reindexState_apply KeyBackend (privateKeyEquiv pp).symm
      (Derivations.splitState Tick PairedHashWord.halves s) (Sum.inr k)

/-- A private label outside the start set retains its exact original half and its own row. -/
theorem toKeyedState_other (pp : PublicParam)
    (s : SecretEncoding.SplitCache Backend PrfInput HashOutput)
    (k : OtherPrivate pp) :
    (toKeyedState pp s).2 (.inr k) =
      (RandomOraclePairedValue.splitCache PairedHashWord.halves s.2) k.val := by
  change _ = (RandomOraclePairedValue.splitCache PairedHashWord.halves s.2) k.val
  rfl

open Classical in
/-- An adaptive caller can use explicit private chain starts and a residual table.

The caller may start after parameter generation with both private halves already populated.
-/
theorem program_keyed_joint {α : Type} (pp : PublicParam) (body : OracleComp Source α)
    (initial : SecretEncoding.SplitCache Backend PrfInput HashOutput) :
    let perm := (privateKeyEquiv pp).symm
    let e := PairedHashWord.halves
    let aux := Tick
    let original := body
    let program := simulateQ (SecretEncoding.reindexQueries KeyBackend perm)
      (simulateQ (Derivations.expand aux e) original)
    (fun z => (z.1, z.2, toKeyedState pp z.2)) <$>
      (simulateQ (SecretEncoding.idealImpl Backend PrfInput HashOutput) original).run initial =ᵈ
    (fun z => (z.1, Derivations.joinState aux e
      (SecretEncoding.reindexState KeyBackend perm.symm z.2), z.2)) <$>
      (simulateQ (SecretEncoding.idealImpl KeyBackend (StartKey ⊕ OtherPrivate pp)
        (BitVec digestBits))
        program).run (toKeyedState pp initial) := by
  classical
  intro perm e aux original program
  have h := Derivations.run_joint Tick PairedHashWord.halves body initial
  have joint := h.map (fun z => (z.1, z.2.1, SecretEncoding.reindexState KeyBackend perm z.2.2))
  have reindexed := SecretEncoding.reindex_ideal KeyBackend perm
    (simulateQ (Derivations.expand aux e) original) (Derivations.splitState aux e initial)
  unfold program toKeyedState
  rw [← reindexed]
  have mapState {α S T : Type} (f : S → T) :
      (Prod.map id f : α × S → _) = fun z => (z.1, f z.2) := by
    funext ⟨_, _⟩
    rfl
  simp only [Functor.map_map, mapState, SecretEncoding.reindexState_symm] at joint ⊢
  exact joint

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient
