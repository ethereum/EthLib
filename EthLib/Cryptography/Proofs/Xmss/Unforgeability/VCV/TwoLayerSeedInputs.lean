module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.TwoLayerAddresses
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SeedInputs
import EthLib.Cryptography.Proofs.Xmss.Serialization

/-!
# The public hash inputs that can reveal a seed

The leanXMSS draft in "Hashing and parameters" puts eight fixed bytes before the master seed.

Each chain or tree hash has at least 64 input bytes.

The parameter, private chain starts and randomizer base have their own address types.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph

open Constants HashSig OracleSpec OracleComp
open ChainGraph (Public Word)
open scoped ENNReal

/-- The master-seed hash is shorter than every well-formed chain, leaf or node hash. -/
theorem decode_masterSeed (pp : PublicParam) (s : XmssSecurity.MasterSeed) :
    decode pp (XmssSecurity.seedHashInput s) = none := by
  classical
  unfold decode
  split
  next hit =>
    obtain ⟨⟨l, r⟩, vs, _, same⟩ := hit
    have master : (XmssSecurity.seedHashInput s).length = 40 := by
      simp only [XmssSecurity.seedHashInput, List.length_append, HashSig.bytesLE, List.length_ofFn]
      rfl
    have length := (congrArg List.length same).trans master
    change (thInput pp _ (LayerGraph.payload r vs)).size = 40 at length
    simp only [thInput, ByteArray.size_append, size_packBytes] at length
    cases r <;> simp only [LayerGraph.payload, ByteArray.size_append, size_packBytes,
      size_packDigests] at length <;> contradiction
  next => rfl

/-- The three kinds of address at which the scheme derives a private hash word. -/
@[expose] def PrivateAddress (address : Address) : Prop :=
  ∃ tag : AddressType, (tag = .prf ∨ tag = .param ∨ tag = .rnd) ∧
    ∃ mu hi lo, address = encodeAddress tag.code mu hi lo

/-- The three calls used by key generation and OTS signing have private addresses. -/
theorem private_calls (l : Layer) (e : UInt32) (j : Fin (V / 2)) :
    PrivateAddress addrParam ∧ PrivateAddress (addrPrf l e j) ∧ PrivateAddress (addrRnd l e) :=
  ⟨⟨.param, Or.inr (Or.inl rfl), _, _, _, rfl⟩,
   ⟨.prf, Or.inl rfl, _, _, _, rfl⟩, ⟨.rnd, Or.inr (Or.inr rfl), _, _, _, rfl⟩⟩

/-- The remaining physical inputs can pay for seed guesses without revisiting a graph charge. -/
@[expose] def otherInputs (pp : PublicParam) (c : Public.QueryCache) : Set HashInput :=
  physicalInputs c \ addressedInputs pp c

/-- A paid input can test a seed only if its bytes can encode one of the two derivations. -/
@[expose] def seedInputs (c : Public.QueryCache) : Set HashInput :=
  {b | b ∈ physicalInputs c ∧
    ((∃ s, XmssSecurity.seedHashInput s = b) ∨
      ∃ f x, PrivateAddress x.2.1 ∧ prfEncoding.enc f x = b)}

/-- An observed public query at either hidden input reveals a seed word. -/
@[expose] def SeedGuess (c : Public.QueryCache)
    (seeds : XmssSecurity.MasterSeed × (Unit → HashOutput)) : Prop :=
  XmssSecurity.seedHashInput seeds.1 ∈ physicalInputs c ∨
    ∃ x : PrfInput, PrivateAddress x.2.1 ∧ prfEncoding.enc seeds.2 x ∈ physicalInputs c

private theorem master_other (pp : PublicParam) (c : Public.QueryCache)
    (s : XmssSecurity.MasterSeed)
    (seen : XmssSecurity.seedHashInput s ∈ physicalInputs c) :
    XmssSecurity.seedHashInput s ∈ otherInputs pp c := by
  refine ⟨seen, ?_⟩
  rintro ⟨_, named⟩
  simp [decode_masterSeed] at named

private theorem prf_other (pp : PublicParam) (c : Public.QueryCache) (f : Unit → HashOutput)
    (x : PrfInput) (addr : PrivateAddress x.2.1) (seen : prfEncoding.enc f x ∈ physicalInputs c) :
    prfEncoding.enc f x ∈ otherInputs pp c := by
  obtain ⟨p, a, suffix⟩ := x
  obtain ⟨t, ht, mu, hi, lo, rfl⟩ := addr
  refine ⟨seen, other_address_not_charged _ _ _ _ ?_ _ _ _ _⟩
  rcases ht with h | h | h <;> simp [h]

/-- Inputs that can test seeds are disjoint from the ordinary inputs charged by the graph. -/
theorem seedInputs_subset_other (pp : PublicParam) (c : Public.QueryCache) :
    seedInputs c ⊆ otherInputs pp c := by
  rintro b ⟨seen, ⟨s, rfl⟩ | ⟨f, x, addr, rfl⟩⟩
  · exact master_other pp c s seen
  · exact prf_other pp c f x addr seen

/-- An actual digest trial has a message address and a final 16-byte randomizer.

Its input cannot pay for a private derivation or a master-seed guess. -/
theorem message_not_seed (pp : PublicParam) (c : Public.QueryCache) (l : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) :
    (thInput pp (addrMsg l e) (msg ++ packBytes rho)).data.toList ∉ seedInputs c := by
  rintro ⟨_, ⟨s, same⟩ | ⟨f, ⟨other, a, suffix⟩, addr, same⟩⟩
  · have n := congrArg List.length same
    change (XmssSecurity.seedHashInput s).length = (thInput pp _ _).size at n
    simp only [XmssSecurity.seedHashInput, List.length_append, HashSig.bytesLE, List.length_ofFn,
      thInput, ByteArray.size_append, size_packBytes] at n
    change 8 + 32 = 16 + 16 + (msg.size + 16) at n
    omega
  · obtain ⟨t, kind, mu, hi, lo, rfl⟩ := addr
    have sameAddr := (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.1
    have tag := AddressType.code_injective (encodeAddress_inj.mp sameAddr).1
    rcases kind with h | h | h <;> simp [h] at tag

/-- The game draws both hidden values after observing the public cache. -/
@[expose] noncomputable def drawSeeds :
    ProbComp (XmssSecurity.MasterSeed × (Unit → HashOutput)) := do
  let master ← XmssSecurity.sampleMasterSeed
  let table ← $ᵗ (Unit → HashOutput)
  return (master, table)

/-- Each public input outside the charged graph can test at most one candidate for each secret. -/
theorem prEvent_seedGuess (c : Public.QueryCache) :
    Pr{let seeds ← drawSeeds}[SeedGuess c seeds] ≤
      2 * (2 ^ 256 : ℝ≥0∞)⁻¹ * ((seedInputs c).encard : ℝ≥0∞) := by
  let atInput (b : HashInput) (seeds : XmssSecurity.MasterSeed × (Unit → HashOutput)) :=
    b ∈ Set.range (seedEncoding.enc seeds.1) ∨ b ∈ Set.range (prfEncoding.enc seeds.2)
  have charge (b : HashInput) :
      Pr{let seeds ← drawSeeds}[atInput b seeds] ≤ 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    apply (prEvent_or_le drawSeeds _ _).trans
    rw [two_mul]
    apply add_le_add
    · apply le_trans _ (prEvent_mem_range_seedEncoding_le b)
      apply le_of_eq
      simp only [drawSeeds, prEvent_norm]
      simp only [← bind_pure_comp]
      apply prEvent_bind_congr_of_support
      intro master _
      exact OracleComp.prEvent_bind_const _ _
    · apply le_trans _ (prEvent_mem_range_prfEncoding_le b)
      apply le_of_eq
      simp only [drawSeeds, prEvent_norm]
      simp only [← bind_pure_comp]
      exact OracleComp.prEvent_bind_const _ _
  apply le_trans (prEvent_mono _ _ _ ?_) (prEvent_exists_mem_le_encard_mul
    drawSeeds (seedInputs c) atInput (fun b _ => charge b))
  rintro seeds (master | ⟨x, addr, seen⟩)
  · exact ⟨_, ⟨master, Or.inl ⟨_, rfl⟩⟩, Or.inl ⟨(), rfl⟩⟩
  · exact ⟨_, ⟨seen, Or.inr ⟨_, x, addr, rfl⟩⟩, Or.inr ⟨x, rfl⟩⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.TwoLayerGraph
