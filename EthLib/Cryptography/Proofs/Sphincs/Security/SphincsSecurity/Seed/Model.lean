module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Seed.Guess
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Recovery

/-!
# Key material without the master seed

A secret is the start of one WOTS+C chain, the secret of one FORS leaf, or a surrogate.

Each secret is one derivation: the first 16 bytes of one hash of `SK.seed` at `PK.seed`.

The seed also gives two hashes of `leanSPHINCS || SK.seed || d` without an address.

The first 16 bytes at `d = 0` are `PK.seed`, and the whole output at `d = 1` is `SK.prf`.

`SK.prf` keys the randomizers.

The material holds these two outputs and one 32-byte value per secret.

These are the full answers of the programmed inputs, with the 16 bytes that a derivation discards.

Its sampling takes no master seed.

Only the inputs of the secrets depend on the public seed, the first 16 bytes of its output.

Programming a cache writes the material at these inputs.

This module does not assume that a cache of the honest game is independent of the master seed.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.SeedModel

variable [Params]

abbrev OtsPosition := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev ForsPosition := Index × FTree × FLeaf
/-- The position of a secret: a chain start, a FORS leaf or a surrogate level. -/
abbrev SecretPosition := OtsPosition ⊕ (ForsPosition ⊕ Fin maxLayerHeight)
abbrev SecretOutputs := SecretPosition → HashOutput

instance forsPositionDecEq : DecidableEq ForsPosition := inferInstance
instance otsPositionDecEq : DecidableEq OtsPosition := inferInstance
instance secretPositionDecEq : DecidableEq SecretPosition :=
  @instDecidableEqSum _ _ otsPositionDecEq (@instDecidableEqSum _ _ forsPositionDecEq inferInstance)
instance secretPositionFintype : Fintype SecretPosition := inferInstance
noncomputable instance secretOutputsFintype : Fintype SecretOutputs := Pi.instFintype

attribute [local instance] Classical.propDecidable

/-- The outputs that give `PK.seed` and `SK.prf`, then one 32-byte value per secret.

A secret uses only the first 16 bytes of its value, but the material keeps all 32. -/
abbrev Material := (HashOutput × HashOutput) × SecretOutputs

/-- The output whose first half is `PK.seed`. -/
def parameterOutput (material : Material) : HashOutput := material.1.1

/-- The public seed: the first 16 bytes of the parameter output. -/
def parameter (material : Material) : PublicParameter := truncateHash (parameterOutput material)

/-- The secret PRF key `SK.prf`. -/
def prf (material : Material) : HashOutput := material.1.2

@[irreducible] noncomputable def secretOutputsSampleableType : SampleableType SecretOutputs :=
  SampleableType.ofFintype SecretOutputs

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- Uniform material; the sampling takes no master seed, and it draws `SK.prf` last. -/
noncomputable def sampleMaterial : ProbComp Material := do
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ SecretOutputs
  let prf ← $ᵗ HashOutput
  return ((parameterOutput, prf), outputs)

/-! ### The derivation of each secret -/

/-- The hash domain of the derivation that gives a secret. -/
def secretDomain : SecretPosition → KeygenDomain
  | .inl (lay, tree, leaf, chain) => .ots lay tree leaf chain
  | .inr (.inl (index, κ, leaf)) => .fors index κ leaf
  | .inr (.inr level) => .surrogate level

/-- Distinct secrets have distinct derivation domains. -/
theorem secretDomain_injective : Function.Injective secretDomain := by
  intro left right h
  rcases left with ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | _ <;>
    rcases right with ⟨_, _, _, _⟩ | ⟨_, _, _⟩ | _ <;> simp_all [secretDomain]

/-! ### Programming the cache -/

/-- The input whose output gives `PK.seed`. -/
def parameterInput (seed : MasterSeed) : HashInput := keySeedInput seed 0

/-- The input whose output is `SK.prf`. -/
def prfInput (seed : MasterSeed) : HashInput := keySeedInput seed 1

/-- The input of the derivation that gives a secret, at the public seed of the material. -/
def secretInput (seed : MasterSeed) (material : Material) (position : SecretPosition) : HashInput :=
  keygenHashInput (parameter material) (secretDomain position) seed

theorem secretInput_injective (seed : MasterSeed) (material : Material) :
    Function.Injective (secretInput seed material) := by
  intro left right h
  exact secretDomain_injective (keygenInput_injective h).2.1

omit [Params] in
theorem prfInput_ne_parameterInput (seed : MasterSeed) : prfInput seed ≠ parameterInput seed :=
  fun h => absurd (keySeedInput_injective (by decide) (by decide) h).2 (by decide)

theorem secretInput_ne_parameterInput (seed : MasterSeed) (material : Material)
    (position : SecretPosition) : secretInput seed material position ≠ parameterInput seed :=
  fun h => keySeedInput_ne_keygenHashInput seed seed 0 _ _ h.symm

theorem secretInput_ne_prfInput (seed : MasterSeed) (material : Material)
    (position : SecretPosition) : secretInput seed material position ≠ prfInput seed :=
  fun h => keySeedInput_ne_keygenHashInput seed seed 1 _ _ h.symm

/-- The base cache with the two key-seed outputs and the value of every secret written in.

Programming overwrites these inputs and keeps every other input of the base cache. -/
noncomputable def programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) : QueryCache HashSpec := QueryCache.ofFn fun input =>
  if input = parameterInput seed then some (parameterOutput material)
  else if input = prfInput seed then some (prf material)
  else if h : ∃ position, input = secretInput seed material position then
    some (material.2 (Classical.choose h))
  else base input

theorem programCache_parameter (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) :
    programCache base seed material (parameterInput seed) = some (parameterOutput material) := by
  simp [programCache]

theorem programCache_prf (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    programCache base seed material (prfInput seed) = some (prf material) := by
  rw [programCache, QueryCache.toFn_ofFn, ite_eq_right (prfInput_ne_parameterInput seed),
    ite_eq_left rfl]

theorem programCache_secret (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) (position : SecretPosition) :
    programCache base seed material (secretInput seed material position) =
      some (material.2 position) := by
  rw [programCache, QueryCache.toFn_ofFn,
    ite_eq_right (secretInput_ne_parameterInput seed material position),
    ite_eq_right (secretInput_ne_prfInput seed material position)]
  have h : ∃ other, secretInput seed material position = secretInput seed material other :=
    ⟨position, rfl⟩
  rw [dite_eq_left h]
  exact congrArg (fun p => some (material.2 p))
    (secretInput_injective seed material (Classical.choose_spec h).symm)

/-- Programming keeps every input that is neither a key-seed input nor the input of a secret.

This includes the derivations under any other public seed. -/
theorem programCache_other (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) (hparameter : input ≠ parameterInput seed) (hprf : input ≠ prfInput seed)
    (hsecret : ∀ position, input ≠ secretInput seed material position) :
    programCache base seed material input = base input := by
  simp only [programCache, QueryCache.toFn_ofFn, hparameter, hprf, ↓reduceIte]
  refine dite_eq_right ?_
  rintro ⟨position, hd⟩
  exact hsecret position hd

/-! ### The inputs that name the seed -/

/-- The input names the seed: it derives a key from it, or it is `leanSPHINCS || seed || d`. -/
abbrev SeedNamed (input : HashInput) (seed : MasterSeed) : Prop := SeedGuess.SeedHit input seed

/-- Two caches agree at every input that does not name the seed. -/
def AgreeOutsideSeed (seed : MasterSeed) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬SeedNamed input seed → left input = right input

/-- Programming changes no input that does not name the seed. -/
theorem programCache_agreeOutside (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) :
    AgreeOutsideSeed seed (programCache base seed material) base := by
  intro input hnot
  apply programCache_other
  · intro heq
    exact hnot (.inr ⟨0, heq.symm⟩)
  · intro heq
    exact hnot (.inr ⟨1, heq.symm⟩)
  · intro position heq
    exact hnot (.inl ⟨parameter material, secretDomain position, heq.symm⟩)

/-- Programming changes no input of the tweakable hash. -/
theorem programCache_verifier (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    programCache base seed material (tweakableHashInput p domain payload) =
      base (tweakableHashInput p domain payload) := by
  apply programCache_agreeOutside
  rintro (⟨p', domain', heq⟩ | ⟨index, heq⟩)
  · exact keygenInput_ne_hashInput p' p domain' domain seed payload heq
  · exact keySeedInput_ne_tweakableHashInput seed index p domain payload heq

/-- The answer function agrees with the programmed answers.

This holds at the two key-seed inputs and at the input of every secret. -/
def PreparedAgreement (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) :
    Prop :=
  f (parameterInput seed) = parameterOutput material ∧ f (prfInput seed) = prf material ∧
    ∀ position, f (secretInput seed material position) = material.2 position

/-- Let the answer function agree with the programmed answers.

Then the secret that the signer derives is the first 16 bytes of its material value. -/
theorem secret_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (position : SecretPosition) :
    truncateHash (f (secretInput seed material position)) = truncateHash (material.2 position) := by
  rw [h.2.2]

/-- Let the answer function agree with the programmed answers.

Then `PK.seed` is the public seed of the material. -/
theorem eval_parameter_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) (h : PreparedAgreement f seed material) :
    evalWithAnswerFn f (derivePublicSeed seed : OracleComp HashSpec PublicParameter) =
      parameter material := by
  simp only [derivePublicSeed]
  exact congrArg truncateHash h.1

/-- Let the answer function agree with the programmed answers.

Then `SK.prf` is the PRF key of the material. -/
theorem eval_prf_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) :
    evalWithAnswerFn f (derivePrf seed : OracleComp HashSpec HashOutput) = prf material := by
  simp only [derivePrf, Completeness.eval_oracleHash]
  exact h.2.1

/-- Let the answer function agree with the programmed answers.

Then the start of a WOTS+C chain is the first 16 bytes of its material value. -/
theorem eval_ots_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) :
    evalWithAnswerFn f (Seeded.otsStart (parameter material) lay tree leaf chain seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 (.inl (lay, tree, leaf, chain))) := by
  rw [← secret_prepared f seed material h (.inl (lay, tree, leaf, chain))]
  exact Completeness.otsSecret_eq f _ lay tree leaf seed chain

/-- Let the answer function agree with the programmed answers.

Then the secret of a FORS leaf is the first 16 bytes of its material value. -/
theorem eval_fors_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (index : Index) (κ : FTree) (leaf : FLeaf) :
    evalWithAnswerFn f (Seeded.forsSecret (parameter material) index κ leaf seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 (.inr (.inl (index, κ, leaf)))) := by
  rw [← secret_prepared f seed material h (.inr (.inl (index, κ, leaf)))]
  exact Completeness.forsSecretValue_eq f _ index κ seed leaf

/-- Let the answer function agree with the programmed answers.

Then a surrogate is the first 16 bytes of its material value. -/
theorem eval_surrogate_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) (h : PreparedAgreement f seed material) (level : Fin maxLayerHeight) :
    evalWithAnswerFn f (deriveKey (parameter material) (.surrogate level) seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 (.inr (.inr level))) := by
  rw [← secret_prepared f seed material h (.inr (.inr level)), Completeness.eval_deriveKey]
  rfl

end SphincsSecurity.Security.SeedModel
