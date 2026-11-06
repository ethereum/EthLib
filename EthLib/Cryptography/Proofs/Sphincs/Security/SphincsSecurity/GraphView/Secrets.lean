module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Classification.Signature
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Domains
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Base.Prelude

@[expose] public section

section

/-!
# Secret tables and the fixed-function world

A hash output splits into its low 128 bits, the digest that the scheme keeps, and its high bits.

Recombining the two parts gives back the output, so a split loses no information.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Prefix

variable [Params]
open Concrete

abbrev High := BitVec (hashOutputBits - digestBits)

noncomputable def combine (low : Digest) (high : High) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

omit [Params] in
theorem split_combine (low : Digest) (high : High) :
    splitHashOutput digestBits (combine low high) = (low, high) :=
  (splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high)

omit [Params] in
theorem truncate_combine (low : Digest) (high : High) : truncateHash (combine low high) = low :=
  congrArg Prod.fst (split_combine low high)

omit [Params] in
theorem combine_split (output : HashOutput) :
    combine (truncateHash output) (splitHashOutput digestBits output).2 = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

end SphincsSecurity.Security.Prefix

end

section

/-! Chain addresses, and the tables of chain secrets indexed by them. -/

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Prefix

variable [Params]
open UniformTableSplit

attribute [local instance] Classical.propDecidable

abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev Secrets := ChainAddress → Digest

end SphincsSecurity.Security.Prefix

end

section

/-!
The predicate that selects the hash calls of a run.

The fixed-function world answers private draws freshly and hash calls with a supplied function.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security.Prefix

variable [Params]

/-- Source-side hash calls, excluding private uniform samples. -/
def SourceHash : OracleWorld.Domain → Prop
  | .inl _ => False
  | .inr _ => True

instance (input : OracleWorld.Domain) : Decidable (SourceHash input) := by
  cases input <;> unfold SourceHash <;> infer_instance

/-- Fresh private uniform sampling together with a supplied fixed hash function. -/
noncomputable def fixedHashWorld (outside : QueryImpl HashSpec Id) : QueryImpl OracleWorld ProbComp
  | .inl sample => liftM (unifSpec.query sample)
  | .inr bytes => pure (outside bytes)

end SphincsSecurity.Security.Prefix

end

section

/-! The chain secrets derived from the seed, as a table indexed by chain addresses. -/

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Prefix

variable [Params]
open Concrete

def derivedSecrets (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (seed : MasterSeed) :
    Secrets :=
  fun (lay, tree, leaf, chain) =>
    evalWithAnswerFn f
      (Seeded.otsStart parameter lay tree leaf chain seed : OracleComp HashSpec Digest)

end SphincsSecurity.Security.Prefix

end

section

/-! The first successful encoding of a counter search, which the honest one-time signer computes. -/

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Prefix

variable [Params]
open Concrete

attribute [local instance] Classical.propDecidable
attribute [local irreducible] encodingAttemptLimit Seeded.treePath Seeded.forsNode chainWalk

/-- The actual least successful encoding search; its counter remains a 32-bit value. -/
noncomputable def firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : HashInput) :
    Nat → Nat → Option (Counter × Encoding)
  | 0, _ => none
  | attempts + 1, counter =>
      match evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) :
            OracleComp HashSpec (Option Encoding)) with
      | some word => some (BitVec.ofNat counterBits counter, word)
      | none => firstEncoding f parameter lay tree leaf message attempts (counter + 1)

theorem otsSignFrom_eq_firstEncoding (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (seed : MasterSeed) (message : HashInput)
    (attempts start : Nat) :
    evalWithAnswerFn f (Seeded.otsSignFrom parameter lay tree leaf seed message attempts start :
      OracleComp HashSpec (Option (Counter × (ChainIndex → Digest)))) =
    (firstEncoding f parameter lay tree leaf message attempts start).map (fun pair =>
      (pair.1, fun chain => evalWithAnswerFn f (chainWalk parameter lay tree leaf chain 0
        (pair.2 chain).val (derivedSecrets f parameter seed (lay, tree, leaf, chain)) :
        OracleComp HashSpec Digest))) := by
  induction attempts generalizing start with
  | zero => rfl
  | succ attempts ih =>
      cases hencode : evalWithAnswerFn f
          (encode parameter lay tree leaf message (BitVec.ofNat counterBits start) :
            OracleComp HashSpec (Option Encoding)) with
      | none =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode]
          exact ih (start + 1)
      | some word =>
          simp only [Seeded.otsSignFrom, evalWithAnswerFn_bind, firstEncoding, hencode,
            Completeness.eval_sequenceFin, Completeness.eval_otsSecrets, Completeness.otsSecret,
            evalWithAnswerFn_pure, Option.map_some, derivedSecrets]

end SphincsSecurity.Security.Prefix

end

section

/-! Hash-only evaluation inside the private-sampling interpreter is deterministic. -/

open OracleComp OracleSpec

namespace SphincsSecurity.Security.Prefix

variable [Params]
open Concrete

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit Seeded.signLayer
  Seeded.forsOpen Seeded.forsKey sequenceFin chainWalk

omit [Params] in
/-- Hash-only evaluation inside the private-sampling interpreter is deterministic. -/
theorem fixedHashWorld_lift_hash (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) :
    simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      pure (evalWithAnswerFn f computation) := by
  have hlift : simulateQ (fixedHashWorld f) (liftM computation : OracleComp OracleWorld α) =
      simulateQ (fun bytes => pure (f bytes) : QueryImpl HashSpec ProbComp) computation :=
    QueryImpl.simulateQ_liftComp_right_eq_of_apply (fixedHashWorld f)
      (fun bytes => pure (f bytes)) (fun _ => rfl) computation
  rw [hlift]
  clear hlift
  induction computation using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind input next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, evalWithAnswerFn_bind,
        show evalWithAnswerFn f (liftM (HashSpec.query input)) = f input from
          simulateQ_spec_query f input,
        pure_bind]
      exact ih (f input)

end SphincsSecurity.Security.Prefix

end
