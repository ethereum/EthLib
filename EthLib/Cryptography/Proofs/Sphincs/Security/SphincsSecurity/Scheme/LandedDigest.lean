module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.DigestView
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Bytes
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Search
public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Scheme.Landing

/-!
# Landing digests

The message digest reads each of its bits from its own bit of the digest calls.

This is how Algorithm 19 of FIPS 205 reads the digest.

So uniform digest calls give a uniform digest.

The kept view of a digest is its local index in the kept subtree and the `k` FORS leaf indices.

A uniform digest lands with its kept view in a set `E` with probability `2^-(h - b)` times `p`.

Here `p` is the probability that a uniform kept view lies in `E`.
-/

@[expose] public section

section

/-! ## The digest calls -/

open OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 512

namespace SphincsSecurity.Security

variable [Params]
open Concrete

/-- Uniform outputs of the digest calls give a uniform digest. -/
theorem evalDist_digestBlock_uniform :
    (truncateMessageDigest <$> ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput)))
      =ᵈ ($ᵗ MessageDigest : ProbComp MessageDigest) :=
  evalDist_truncateMessageDigest_uniform

/-- The input of a digest call. -/
abbrev digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : DigestCall) : HashInput :=
  messageDigestInput parameter root message randomness call

end SphincsSecurity.Security

end

section

/-! ## The kept view -/

namespace SphincsSecurity.Lifetime

variable [Params]

set_option exponentiation.threshold 512

open OracleComp OracleSpec ENNReal Concrete


/-- A kept view: a local index below `2^b` and a leaf index for each FORS tree. -/
abbrev KeptDigestView := Fin (2 ^ subtreeHeight) × (FTree → FLeaf)

/-- The kept view of a view: the index modulo `2^b` and the `k` leaf indices.

It is defined for every index, also for one that does not land. -/
def localFullView (view : FullDigestView) : KeptDigestView :=
  (⟨view.1.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩, view.2)

/-- The kept views correspond to the views whose index lands. -/
def keptViewEquiv (parameter : PublicParameter) :
    KeptDigestView ≃ {view : FullDigestView // Landed parameter view.1} where
  toFun view := ⟨((keptLeafEquiv parameter view.1).val, view.2),
    (keptLeafEquiv parameter view.1).property⟩
  invFun view := localFullView view.val
  left_inv view := by
    apply Prod.ext
    · exact (keptLeafEquiv parameter).left_inv view.1
    · rfl
  right_inv view := by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val ((keptLeafEquiv parameter).right_inv ⟨view.val.1, view.property⟩)
    · rfl

theorem local_keptView (parameter : PublicParameter) (view : KeptDigestView) :
    localFullView (keptViewEquiv parameter view).val = view :=
  (keptViewEquiv parameter).left_inv view

def keptFilteredEquiv (parameter : PublicParameter) (P : KeptDigestView → Prop) :
    {view : KeptDigestView // P view} ≃
      {view : FullDigestView // Landed parameter view.1 ∧ P (localFullView view)} where
  toFun view := ⟨(keptViewEquiv parameter view.val).val,
    (keptViewEquiv parameter view.val).property, by simpa only [local_keptView] using view.property⟩
  invFun view := ⟨localFullView view.val, view.property.2⟩
  left_inv view := by apply Subtype.ext; exact local_keptView parameter view.val
  right_inv view := by
    exact Subtype.ext (congrArg
      (fun v : {view : FullDigestView // Landed parameter view.1} => v.val)
      ((keptViewEquiv parameter).right_inv ⟨view.val, view.property.1⟩))

theorem fullDigestView_card_factor :
    Fintype.card FullDigestView = 2 ^ (totalHeight - subtreeHeight) *
      Fintype.card KeptDigestView := by
  simp only [FullDigestView, KeptDigestView, Fintype.card_prod, Fintype.card_fin,
    mul_assoc, ← subtree_size_mul]

/-- The kept view of a digest. -/
def localDigestView (digest : MessageDigest) : KeptDigestView :=
  localFullView (fullDigestView digest)

/-- A uniform digest lands with its kept view in a set with probability `2^-(h - b)` times `p`.

Here `p` is the probability that a uniform kept view lies in the set. -/
theorem probEvent_landed_localDigest (parameter : PublicParameter)
    (P : KeptDigestView → Prop) [DecidablePred P] :
    Pr{let digest ← ($ᵗ MessageDigest : ProbComp MessageDigest)}[Landed parameter
        (digestIndex digest) ∧ P (localDigestView digest)] =
        ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
          Pr{let x ← ($ᵗ KeptDigestView : ProbComp KeptDigestView)}[P x] := by
  change Pr{let x ← ($ᵗ MessageDigest : ProbComp MessageDigest)}[Landed parameter
    (fullDigestView x).1 ∧ P (localFullView (fullDigestView x))] = _
  rw [← prEvent_map ($ᵗ MessageDigest : ProbComp MessageDigest) fullDigestView
      (fun view : FullDigestView => Landed parameter view.1 ∧ P (localFullView view)),
    evalDist_fullDigestView_uniform.prEvent_eq]
  rw [SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample,
    ← Fintype.card_subtype,
    ← Fintype.card_subtype, ← Fintype.card_congr (keptFilteredEquiv parameter P),
    fullDigestView_card_factor, Nat.cast_mul]
  simp only [div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  ring

end SphincsSecurity.Lifetime

end
