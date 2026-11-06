module

public import EthLib.Cryptography.Proofs.Sphincs.Security.SphincsSecurity.Statement

/-!
# Signing requests without repeats

This module defines programs and adversaries that never request two signatures on one message.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SphincsSecurity.Security.ForsPotential

variable [Params]


/-- The program never requests a signature on a message in `S`, nor twice on one message. -/
def NoRepeat {α : Type} (M : OracleComp (OracleWorld + SigningSpec) α) : List Message → Prop :=
  OracleComp.construct (C := fun _ => List Message → Prop) (fun _ _ => True)
    (fun input _ rec S => match input with
      | .inl _ => ∀ v, rec v S
      | .inr m => m ∉ S ∧ ∀ r, rec r (S ++ [m])) M

theorem noRepeat_sign {α : Type} (m : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) (S : List Message) :
    NoRepeat (liftM ((OracleWorld + SigningSpec).query (.inr m)) >>= next) S ↔
      m ∉ S ∧ ∀ r, NoRepeat (next r) (S ++ [m]) :=
  Iff.rfl

/-- For every public key, the adversary never requests two signatures on one message. -/
def _root_.FORS.Security.Adversary.NoRepeat (adversary : Adversary) : Prop :=
  ∀ pk, ForsPotential.NoRepeat (adversary.main pk) []

end SphincsSecurity.Security.ForsPotential
