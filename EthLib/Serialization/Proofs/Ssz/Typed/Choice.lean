module

public import EthLib.Serialization.Ssz.Typed.Choice
public import EthLib.Serialization.Proofs.Ssz.Typed.Class

/-!
# Proofs: a type that a decision chooses is lawful

The choice is lawful when both of its options are, since its codec is that of the chosen one.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A type that a decision chooses is lawful when both of its choices are. -/
instance instLawfulSszTypeIte {p : Prop} [decision : Decidable p] {α β : Type} [SszType α]
    [SszType β] [LawfulSszType α] [LawfulSszType β] :
    LawfulSszType (@ite Type p decision α β) :=
  match decision with
  | .isTrue _ => inferInstanceAs (LawfulSszType α)
  | .isFalse _ => inferInstanceAs (LawfulSszType β)

end EthLib.Serialization.Ssz
