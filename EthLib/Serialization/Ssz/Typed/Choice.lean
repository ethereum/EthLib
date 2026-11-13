module

public import EthLib.Serialization.Ssz.Typed.Class

/-!
# Typed SSZ values: a type that a decision chooses

A fork can choose which of two containers a message carries.

The type of the message is then a choice between the two, which a decision settles.

Its codec is that of the type it chooses, so its bytes are those of that type.
-/

@[expose] public section

namespace EthLib.Serialization.Ssz

/-- A type that a decision chooses has the codec of the type that it chooses. -/
instance instSszTypeIte {p : Prop} [decision : Decidable p] {α β : Type} [SszType α]
    [SszType β] : SszType (@ite Type p decision α β) :=
  match decision with
  | .isTrue _ => inferInstanceAs (SszType α)
  | .isFalse _ => inferInstanceAs (SszType β)

end EthLib.Serialization.Ssz
