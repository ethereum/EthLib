module

public import Mathlib.Data.LawfulXor.Basic

/-!
# Proofs: the sponge construction over any permutation

The sponge of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge], §3.1.

Their Algorithm 1 starts from zero; this one squeezes once, from any initial state.

The permutation is a function in any monad.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

variable {Dg E C Msg : Type}

/-- The state of a sponge: the rate, split into a digest part and the rest, then the capacity.

A block is XORed into the rate before each permutation call. -/
abbrev SpongeState (Dg E C : Type) := (Dg × E) × C

/-- The digest part of a state: the first component of the rate. -/
abbrev SpongeState.out (s : SpongeState Dg E C) : Dg := s.1.1

section Xor

variable [XorOp Dg] [XorOp E]

/-- XOR on the rate, component by component. -/
def rateXor (a b : Dg × E) : Dg × E := (a.1 ^^^ b.1, a.2 ^^^ b.2)

/-- Absorb a block: XOR it into the rate, and keep the capacity. -/
def absorb (s : SpongeState Dg E C) (B : Dg × E) : SpongeState Dg E C := (rateXor s.1 B, s.2)

/-- The block that takes the state `s` to the state `x`.

It does so when the two capacities agree and XOR cancels. -/
def blockTo (s x : SpongeState Dg E C) : Dg × E := rateXor s.1 x.1

/-- Absorb the blocks from a state: XOR each into the rate, then permute with `π`. -/
def absorbAll {m : Type → Type} [Monad m] (π : SpongeState Dg E C → m (SpongeState Dg E C)) :
    SpongeState Dg E C → List (Dg × E) → m (SpongeState Dg E C)
  | s, [] => pure s
  | s, B :: bs => do
    let y ← π (absorb s B)
    absorbAll π y bs

@[simp] theorem absorbAll_nil {m : Type → Type} [Monad m]
    (π : SpongeState Dg E C → m (SpongeState Dg E C)) (s : SpongeState Dg E C) :
    absorbAll π s [] = pure s := rfl

theorem absorbAll_cons {m : Type → Type} [Monad m]
    (π : SpongeState Dg E C → m (SpongeState Dg E C)) (s : SpongeState Dg E C) (B : Dg × E)
    (bs : List (Dg × E)) :
    absorbAll π s (B :: bs) = (π (absorb s B) >>= fun y => absorbAll π y bs) := rfl

/-- The sponge over a pure function, in a lawful monad, returns the pure hash. -/
theorem absorbAll_pure {m : Type → Type} [Monad m] [LawfulMonad m]
    (π : SpongeState Dg E C → SpongeState Dg E C) (s : SpongeState Dg E C)
    (bs : List (Dg × E)) :
    absorbAll (fun x => (pure (π x) : m _)) s bs =
      pure (Id.run (absorbAll (fun x => (pure (π x) : Id _)) s bs)) := by
  induction bs generalizing s with
  | nil => rfl
  | cons B bs ih => simp only [absorbAll_cons, pure_bind, ih]

/-- Absorbing keeps the capacity. -/
@[simp] theorem absorb_snd (s : SpongeState Dg E C) (B : Dg × E) : (absorb s B).2 = s.2 := rfl

variable [Zero Dg] [Zero E] [LawfulXor Dg] [LawfulXor E]

/-- XOR on the rate cancels. -/
theorem rateXor_cancel (a b : Dg × E) : rateXor a (rateXor a b) = b := by
  simp [rateXor]

/-- Absorbing the block from `s` to `x` gives `x`, when `s` and `x` share their capacity. -/
theorem absorb_blockTo {s x : SpongeState Dg E C} (h : s.2 = x.2) : absorb s (blockTo s x) = x := by
  obtain ⟨⟨a, b⟩, c⟩ := s
  obtain ⟨⟨a', b'⟩, c'⟩ := x
  simp only at h
  subst h
  simp only [absorb, blockTo]
  rw [rateXor_cancel]

/-- The block absorbed into `s` is the block from `s` to the result. -/
theorem blockTo_absorb (s : SpongeState Dg E C) (B : Dg × E) : blockTo s (absorb s B) = B :=
  rateXor_cancel s.1 B

/-- Absorbing into one state is injective in the block. -/
theorem absorb_injective (s : SpongeState Dg E C) : Function.Injective (absorb s) := by
  intro B B' h
  rw [← blockTo_absorb s B, h, blockTo_absorb]

end Xor

/-- A padding of messages into lists of blocks: injective, and never empty.

Bertoni et al., §3.1 and §3.3, also ask that the last block is not zero.

That condition serves their squeeze of several blocks, so one squeeze does without it. -/
structure Padding (Msg Blk : Type) where
  /-- The padded message, as a list of blocks. -/
  pad : Msg → List Blk
  /-- Distinct messages have distinct paddings. -/
  pad_injective : Function.Injective pad
  /-- A padded message has at least one block. -/
  pad_ne_nil : ∀ m, pad m ≠ []

namespace Padding

variable {Blk : Type} (P : Padding Msg Blk)

/-- The message whose padding is the list, if any. -/
noncomputable def unpad : List Blk → Option Msg := Function.partialInv P.pad

/-- The decoder recognizes exactly the paddings. -/
theorem unpad_eq_some_iff (β : List Blk) (m : Msg) : P.unpad β = some m ↔ P.pad m = β :=
  P.pad_injective.isPartialInv m β

/-- The decoder inverts the padding. -/
@[simp] theorem unpad_pad (m : Msg) : P.unpad (P.pad m) = some m :=
  (P.unpad_eq_some_iff _ m).2 rfl

end Padding

variable [XorOp Dg] [XorOp E]

/-- **The sponge**, with one squeeze.

Absorb the padded message from the initial state `iv` with `π`, and output the digest part. -/
def sponge {m : Type → Type} [Monad m] (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)
    (π : SpongeState Dg E C → m (SpongeState Dg E C)) (msg : Msg) : m Dg :=
  SpongeState.out <$> absorbAll π iv (P.pad msg)

/-- The sponge over a function `π`, as a hash of messages. -/
def spongeHash (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)
    (π : SpongeState Dg E C → SpongeState Dg E C) (msg : Msg) : Dg :=
  Id.run (sponge P iv (fun s => pure (π s)) msg)

end EthLib.Cryptography.Sponge
