module

public import EthLib.Serialization.Der
public import EthLib.Base.Except

/-!
# DER reader checks

A successful typed read has the requested tag and a complete read consumes its input.
-/

@[expose] public section

namespace EthLib.Serialization.Proofs.Der

open EthLib.Serialization.Der
open EthLib.Base

/-- A typed read succeeds only with the requested tag and the underlying reader's result. -/
theorem readTag_ok_iff {tag : UInt8} {input rest : ByteArray} {value : Value} :
    readTag tag input = .ok (value, rest) ↔
      read input = .ok (value, rest) ∧ value.tag = tag := by
  simp only [readTag, bind_ok_iff]
  constructor
  · rintro ⟨⟨v, r⟩, parsed, checked⟩
    split at checked
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at checked
      obtain ⟨rfl, rfl⟩ := checked
      exact ⟨parsed, ‹v.tag = tag›⟩
    · simp at checked
  · rintro ⟨parsed, same⟩
    exact ⟨(value, rest), parsed, by simp [same, pure, Except.pure]⟩

/-- An exact read succeeds only when no trailing bytes remain. -/
theorem exact_ok_iff {tag : UInt8} {input : ByteArray} {value : Value} :
    exact tag input = .ok value ↔
      ∃ rest, readTag tag input = .ok (value, rest) ∧ rest.isEmpty = true := by
  simp only [exact, bind_ok_iff]
  constructor
  · rintro ⟨⟨v, r⟩, parsed, checked⟩
    split at checked
    · simp only [pure, Except.pure, Except.ok.injEq] at checked
      subst v
      exact ⟨r, parsed, ‹r.isEmpty = true›⟩
    · simp at checked
  · rintro ⟨rest, parsed, empty⟩
    exact ⟨(value, rest), parsed, by simp [empty, pure, Except.pure]⟩

/-- An INTEGER whose zero sign byte is redundant is rejected for every remaining byte. -/
theorem integer_redundant_zero (next : UInt8) (rest : List UInt8)
    (small : next.toNat < 128) (encoded : ByteArray) :
    integer ⟨2, ⟨(0 :: next :: rest).toArray⟩, encoded⟩ = .error .value := by
  simp [integer, small, throw, throwThe, MonadExceptOf.throw,
    Functor.map, Except.map]

end EthLib.Serialization.Proofs.Der
