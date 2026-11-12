module

public import EthLib.Execution.Blocks.ProofOfWork
public import EthLib.Execution.Proofs.Blocks.Header

/-!
# Proofs: the proof of work of a header

Before Shapella, the seal item is the item of the header without the mix digest and the nonce.

So the seal hash keeps every other field in its order, the base fee from London included.

A header passes the check exactly when Ethash gives its mix digest and a result within the target.

So a header with another mix digest fails, whatever its nonce.

A higher difficulty never raises the target, so it never accepts a result that a lower one rejects.

The official proof-of-work vectors are in the Python suite, through the bindings.
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Ethash (PowOutput)
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace Header

/-- Before Shapella, the seal item is the item of the header without its 14th and 15th items.

Those two are the mix digest and the nonce.

So it keeps the first 13 fields in their order, then the base fee from London. -/
theorem sealItem_eq {fork : Fork} (h : Header fork) {items : List Item}
    (hItem : Codec.toItem h = .list items) (hFork : fork < .shapella) :
    h.sealItem = .list (items.take 13 ++ items.drop 15) := by
  rw [toItem_eq] at hItem
  obtain rfl := Item.list.inj hItem
  -- Every field added from Shapella on holds no item.
  have hNot : ∀ f : Fork, Fork.shapella ≤ f → ¬f ≤ fork := fun f hf hle =>
    absurd (Nat.lt_of_le_of_lt (Nat.le_trans hf hle) hFork) (Nat.lt_irrefl _)
  simp only [Item.ofSince, hNot .shapella (by decide), hNot .dencun (by decide),
    hNot .pectra (by decide), hNot .glamsterdam (by decide), dite_false, List.append_nil]
  rfl

/-- Before Shapella, the seal hash hashes the header item without its 14th and 15th items. -/
theorem sealHash_eq {fork : Fork} (h : Header fork) {items : List Item}
    (hItem : Codec.toItem h = .list items) (hFork : fork < .shapella) :
    h.sealHash = keccak256 <$> encode (.list (items.take 13 ++ items.drop 15)) := by
  rw [sealHash, ← sealItem_eq h hItem hFork]
  cases encode h.sealItem <;> rfl

end Header

/-- An output seals a header exactly when it has the header's mix digest and a result in target. -/
theorem checkPowOutput_eq_ok_iff {fork : Fork} (h : Header fork) (out : PowOutput) :
    checkPowOutput h out = .ok () ↔
      out.mixDigest = ⟨h.prevRandao.toArray⟩ ∧
        bytesToNat out.result.toList ≤ powTarget h.difficulty := by
  unfold checkPowOutput
  split
  · rename_i hm
    exact ⟨(fun h => nomatch h), fun ⟨h, _⟩ => absurd h hm⟩
  · rename_i hm
    split
    · rename_i hr
      exact ⟨(fun h => nomatch h), fun ⟨_, h⟩ => absurd h (Nat.not_le.mpr hr)⟩
    · rename_i hr
      exact ⟨fun _ => ⟨Classical.not_not.mp hm, Nat.not_lt.mp hr⟩, fun _ => rfl⟩

/-- The check passes exactly when Ethash gives the header's mix digest and a result in target. -/
theorem checkProofOfWork_eq_ok_iff {fork : Fork} (h : Header fork) :
    checkProofOfWork h = .ok () ↔
      ∃ out : PowOutput, powOutput h = .ok out ∧
        out.mixDigest = ⟨h.prevRandao.toArray⟩ ∧
        bytesToNat out.result.toList ≤ powTarget h.difficulty := by
  unfold checkProofOfWork
  -- The output stays opaque: only its shape matters.
  generalize powOutput h = r
  cases r with
  | error e => exact ⟨(fun h => nomatch h), fun ⟨_, h, _⟩ => nomatch h⟩
  | ok out =>
    show checkPowOutput h out = .ok () ↔ _
    rw [checkPowOutput_eq_ok_iff]
    exact ⟨fun hc => ⟨out, rfl, hc⟩, fun ⟨_, ho, hc⟩ => by cases ho; exact hc⟩

/-- A header whose mix digest is not the one that Ethash gives fails the check. -/
theorem checkProofOfWork_wrongMixDigest {fork : Fork} {h : Header fork} {out : PowOutput}
    (hp : powOutput h = .ok out) (hm : out.mixDigest ≠ ⟨h.prevRandao.toArray⟩) :
    checkProofOfWork h ≠ .ok () := by
  rw [Ne, checkProofOfWork_eq_ok_iff]
  rintro ⟨out', hp', hm', -⟩
  rw [hp] at hp'
  cases hp'
  exact hm hm'

/-- Each error has its own code. -/
theorem PowError.code_injective (e₁ e₂ : PowError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [PowError.code] at h; exact absurd h (by decide))

/-- A higher positive difficulty has a target no higher. -/
theorem powTarget_antitone {d d' : Nat} (hd : 0 < d) (h : d ≤ d') :
    powTarget d' ≤ powTarget d :=
  Nat.div_le_div_left h hd

end EthLib.Execution.Blocks
