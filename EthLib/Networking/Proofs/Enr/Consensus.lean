module

public import EthLib.Networking.Enr.Consensus
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# `Networking.Proofs.Enr.Consensus`

Properties of the consensus entries of a node record.

- The `eth2` value is a lawful SSZ container, so it round-trips and has 16 bytes.
- A key that exists at a fork exists at every later fork.
- A node before Altair reads no sync committee subnets.
- A node from Fulu on reads a custody group count and a next fork digest, or rejects the record.
- Each entry error has its own code, and no record error has that code.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Enr.Consensus

open EthLib.Base (Fork)
open EthLib.Networking.Enr
open EthLib.Serialization.Ssz

instance : LawfulSszType EnrForkId :=
  .container (by decide) (fun _ => rfl) (fun _ => rfl)

/-- The SSZ bytes of an `eth2` value are 16 bytes long. -/
theorem serialize_size {e : EnrForkId} {data : ByteArray} (h : SszType.serialize e = .ok data) :
    data.size = 16 :=
  SszType.serialize_size (by decide) h

/-- A key that exists at a fork exists at every later fork. -/
theorem keysAt_mono {f g : Fork} {k : ConsensusKey} (hfg : f ≤ g) (hk : k ∈ keysAt f) :
    k ∈ keysAt g := by
  simp only [keysAt, List.mem_filter, decide_eq_true_eq] at hk ⊢
  exact ⟨hk.1, Nat.le_trans hk.2 hfg⟩

/-- A step of `Except` that succeeds came from a first step that succeeds. -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

/-- A key that the fork does not know reads as absent. -/
theorem readAt_before {α : Type} {fork : Fork} {key : ConsensusKey}
    {read : Except EntryError (Option α)} {v : Option α} (h : readAt fork key read = .ok v)
    (hf : fork < key.since) : v = none := by
  have : ¬ key.since ≤ fork := Nat.not_le.mpr hf
  simp only [readAt, this, ite_false, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

/-- A key that the fork requires reads as present. -/
theorem readRequiredAt_isSome {α : Type} {fork : Fork} {key : ConsensusKey}
    {read : Except EntryError (Option α)} {v : Option α} (h : readRequiredAt fork key read = .ok v)
    (hf : key.since ≤ fork) : v.isSome := by
  simp only [readRequiredAt, hf, ite_true] at h
  obtain ⟨a, _, ha⟩ := bind_ok h
  cases a with
  | none => simp [throw, throwThe, MonadExceptOf.throw] at ha
  | some x =>
    simp only [pure, Except.pure, Except.ok.injEq] at ha
    simp [← ha]

/-- The entries that a node reads, from the values of each step. -/
theorem readEntries_ok {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count}
    (h : readEntries count fork r = .ok e) :
    readAt fork .syncnets (readSsz Syncnets r .syncnets) = .ok e.syncnets ∧
      readRequiredAt fork .cgc (readCgc r) = .ok e.cgc ∧
      readRequiredAt fork .nfd (readSsz (Vector UInt8 4) r .nfd) = .ok e.nfd := by
  simp only [readEntries] at h
  obtain ⟨eth2?, _, h⟩ := bind_ok h
  cases eth2? with
  | none => simp [throw, throwThe, MonadExceptOf.throw] at h
  | some eth2 =>
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨syncnets, hs, h⟩ := bind_ok h
    obtain ⟨cgc, hc, h⟩ := bind_ok h
    obtain ⟨nfd, hn, h⟩ := bind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hs, hc, hn⟩

/-- Before Altair, a node reads no sync committee subnets. -/
theorem readEntries_syncnets {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count}
    (h : readEntries count fork r = .ok e) (hf : fork < .altair) : e.syncnets = none :=
  readAt_before (readEntries_ok h).1 hf

/-- From Fulu on, a record that a node accepts has a custody group count and a next fork digest. -/
theorem readEntries_fulu {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count}
    (h : readEntries count fork r = .ok e) (hf : .fusaka ≤ fork) : e.cgc.isSome ∧ e.nfd.isSome :=
  ⟨readRequiredAt_isSome (readEntries_ok h).2.1 hf, readRequiredAt_isSome (readEntries_ok h).2.2 hf⟩

/-! ## Error codes -/

/-- Two entry errors with one code come from one constructor. -/
theorem EntryError.code_injective (e₁ e₂ : EntryError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Two distinct constructors have two distinct literal codes, which `decide` separates.
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [EntryError.code] at h; exact absurd h (by decide))

/-- An entry error never has the code of a record error, so one Python class carries both. -/
theorem EntryError.code_ne_record (e : EntryError) (r : EnrError) : e.code ≠ r.code := by
  cases e <;> cases r <;> simp only [EntryError.code, EnrError.code] <;> decide

end EthLib.Networking.Proofs.Enr.Consensus
