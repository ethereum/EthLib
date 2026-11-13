module

public import EthLib.Base.Proofs.MapM
public import EthLib.Networking.Enr.Consensus
public import EthLib.Serialization.Proofs.Ssz.Typed.Basic
public import EthLib.Serialization.Proofs.Ssz.Typed.Collections
public import EthLib.Serialization.Proofs.Ssz.Typed.Container

/-!
# `Networking.Proofs.Enr.Consensus`

Properties of the consensus entries of a node record.

- The `eth2` value is a lawful SSZ container, so it round-trips and has 16 bytes.
- A key that exists at a fork exists at every later fork.
- A node accepts a record exactly when each of its entries reads, and the `eth2` entry is present.
- A node before Altair reads no sync committee subnets.
- A node from Fulu on reads a custody group count and a next fork digest, or rejects the record.
- The custody group count is the number that its bytes write, most significant first.
- The next fork digest is the four bytes of its entry.
- A node before Fulu reads neither.
- Each entry error has its own code, and no record error has that code.
-/

@[expose] public section

namespace EthLib.Networking.Proofs.Enr.Consensus

open EthLib.Base (Fork bind_ok_iff)
open EthLib.Networking.Enr
open EthLib.Serialization
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
  obtain ⟨a, _, ha⟩ := bind_ok_iff.mp h
  cases a with
  | none => simp [throw, throwThe, MonadExceptOf.throw] at ha
  | some x =>
    simp only [pure, Except.pure, Except.ok.injEq] at ha
    simp [← ha]

/--
A node accepts a record exactly when each entry reads at the fork, and the entries are those values.

The `eth2` entry must be present.
-/
theorem readEntries_eq_ok_iff {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count} :
    readEntries count fork r = .ok e ↔
      readSsz EnrForkId r .eth2 = .ok (some e.eth2) ∧
        readSsz (Attnets count) r .attnets = .ok e.attnets ∧
        readAt fork .syncnets (readSsz Syncnets r .syncnets) = .ok e.syncnets ∧
        readRequiredAt fork .cgc (readCgc r) = .ok e.cgc ∧
        readRequiredAt fork .nfd (readSsz (Vector UInt8 4) r .nfd) = .ok e.nfd := by
  constructor
  · intro h
    simp only [readEntries] at h
    obtain ⟨eth2?, he, h⟩ := bind_ok_iff.mp h
    cases eth2? with
    | none => simp [throw, throwThe, MonadExceptOf.throw] at h
    | some eth2 =>
      obtain ⟨attnets, ha, h⟩ := bind_ok_iff.mp h
      obtain ⟨syncnets, hs, h⟩ := bind_ok_iff.mp h
      obtain ⟨cgc, hc, h⟩ := bind_ok_iff.mp h
      obtain ⟨nfd, hn, h⟩ := bind_ok_iff.mp h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨he, ha, hs, hc, hn⟩
  · rintro ⟨he, ha, hs, hc, hn⟩
    simp only [readEntries, he, ha, hs, hc, hn, bind, Except.bind, pure, Except.pure]

/-- The entries that a node reads, from the values of each step. -/
theorem readEntries_ok {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count}
    (h : readEntries count fork r = .ok e) :
    readAt fork .syncnets (readSsz Syncnets r .syncnets) = .ok e.syncnets ∧
      readRequiredAt fork .cgc (readCgc r) = .ok e.cgc ∧
      readRequiredAt fork .nfd (readSsz (Vector UInt8 4) r .nfd) = .ok e.nfd :=
  (readEntries_eq_ok_iff.mp h).2.2

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

/-- A required key reads a value exactly when the fork has the key and the read gives that value. -/
theorem readRequiredAt_eq_ok_some_iff {α : Type} {fork : Fork} {key : ConsensusKey}
    {read : Except EntryError (Option α)} {a : α} :
    readRequiredAt fork key read = .ok (some a) ↔ key.since ≤ fork ∧ read = .ok (some a) := by
  by_cases hf : key.since ≤ fork
  · simp only [readRequiredAt, hf, ite_true, true_and]
    cases read with
    | error e => simp [bind, Except.bind]
    | ok v =>
      cases v <;> simp [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  · simp [readRequiredAt, hf, pure, Except.pure]

/--
A record has the custody group count `n` exactly when its `cgc` bytes write `n` in base 256.

The bytes come most significant first, with no leading zero byte, so zero is the empty byte string.
-/
theorem readCgc_eq_ok_some_iff {r : Enr} {n : UInt64} :
    readCgc r = .ok (some n) ↔
      ∃ b : ByteArray, lookup r .cgc = some (.bytes b) ∧ b.data.toList.head? ≠ some 0 ∧
        Rlp.ofBigEndian b.data.toList = n.toNat := by
  simp only [readCgc, lookupBytes]
  cases hl : lookup r .cgc with
  | none => simp [bind, Except.bind, pure, Except.pure]
  | some item =>
    cases item with
    | list _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    | bytes b =>
      simp only [bind, Except.bind, pure, Except.pure, Option.some.injEq, Rlp.Item.bytes.injEq,
        exists_eq_left', Rlp.Codec.ofItem, Rlp.Item.toScalarBelow, Rlp.Item.toScalar]
      by_cases h0 : b.data.toList.head? = some 0
      · simp [h0, Except.mapError]
      · simp only [h0, ite_false, ne_eq, not_false_eq_true, true_and]
        by_cases hlt : Rlp.ofBigEndian b.data.toList < 2 ^ 64
        · simp only [hlt, ite_true, Except.mapError, Except.ok.injEq, Option.some.injEq]
          constructor
          · rintro rfl
            exact (UInt64.toNat_ofNat_of_lt' hlt).symm
          · intro h
            rw [h, UInt64.ofNat_toNat]
        · simp only [hlt, ite_false, Except.mapError, reduceCtorEq, false_iff]
          intro h
          exact hlt (h ▸ n.toNat_lt)

/-- A record has the fork digest `d` at a key exactly when the key holds the four bytes of `d`. -/
theorem readSsz_digest_eq_ok_some_iff {r : Enr} {key : ConsensusKey} {d : Vector UInt8 4} :
    readSsz (Vector UInt8 4) r key = .ok (some d) ↔ lookup r key = some (.bytes ⟨d.toArray⟩) := by
  have hs : SszType.serialize d = .ok ⟨d.toArray⟩ := rfl
  simp only [readSsz, lookupBytes]
  cases hl : lookup r key with
  | none => simp [bind, Except.bind, pure, Except.pure]
  | some item =>
    cases item with
    | list _ => simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
    | bytes b =>
      simp only [bind, Except.bind, pure, Except.pure, Option.some.injEq, Rlp.Item.bytes.injEq]
      cases hd : SszType.deserialize (Vector UInt8 4) b with
      | error e =>
        simp only [Except.mapError, reduceCtorEq, false_iff]
        rintro rfl
        rw [SszType.deserialize_serialize hs] at hd
        cases hd
      | ok d' =>
        simp only [Except.mapError, Except.ok.injEq, Option.some.injEq]
        constructor
        · rintro rfl
          have := SszType.serialize_deserialize hd
          rw [hs] at this
          cases this
          rfl
        · rintro rfl
          rw [SszType.deserialize_serialize hs] at hd
          cases hd
          rfl

/--
A node reads a custody group count exactly from Fulu on, and it is the number that `cgc` writes.

The bytes come most significant first, with no leading zero byte, so zero is the empty byte string.
-/
theorem readEntries_cgc_eq_some_iff {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count} (h : readEntries count fork r = .ok e) {n : UInt64} :
    e.cgc = some n ↔
      .fusaka ≤ fork ∧ ∃ b : ByteArray, lookup r .cgc = some (.bytes b) ∧
        b.data.toList.head? ≠ some 0 ∧ Rlp.ofBigEndian b.data.toList = n.toNat := by
  have hc := (readEntries_ok h).2.1
  constructor
  · intro hn
    rw [hn] at hc
    obtain ⟨hf, hr⟩ := readRequiredAt_eq_ok_some_iff.mp hc
    exact ⟨hf, readCgc_eq_ok_some_iff.mp hr⟩
  · rintro ⟨hf, hb⟩
    have hr : readRequiredAt fork .cgc (readCgc r) = .ok (some n) :=
      readRequiredAt_eq_ok_some_iff.mpr ⟨hf, readCgc_eq_ok_some_iff.mpr hb⟩
    rw [hc] at hr
    exact Except.ok.inj hr

/-- A node reads a next fork digest exactly from Fulu on, and it is the four bytes of `nfd`. -/
theorem readEntries_nfd_eq_some_iff {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count} (h : readEntries count fork r = .ok e) {d : Vector UInt8 4} :
    e.nfd = some d ↔ .fusaka ≤ fork ∧ lookup r .nfd = some (.bytes ⟨d.toArray⟩) := by
  have hn := (readEntries_ok h).2.2
  constructor
  · intro hd
    rw [hd] at hn
    obtain ⟨hf, hr⟩ := readRequiredAt_eq_ok_some_iff.mp hn
    exact ⟨hf, readSsz_digest_eq_ok_some_iff.mp hr⟩
  · rintro ⟨hf, hb⟩
    have hr : readRequiredAt fork .nfd (readSsz (Vector UInt8 4) r .nfd) = .ok (some d) :=
      readRequiredAt_eq_ok_some_iff.mpr ⟨hf, readSsz_digest_eq_ok_some_iff.mpr hb⟩
    rw [hn] at hr
    exact Except.ok.inj hr

/-- Before Fulu, a node reads neither a custody group count nor a next fork digest. -/
theorem readEntries_before_fulu {count : UInt64} {fork : Fork} {r : Enr}
    {e : ConsensusEntries count} (h : readEntries count fork r = .ok e) (hf : fork < .fusaka) :
    e.cgc = none ∧ e.nfd = none :=
  ⟨Option.eq_none_iff_forall_ne_some.mpr fun _ hn =>
      absurd ((readEntries_cgc_eq_some_iff h).mp hn).1 (Nat.not_le.mpr hf),
    Option.eq_none_iff_forall_ne_some.mpr fun _ hn =>
      absurd ((readEntries_nfd_eq_some_iff h).mp hn).1 (Nat.not_le.mpr hf)⟩

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
