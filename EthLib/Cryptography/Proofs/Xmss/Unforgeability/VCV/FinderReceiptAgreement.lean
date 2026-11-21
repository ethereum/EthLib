module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptEntries
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderReceiptRows
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNoticeExtensions
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SignedHistory

/-!
# Registration agreement on a single signing key

A valid raw log determines the unique lower signing request for a leaf.

Requests sharing an upper key use the same stored bottom root and upper signature.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open EthLib.Cryptography HashSig Constants OracleSpec OracleComp TwoLayerGraph
    Honest VerifierProbe CachedCodeword PostSigning
open ChainGraph (digestEquiv)

private def payload : FinderNotice → Option Digest
  | .register _ _ _ d => some d
  | .attempt .. => none

private def input : FinderNotice → Option HashInput
  | .register _ _ b _ => some b
  | .attempt .. => none

private theorem lower_of_note {pp q idx msg sig} (c : Receipt pp q idx msg sig)
    {epoch b d st} (here : (FinderNotice.register .bottom epoch b d, st) ∈ c.notes) :
    epoch = UInt32.ofNat idx.toNat ∧
      b = trialInput pp .bottom (UInt32.ofNat idx.toNat) (packBytes msg) sig.bottom.randomizer ∧
      d = selectedDigest c.x := by
  rcases List.mem_cons.mp here with h | tail
  · cases (congrArg (fun a : Registered => a.1.key.1) h)
  · have h := List.mem_singleton.mp tail
    exact ⟨congrArg (fun a : Registered => a.1.key.2) h,
      Option.some.inj (congrArg (fun a : Registered => input a.1) h),
      Option.some.inj (congrArg (fun a : Registered => payload a.1) h)⟩

private theorem upper_of_note {pp q idx msg sig} (c : Receipt pp q idx msg sig)
    {epoch b d st} (here : (FinderNotice.register .top epoch b d, st) ∈ c.notes) :
    epoch = UInt32.ofNat (bottomTree idx) ∧
      b = trialInput pp .top (UInt32.ofNat (bottomTree idx)) (packBytes c.root) sig.top.randomizer ∧
      d = selectedDigest c.y := by
  rcases List.mem_cons.mp here with h | tail
  · exact ⟨congrArg (fun a : Registered => a.1.key.2) h,
      Option.some.inj (congrArg (fun a : Registered => input a.1) h),
      Option.some.inj (congrArg (fun a : Registered => payload a.1) h)⟩
  · cases (congrArg (fun a : Registered => a.1.key.1) (List.mem_singleton.mp tail))

private theorem bounds {pp q idx msg sig} {xs : List Arrival} (c : Receipt pp q idx msg sig)
    {last : SharedState} (present : c.notes ⊆ registrations xs)
    (later : ∀ a ∈ xs, (physical a.prior).1 ≤ last) :
    (physical c.lowerPrior).1 ≤ last ∧ (physical c.upperPrior).1 ≤ last := by
  constructor
  · apply later (Arrival.note (selectedNotice pp .bottom (UInt32.ofNat idx.toNat)
      (packBytes msg) sig.bottom.randomizer c.x) c.lowerPrior)
    apply (member_register xs).mp
    exact present (List.mem_cons_of_mem _ List.mem_cons_self)
  · apply later (Arrival.note (selectedNotice pp .top (UInt32.ofNat (bottomTree idx))
      (packBytes c.root) sig.top.randomizer c.y) c.upperPrior)
    apply (member_register xs).mp
    exact present List.mem_cons_self

/-- Every registration of this lower key uses its signature's physical input and digest. -/
theorem lower_input_agreement {pp q raw xs req sig}
    (receipts : ReceiptLog pp q raw [] (registrations xs))
    (valid : Valid (eraseLog raw)) (logged : (req, Except.ok sig) ∈ raw)
    (c : Receipt pp q req.leafIndex req.message sig) (here : c.notes ⊆ registrations xs)
    {last : SharedState} (later : ∀ a ∈ xs, (physical a.prior).1 ≤ last)
      (clean : ¬ (graph pp).Conflict last) :
    ∀ b d st, Arrival.note (.register .bottom (UInt32.ofNat req.leafIndex.toNat) b d) st ∈ xs →
      b = trialInput pp .bottom (UInt32.ofNat req.leafIndex.toNat)
        (packBytes req.message) sig.bottom.randomizer ∧
        d = selectedDigest c.x := by
  intro b d st actual
  obtain pre | ⟨other, reply, log, rec, mem, all⟩ := receipts.of_register
    ((member_register xs).mpr actual)
  · cases pre
  obtain ⟨key,address,rfl⟩ := lower_of_note rec mem
  have idx : req.leafIndex = other.leafIndex := by simpa using key
  have unique : (raw.map fun a => a.1.leafIndex).Nodup := by
    simpa [Valid, eraseLog, List.map_map, Function.comp_def] using valid
  obtain ⟨rfl, rfl⟩ : req = other ∧ sig = reply := by
    have eq := Prod.mk.inj (List.inj_on_of_nodup_map unique logged log idx)
    exact ⟨eq.1, Except.ok.inj eq.2⟩
  refine ⟨address, ?_⟩
  exact Option.some.inj ((rec.lower_digest (bounds rec all later).1 clean).symm.trans
    (c.lower_digest (bounds c here later).1 clean))

/-- Every registration of this lower key records its signature's digest. -/
theorem lower_agreement {pp q raw xs req sig} (receipts : ReceiptLog pp q raw [] (registrations xs))
    (valid : Valid (eraseLog raw)) (logged : (req, Except.ok sig) ∈ raw)
    (c : Receipt pp q req.leafIndex req.message sig) (here : c.notes ⊆ registrations xs)
    {last : SharedState} (later : ∀ a ∈ xs, (physical a.prior).1 ≤ last)
      (clean : ¬ (graph pp).Conflict last) :
    ∀ b d st, Arrival.note (.register .bottom (UInt32.ofNat req.leafIndex.toNat) b d) st ∈ xs →
      d = selectedDigest c.x :=
  fun b d st mem => (lower_input_agreement receipts valid logged c here later clean b d st mem).2

private theorem nat_key {a b : LeafIndex}
    (equal : UInt32.ofNat (bottomTree a) = UInt32.ofNat (bottomTree b)) : bottomTree a =
      bottomTree b := by
  have fits (i : LeafIndex) : bottomTree i < 2 ^ 32 :=
    (bottomTree_lt i).trans_le (by decide)
  simpa only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (fits a), Nat.mod_eq_of_lt (fits b)]
    using congrArg UInt32.toNat equal

/-- Registrations at a shared upper key agree on input and digest across lower leaves. -/
theorem upper_input_agreement {pp q raw xs req sig r}
    (receipts : ReceiptLog pp q raw [] (registrations xs))
    (logged : (req, Except.ok sig) ∈ raw) (c : Receipt pp q req.leafIndex req.message sig)
    (here : c.notes ⊆ registrations xs) {last : SharedState}
    (later : ∀ a ∈ xs, (physical a.prior).1 ≤ last) (clean : ¬ (graph pp).Conflict last)
    (facts : LogFacts pp raw r last) :
    ∀ b d st, Arrival.note (.register .top (UInt32.ofNat (bottomTree req.leafIndex)) b d) st ∈ xs →
      b = trialInput pp .top (UInt32.ofNat (bottomTree req.leafIndex))
        (packBytes c.root) sig.top.randomizer ∧
        d = selectedDigest c.y := by
  intro b d st actual
  obtain pre | ⟨other,reply,log,rec,mem,all⟩ := receipts.of_register
    ((member_register xs).mpr actual)
  · cases pre
  obtain ⟨key,address,rfl⟩ := upper_of_note rec mem
  have epoch := nat_key key
  have topSig := ((facts req sig logged).same_top (facts other reply log) epoch clean).1
  have left := bounds c here later
  have right := bounds rec all later
  have old := rec.bottom_root right.1
  rw [← epoch] at old
  have roots := digestEquiv.injective (Option.some.inj (old.symm.trans (c.bottom_root left.1)))
  have dec := rec.upper_digest right.2 clean
  rw [← epoch, roots, ← topSig] at dec address
  refine ⟨address, ?_⟩
  exact Option.some.inj (dec.symm.trans (c.upper_digest left.2 clean))

/-- Registrations at a shared upper key agree on its digest across lower leaves. -/
theorem upper_agreement {pp q raw xs req sig r} (receipts : ReceiptLog pp q raw []
    (registrations xs))
    (logged : (req, Except.ok sig) ∈ raw) (c : Receipt pp q req.leafIndex req.message sig)
    (here : c.notes ⊆ registrations xs) {last : SharedState}
    (later : ∀ a ∈ xs, (physical a.prior).1 ≤ last) (clean : ¬ (graph pp).Conflict last)
    (facts : LogFacts pp raw r last) :
    ∀ b d st, Arrival.note (.register .top (UInt32.ofNat (bottomTree req.leafIndex)) b d) st ∈ xs →
      d = selectedDigest c.y :=
  fun b d st mem => (upper_input_agreement receipts logged c here later clean facts b d st mem).2

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
