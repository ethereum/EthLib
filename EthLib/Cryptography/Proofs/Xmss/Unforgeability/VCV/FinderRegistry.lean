module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderNotice
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.SearchLedgerAllowance

/-!
# First finder attempts and successful signing targets

Both notices name the same signing key.

An attempt can freeze its pre-search cache without recording a digest.

A complete signature records the actual low digest which its successful finder returned.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices

open HashSig OracleSpec OracleComp Constants CachedCodeword EarlierDigest PostSigning

abbrev Registry := (Layer × UInt32) → Option Digest

/-- Every attempt books its pre-search cache, and later bookings are idempotent. -/
@[expose] def cut (n : FinderNotice) : Option (Layer × UInt32) := some n.key

/-- A success notification installs its digest at one actual signing key. -/
@[expose] noncomputable def register : FinderNotice → Registry → Registry
  | .attempt _ _ _, old => old
  | .register l e _ d, old => Function.update old (l, e) (some d)

/-- Read the target from the complete bytes of a physical trial. -/
@[expose] noncomputable def target (pp : PublicParam) (old : Registry)
    (b : HashInput) : Option Digest :=
  (messageKey pp b).bind old

/-- There is no registered target before the first signature. -/
@[simp] theorem empty_target (pp : PublicParam) (b : HashInput) :
    target pp (fun _ => none) b = none := by simp [target]

/-- Every newly registered key is part of that same notice's first-attempt ledger. -/
theorem tracks (pp : PublicParam) :
    EarlierDigest.Ledger.TracksRegistration pp cut register (fun r b =>
      (target pp r b).isSome) := by
  intro n old b k key marked
  cases n with
  | attempt l e msg => exact Or.inl marked
  | register l e input digest =>
    by_cases same : k = (l, e)
    · exact Or.inr (by simp [cut, FinderNotice.key, same])
    · left
      simpa [target, key, register, Function.update_of_ne same] using marked

/-- Suppose the physical input holds the selected answer.

The notice then produces the same registry as registration from the cache. -/
theorem register_matches_original (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) (x : Vector (Fin CHAIN_LENGTH) V)
    (c : HashSpec.QueryCache) (w : HashOutput) (old : Registry)
    (read : c (trialInput pp l e msg rho) = some w) (accepted : digits w = some x) :
    register (selectedNotice pp l e msg rho x) old =
      record pp (trialInput pp l e msg rho) c old := by
  have word : codeword? (halfOf 0 (ofOutput w)) = some x := accepted
  simp [selectedNotice, register, record, messageKey_trial, read, accepted,
    low, selectedDigest_eq word]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices
