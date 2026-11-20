module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PostSigning
public import VCVio.OracleComp.QueryTracking.RandomOracle.MarkedReplies.Registration

/-!
# Message queries after a digest is recorded for signing

The leanXMSS draft in "Hashing and parameters" hashes the message address with its layer and key.

A caller can record a digest once it is known and keep issuing hash queries at any address.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning

open Constants OracleComp OracleSpec HashSig CachedCodeword
open scoped ENNReal

/-- The layer and key of a genuine message input, if the entire input has such an encoding. -/
noncomputable def messageKey (pp : PublicParam) (b : HashInput) : Option (Layer × UInt32) := by
  classical
  exact if h : ∃ k : Layer × UInt32, ∃ m r, trialInput pp k.1 k.2 m r = b then some h.choose
    else none

/-- A query by the real message digest function always watches its actual layer and OTS key. -/
theorem messageKey_trial (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : Randomizer) : messageKey pp (trialInput pp l e m r) = some (l, e) := by
  classical
  unfold messageKey
  split
  next h =>
    obtain ⟨n, s, same⟩ := h.choose_spec
    obtain ⟨layer, key⟩ := trial_key same
    exact congrArg some (Prod.ext layer key)
  next h => exact False.elim (h ⟨(l, e), m, r, rfl⟩)

/-- The extra operation records a digest at one layer and key. -/
abbrev WatchQueries := randomOracle.Targets.Queries HashSpec HashInput

/-- The ordinary random-oracle cache together with the current signing targets and match count. -/
abbrev WatchState := randomOracle.Targets.State HashSpec (Layer × UInt32) Digest

/-- Each genuine message trial uses the low half of the 32-byte word. -/
@[expose] def low (_ : HashInput) (w : HashOutput) := halfOf 0 (ofOutput w)

/-- Record the selected digest only when its actual physical input already holds a valid codeword. -/
@[expose] noncomputable def record (pp : PublicParam) :
    randomOracle.Targets.Register HashSpec HashInput (Layer × UInt32) Digest :=
  fun b cache old => match messageKey pp b, cache b with
    | some key, some w =>
      if (digits w).isSome then Function.update old key (some (low b w)) else old
    | _, _ => old

/-- A successful trial records exactly the low digest from the existing cache. -/
theorem record_trial (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray) (r : Randomizer)
    (cache : HashSpec.QueryCache) (w : HashOutput) (old : (Layer × UInt32) → Option Digest)
    (present : cache (trialInput pp l e m r) = some w) (valid : (digits w).isSome) :
    record pp (trialInput pp l e m r) cache old (l, e) = some (halfOf 0 (ofOutput w)) := by
  simp [record, messageKey_trial, present, valid, low]

/-- Bound a digest match over arbitrarily interleaved registrations, hashes and private coins.

Only fresh message queries made after a target was registered count toward q. -/
theorem prEvent_registered_match {α : Type} (pp : PublicParam) (caller : OracleComp WatchQueries α)
    (s : WatchState) (clean : s.hit = false) (q : Nat) :
    Pr{let z ← (simulateQ (randomOracle.Targets.impl (record pp) (messageKey pp) low) caller).run s}[
      z.2.hit = true ∧ z.2.paid ≤ q] ≤ (q : ℝ≥0∞) / 2 ^ 128 := by
  apply le_trans (randomOracle.Targets.prEvent_hit_and_paid _ _ _ ((1 : ℝ≥0∞) / 2 ^ 128)
    (by norm_num) ?_ caller s clean q)
  · simp [div_eq_mul_inv]
  · intro b k _ d
    unfold low
    rw [prEvent_halfOf_ofOutput (fun h => h = d)]
    simp

/-- Registering signing targets does not change the ordinary caller's result or its public cache. -/
theorem erase_registered {α : Type} (pp : PublicParam) (caller : OracleComp WatchQueries α)
    (s : WatchState) :
    (fun z => (z.1, z.2.cache)) <$>
        (simulateQ (randomOracle.Targets.impl (record pp) (messageKey pp) low) caller).run s =
      (simulateQ randomOracle.Targets.erase caller).run s.cache :=
  randomOracle.Targets.erase_run _ _ _ _ _

/-- The scheme's message hash asks exactly the public byte input monitored for this trial. -/
theorem messageDigest_query (pp : PublicParam) (l : Layer) (e : UInt32) (m : ByteArray)
    (r : Randomizer) :
    messageDigest (queryH (m := OracleComp WatchQueries)) pp l e m r =
      low (trialInput pp l e m r) <$>
        (query (spec := WatchQueries) (.inl (.inr (trialInput pp l e m r)))) := by
  simp [messageDigest, th, queryH, HashSig.oracleHash, trialInput, Functor.map_map]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.PostSigning
