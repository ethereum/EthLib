module

public import EthLib.Consensus.Proofs.DirectSafety.Signatures
public import EthLib.Cryptography.Proofs.Bls.Security.MultiKeyBytes

/-!
# Proofs: a forged header call of two runs reduces to co-CDH

A forger against `n` honest keys picks two runs from one state and one header call of them.

It wins when the call names an honest key that never signed its message, and the check accepts.

The check uses the random oracle's hash of the message in place of the hash to `G2`.

It wins at most `n * q` times as often as a named co-CDH solver, within `q` hash calls.

Source: the one-key game of [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), §3.
-/

@[expose] public section

namespace EthLib.Consensus.DirectSafety

open OracleComp ENNReal Base
open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.Security

variable {preset : Preset} {n : ℕ}

/-- The output of a forger: a configuration, the checks, two runs from one state, and one call. -/
structure TwoRunsForgery (preset : Preset) where
  /-- The configuration of the chain. -/
  config : Config
  /-- Any signature checks, which the forger chooses and the win does not read. -/
  checks : SignatureChecks
  /-- The genesis state of the shared run. -/
  genesis : ForkedBeaconState preset
  /-- The state where the runs split. -/
  split : ForkedBeaconState preset
  /-- The end of the left run. -/
  leftEnd : ForkedBeaconState preset
  /-- The end of the right run. -/
  rightEnd : ForkedBeaconState preset
  /-- The shared run, from the genesis state to the split. -/
  shared : Run config checks genesis split
  /-- The left run, from the split. -/
  left : Run config checks split leftEnd
  /-- The right run, from the split. -/
  right : Run config checks split rightEnd
  /-- The call that the forger claims: a key, a message and a signature. -/
  call : BLSPubkey × ByteArray × BLSSignature

/-- A forger against `n` honest keys: it gets the encoded keys and the oracles of the game. -/
structure TwoRunsAdversary (preset : Preset) (n : ℕ) where
  /-- The forger's run. -/
  main : (Fin n → ByteArray) →
    OracleComp (MultiSpec n ByteArray ByteArray) (TwoRunsForgery preset)

/-- Whether a forgery wins against the encoded honest keys `pks`, given the hash `h` of its message.

The signed list holds each signing request, with the key that signed and the message. -/
def TwoRunsForgery.Wins (f : TwoRunsForgery preset) (pks : Fin n → ByteArray)
    (signed : List (Fin n × ByteArray)) (h : G2Sub) : Prop :=
  -- The call is a header call of one of the two runs.
  f.call ∈ verifyCalls (f.shared.append f.left) ∪ verifyCalls (f.shared.append f.right) ∧
    -- It names an honest key, and no honest key with those bytes signed its message.
    (∃ j, pks j = packBytes f.call.1) ∧
    (∀ j, pks j = packBytes f.call.1 → (j, f.call.2.1) ∉ signed) ∧
    -- The check on bytes accepts it with the oracle's hash of the message.
    byteVerify (packBytes f.call.1) (packBytes f.call.2.2) h = true

/-- The game for the secret scalars `a`: the forger's run, then the hash of the call's message. -/
noncomputable def twoRunsExperimentAt (adversary : TwoRunsAdversary preset n)
    (a : Fin n → Scalar) : ProbComp (Bool × MultiState n Scalar ByteArray) := by
  classical
  exact do
    let pks := fun j => a j • g1
    let ((f, h), st) ← (simulateQ (multiImpl g2 a) (do
      let f ← simulateQ (multiEncodingImpl n) (adversary.main fun j => G1Sub.encode (pks j))
      let h ← query (spec := MultiSpec n ByteArray G2Sub) (.inr (.inl f.call.2.1))
      return (f, h))).run MultiState.init
    return (decide (f.Wins (fun j => G1Sub.encode (pks j)) st.signed h), st)

/-- The game draws the secret scalars uniformly, zero included. -/
noncomputable def twoRunsExperiment (adversary : TwoRunsAdversary preset n) :
    ProbComp (Bool × MultiState n Scalar ByteArray) := do
  let a ← $ᵗ (Fin n → Scalar)
  twoRunsExperimentAt adversary a

/-- The probability that the forger's call of two runs forges an honest key. -/
noncomputable def twoRunsForgeAdvantage (adversary : TwoRunsAdversary preset n) : ℝ≥0∞ :=
  Pr{let z ← twoRunsExperiment adversary}[z.1 = true]

/-- Every run of the game makes at most `q` hash calls, the final one included. -/
def TwoRunsHashCallBound (adversary : TwoRunsAdversary preset n) (q : ℕ) : Prop :=
  ∀ z ∈ support (twoRunsExperiment adversary), z.2.calls ≤ q

/-- The forger read as a byte forger: an honest index of the call's key, its message and signature.

A key that names no honest key gives index `0`.

The game of two runs loses there, so the reading wins at least as often. -/
noncomputable def TwoRunsAdversary.toMulti [NeZero n] (adversary : TwoRunsAdversary preset n) :
    MultiByteAdversary n where
  main pks := (fun f => (if h : ∃ j, pks j = packBytes f.call.1 then Classical.choose h else 0,
    f.call.2.1, packBytes f.call.2.2)) <$> adversary.main pks

/-! ## The assumption on the calls of two runs -/

/-- The checks with a hash `H` to `G2`: the single check on bytes against `H` of the message.

Only their single check is used here, and they accept no aggregate. -/
noncomputable def hashChecks (H : ByteArray → G2Sub) : SignatureChecks where
  verify key message signature := byteVerify (packBytes key) (packBytes signature) (H message)
  fastAggregateVerify _ _ _ := false

/-- With the hash to `G2`, the single check is EthLib's. -/
theorem hashChecks_hashPoint_verify :
    (hashChecks hashPoint).verify = SignatureChecks.bls.verify := by
  funext key message signature
  exact byteVerify_hashPoint key message signature

/-- A key signed a message: it is no honest key, or an honest key with its bytes signed it. -/
def HonestSigned (pks : Fin n → ByteArray) (signed : List (Fin n × ByteArray))
    (key : BLSPubkey) (message : ByteArray) : Prop :=
  (∀ j, pks j ≠ packBytes key) ∨ ∃ j, pks j = packBytes key ∧ (j, message) ∈ signed

/-- When the assumption on the header calls of two runs fails, one of their calls wins.

It wins with the hash `H` of its message. -/
theorem exists_wins_of_not_verifySoundOn (f : TwoRunsForgery preset) (pks : Fin n → ByteArray)
    (signed : List (Fin n × ByteArray)) (H : ByteArray → G2Sub)
    (hfail : ¬(hashChecks H).VerifySoundOn
      (· ∈ verifyCalls (f.shared.append f.left) ∪ verifyCalls (f.shared.append f.right))
      (HonestSigned pks signed)) :
    ∃ call, ({ f with call := call } : TwoRunsForgery preset).Wins pks signed (H call.2.1) := by
  simp only [SignatureChecks.VerifySoundOn, not_forall] at hfail
  obtain ⟨key, message, signature, hcall, haccept, hunsigned⟩ := hfail
  simp only [HonestSigned, not_or, not_forall, not_not, not_exists, not_and] at hunsigned
  obtain ⟨⟨j, hj⟩, hfresh⟩ := hunsigned
  exact ⟨(key, message, signature), hcall, ⟨j, hj⟩, hfresh, haccept⟩

/-- When the assumption on the header calls fails for EthLib's checks, one of the calls wins.

It wins with the hash to `G2` of its message in place of the oracle's. -/
theorem exists_wins_of_not_bls_verifySoundOn (f : TwoRunsForgery preset)
    (pks : Fin n → ByteArray) (signed : List (Fin n × ByteArray))
    (hfail : ¬SignatureChecks.bls.VerifySoundOn
      (· ∈ verifyCalls (f.shared.append f.left) ∪ verifyCalls (f.shared.append f.right))
      (HonestSigned pks signed)) :
    ∃ call, ({ f with call := call } : TwoRunsForgery preset).Wins pks signed
      (hashPoint call.2.1) :=
  -- The assumption reads only the single check, which is the same for both checks.
  exists_wins_of_not_verifySoundOn f pks signed hashPoint fun hsound =>
    hfail fun key message signature hcall haccept =>
      hsound key message signature hcall
        ((congrFun (congrFun (congrFun hashChecks_hashPoint_verify key) message)
          signature).trans haccept)

/-! ## The bound -/

/-- A winning call is a winning byte forgery for the same hash and signing requests. -/
theorem multiWins_of_wins [NeZero n] {f : TwoRunsForgery preset} {pks : Fin n → ByteArray}
    {signed : List (Fin n × ByteArray)} {h : G2Sub} (hw : f.Wins pks signed h) :
    (if hj : ∃ j, pks j = packBytes f.call.1 then Classical.choose hj else 0,
      f.call.2.1) ∉ signed ∧
    byteVerify (pks (if hj : ∃ j, pks j = packBytes f.call.1 then Classical.choose hj else 0))
      (packBytes f.call.2.2) h = true := by
  obtain ⟨-, hhonest, hfresh, hverify⟩ := hw
  rw [dite_eq_left hhonest]
  -- The chosen index is an honest key with the call's bytes.
  have hkey := Classical.choose_spec hhonest
  rw [hkey]
  exact ⟨hfresh _ hkey, hverify⟩

/-- A forger of two runs wins at most as often as its reading as a byte forger. -/
theorem twoRunsForgeAdvantage_le [NeZero n] (adversary : TwoRunsAdversary preset n) :
    twoRunsForgeAdvantage adversary ≤ multiByteForgeAdvantage adversary.toMulti := by
  classical
  unfold twoRunsForgeAdvantage multiByteForgeAdvantage twoRunsExperiment multiByteExperiment
    twoRunsExperimentAt multiByteExperimentAt
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro a
  simp only [multiByteMain, TwoRunsAdversary.toMulti, simulateQ_bind, simulateQ_map,
    bind_map_left, StateT.run_bind, StateT.run_map, bind_pure_comp, map_bind, Functor.map_map]
  apply prEvent_bind_mono_of_support
  rintro ⟨f, st⟩ _
  apply prEvent_mono
  rintro ⟨h, st'⟩ hw
  obtain ⟨hfresh, hverify⟩ := multiWins_of_wins (of_decide_eq_true hw)
  exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true hfresh, hverify⟩

/-- The game ends in the same states as the byte game of the forger's reading. -/
theorem snd_map_twoRunsExperiment [NeZero n] (adversary : TwoRunsAdversary preset n) :
    Prod.snd <$> twoRunsExperiment adversary =
      Prod.snd <$> multiByteExperiment adversary.toMulti := by
  unfold twoRunsExperiment multiByteExperiment twoRunsExperimentAt multiByteExperimentAt
  simp only [multiByteMain, TwoRunsAdversary.toMulti, simulateQ_bind, simulateQ_map,
    bind_map_left, StateT.run_bind, StateT.run_map, bind_pure_comp, map_bind, Functor.map_map]

/-- **An accepted header call of two runs rarely forges one of `n` honest keys.**

This holds in the random oracle model, for a forger within `q >= 1` hash calls.

It wins at most `n * q` times as often as a named co-CDH solver. -/
theorem twoRunsForgeAdvantage_le_coCdhAdvantage [NeZero n] (adversary : TwoRunsAdversary preset n)
    {q : ℕ} (hq0 : 0 < q) (hq : TwoRunsHashCallBound adversary q) :
    twoRunsForgeAdvantage adversary ≤
      n * (q * coCdhAdvantage Scalar g1 g2
        (reduction (F := Scalar) g2 (adversary.toMulti.toGroup.guess Scalar g1) q)) :=
  (twoRunsForgeAdvantage_le adversary).trans
    (multiByteForgeAdvantage_le_coCdhAdvantage adversary.toMulti hq0
      ((forall_mem_support_snd_iff (snd_map_twoRunsExperiment adversary)
        fun s => s.calls ≤ q).mp hq))

end EthLib.Consensus.DirectSafety
