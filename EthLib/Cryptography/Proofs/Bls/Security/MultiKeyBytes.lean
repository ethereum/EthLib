module

public import EthLib.Cryptography.Proofs.Bls.Security.MultiKey
public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: EthLib's BLS signatures on bytes against several honest keys

A forger on bytes against `n` honest keys wins at most `n * q` times a co-CDH solver.

Source: the one-key game of [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), §3.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp OracleSpec ENNReal

variable {n : ℕ}

/-- A forger on bytes against `n` keys.

It sees the encoded keys and answers, and returns a key, a message and signature bytes. -/
abbrev MultiByteAdversary (n : ℕ) := MultiAdversary n ByteArray ByteArray ByteArray

/-- Encode the answers of the group oracles without changing their queries or state. -/
noncomputable def multiEncodingImpl (n : ℕ) :
    QueryImpl (MultiSpec n ByteArray ByteArray) (OracleComp (MultiSpec n ByteArray G2Sub))
  | .inl k => query (spec := MultiSpec n ByteArray G2Sub) (.inl k)
  | .inr (.inl m) => G2Sub.encode <$> query (spec := MultiSpec n ByteArray G2Sub) (.inr (.inl m))
  | .inr (.inr r) => G2Sub.encode <$> query (spec := MultiSpec n ByteArray G2Sub) (.inr (.inr r))

/-- Run a byte forger through the encodings of the honest keys and of the oracle answers. -/
noncomputable def multiByteMain (adversary : MultiByteAdversary n) (pks : Fin n → G1Sub) :
    OracleComp (MultiSpec n ByteArray G2Sub) (Fin n × ByteArray × ByteArray) :=
  simulateQ (multiEncodingImpl n) (adversary.main fun j => G1Sub.encode (pks j))

/-- The group forger decodes the signature bytes.

A decoding failure returns zero, which can only add wins to the group game. -/
noncomputable def MultiByteAdversary.toGroup (adversary : MultiByteAdversary n) :
    MultiAdversary n G1Sub G2Sub ByteArray where
  main pks := (fun (j, m, sig) => (j, m, (decodeSignature sig).getD 0)) <$>
    multiByteMain adversary pks

/-- The byte game against `n` keys, for the secret scalars `a`.

The forgery wins if key `j` never signed its message and the signature check on bytes accepts. -/
noncomputable def multiByteExperimentAt (adversary : MultiByteAdversary n) (a : Fin n → Scalar) :
    ProbComp (Bool × MultiState n Scalar ByteArray) := by
  classical
  exact do
    let pks := fun j => a j • g1
    let ((j, m, sig, h), st) ← (simulateQ (multiImpl g2 a) (do
      let (j, m, sig) ← multiByteMain adversary pks
      -- Verification hashes the message once.
      let h ← query (spec := MultiSpec n ByteArray G2Sub) (.inr (.inl m))
      return (j, m, sig, h))).run MultiState.init
    return (decide ((j, m) ∉ st.signed) && byteVerify (G1Sub.encode (pks j)) sig h, st)

/-- The byte game draws the secret scalars uniformly, zero included. -/
noncomputable def multiByteExperiment (adversary : MultiByteAdversary n) :
    ProbComp (Bool × MultiState n Scalar ByteArray) := do
  let a ← $ᵗ (Fin n → Scalar)
  multiByteExperimentAt adversary a

/-- The probability of an accepted byte forgery for a key that never signed its message. -/
noncomputable def multiByteForgeAdvantage (adversary : MultiByteAdversary n) : ℝ≥0∞ :=
  Pr{let z ← multiByteExperiment adversary}[z.1 = true]

/-- A byte forger wins at most as often as its decoded group forger.

The signing transcript is the same, so the freshness of the forgery is unchanged. -/
theorem multiByteForgeAdvantage_le (adversary : MultiByteAdversary n) :
    multiByteForgeAdvantage adversary ≤
      multiForgeAdvantage Scalar blsScheme adversary.toGroup := by
  classical
  unfold multiByteForgeAdvantage multiForgeAdvantage multiByteExperiment multiByteExperimentAt
    multiExperiment
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro a
  simp only [multiRun, MultiByteAdversary.toGroup, simulateQ_bind, simulateQ_map,
    bind_map_left, StateT.run_bind, StateT.run_map, bind_pure_comp, map_bind, Functor.map_map]
  apply prEvent_bind_mono_of_support
  rintro ⟨⟨j, m, sig⟩, st⟩ _
  apply prEvent_mono
  rintro ⟨h, st'⟩ hw
  obtain ⟨hf, hv⟩ := Bool.and_eq_true_iff.mp hw
  -- An accepted byte signature is a winning group signature for the same key and hash.
  exact Bool.and_eq_true_iff.mpr ⟨by simpa only [decide_eq_true_eq] using hf,
    isDh_of_byteVerify (a j) sig h hv⟩

/-- Every run of the byte game makes at most `q` hash calls.

That counts the forger's calls, those of signing, and the one of the final verification. -/
def MultiByteHashCallBound (adversary : MultiByteAdversary n) (q : ℕ) : Prop :=
  ∀ z ∈ support (multiByteExperiment adversary), z.2.calls ≤ q

/-- The byte game and the game of the decoded forger end in the same states.

The encoding forwards each oracle query once, so both games make the same calls. -/
theorem snd_map_multiByteExperiment (adversary : MultiByteAdversary n) :
    Prod.snd <$> multiByteExperiment adversary =
      Prod.snd <$> multiExperiment (F := Scalar) blsScheme adversary.toGroup := by
  unfold multiByteExperiment multiByteExperimentAt multiExperiment
  simp only [multiRun, MultiByteAdversary.toGroup, simulateQ_bind, simulateQ_map,
    bind_map_left, StateT.run_bind, StateT.run_map, bind_pure_comp, map_bind, Functor.map_map]
  rfl

/-- A byte forger has a hash-call bound exactly when its decoded forger has the same bound. -/
theorem multiByteHashCallBound_iff (adversary : MultiByteAdversary n) (q : ℕ) :
    MultiByteHashCallBound adversary q ↔
      MultiHashCallBound Scalar blsScheme adversary.toGroup q :=
  forall_mem_support_snd_iff (snd_map_multiByteExperiment adversary) fun s => s.calls ≤ q

/-- **EthLib's BLS signatures on bytes are unforgeable against `n` keys from co-CDH.**

This holds in the random oracle model, for a forger within `q >= 1` hash calls.

It wins at most `n * q` times as often as a named co-CDH solver. -/
theorem multiByteForgeAdvantage_le_coCdhAdvantage [NeZero n] (adversary : MultiByteAdversary n)
    {q : ℕ} (hq0 : 0 < q) (hq : MultiByteHashCallBound adversary q) :
    multiByteForgeAdvantage adversary ≤
      n * (q * coCdhAdvantage Scalar g1 g2
        (reduction (F := Scalar) g2 (adversary.toGroup.guess Scalar g1) q)) :=
  (multiByteForgeAdvantage_le adversary).trans
    (multiForgeAdvantage_le_coCdhAdvantage Scalar blsScheme blsScheme_sound adversary.toGroup hq0
      ((multiByteHashCallBound_iff adversary q).mp hq))

end EthLib.Cryptography.Bls.Security
