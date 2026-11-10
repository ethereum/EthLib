module

public import EthLib.Cryptography.Proofs.Bls.Security.PopBound
public import EthLib.Cryptography.Proofs.Bls.Security.PopRefinement
import EthLib.Base.Proofs.Forall2

/-!
# Proofs: EthLib's BLS aggregates with proofs of possession are unforgeable, on bytes

This carries the bound of the aggregate game to the bytes that EthLib reads.

The forger sees compressed keys, hashes, signatures and proofs.

It returns bytes: keys with their proofs, a message, and an aggregate signature.

It wins if every proof passes proof verification, §3.3.3 of the BLS draft.

The honest key must be among the keys, and the message never signed.

The aggregate must pass fast aggregate verification, §3.3.4, on the message.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3>

The two hashes to `G2`, under the message tag and the key tag, are independent random oracles.

Their distinct tags separate their domains, and the model assumes them independent.

The key hash of bytes that decode to a multiple of `g1` is the game's key hash of that element.

Distinct such bytes decode to distinct elements, so this is a random oracle on them.

Other bytes get their own lazily drawn uniform answers, from the coins of the game.

Verification never hashes them, since key validation rejects them first.

The run of the game accepts a forger with any output that it reads as an aggregate forgery.

A game that wins only when the byte game wins on that reading is won at most as often.

Decoding the output gives a forger of the group game that wins at least as often.

So the group bound applies, over the scalars modulo `r`, with `qK` at most `r`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.Signatures

open scoped Classical

/-- The oracles of the group game over the multiples of the generators. -/
abbrev GroupSpec := Spec ByteArray G1Sub G2Sub

/-- A forger on bytes.

It receives the encoded honest key and proof, and its oracles answer with bytes. -/
abbrev ByteAdversary := Adversary ByteArray ByteArray ByteArray

/-- The forger's oracles, answered through the group oracles.

Coins, message hashes and signing pass through, and their answers are encoded.

A key that decodes is hashed as its group element.

Other key bytes get a uniform multiple of `g2`, drawn on the first call and kept in a cache. -/
noncomputable def encodingImpl :
    QueryImpl (Spec ByteArray ByteArray ByteArray)
      (StateT (List (ByteArray × Scalar)) (OracleComp GroupSpec))
  | .inl n => liftM (query (spec := GroupSpec) (.inl n) : OracleComp GroupSpec (Fin (n + 1)))
  | .inr (.inl (.inl m)) => liftM (G2Sub.encode <$>
      (query (spec := GroupSpec) (.inr (.inl (.inl m))) : OracleComp GroupSpec G2Sub))
  | .inr (.inl (.inr m)) => liftM (G2Sub.encode <$>
      (query (spec := GroupSpec) (.inr (.inl (.inr m))) : OracleComp GroupSpec G2Sub))
  | .inr (.inr x) => fun cache =>
    match decodeKey x with
    | some P => (fun σ => (G2Sub.encode σ, cache)) <$>
        (query (spec := GroupSpec) (.inr (.inr P)) : OracleComp GroupSpec G2Sub)
    | none =>
      match cache.lookup x with
      | some t => pure (G2Sub.encode (t • g2), cache)
      | none =>
        (fun t => (G2Sub.encode (t • g2), cache ++ [(x, t)])) <$>
          (liftM ($ᵗ Scalar : ProbComp Scalar) : OracleComp GroupSpec Scalar)

/-- Run a forger with any output on the encoded honest key and proof, through the encoded oracles.
-/
noncomputable def encodedMain {α : Type}
    (main : ByteArray → ByteArray → OracleComp (Spec ByteArray ByteArray ByteArray) α)
    (pk : G1Sub) (proof : G2Sub) : OracleComp GroupSpec α :=
  (simulateQ encodingImpl (main (G1Sub.encode pk) (G2Sub.encode proof))).run' []

/-- Run a byte forger on the encoded honest key and proof, through the encoded oracles. -/
noncomputable def byteMain (adversary : ByteAdversary) (pk : G1Sub) (proof : G2Sub) :
    OracleComp GroupSpec (List (ByteArray × ByteArray) × ByteArray × ByteArray) :=
  encodedMain adversary.main pk proof

/-- Decode the keys and proofs of a forgery.

If any key fails to decode, it returns no keys, so the group forgery loses. -/
noncomputable def decodeKeys (keys : List (ByteArray × ByteArray)) : List (G1Sub × G2Sub) :=
  (keys.mapM fun k => (decodeKey k.1).map fun x => (x, (decodeSignature k.2).getD 0)).getD []

/-- The run of the byte game for the secret scalar `a`, for a forger with any output.

The output is read as an aggregate forgery by `read`.

The honest proof is `a • H'(pk)`, with the key hash of the group game.

After the forger's run, verification hashes the message and each decoded key.

It returns the output, the hashes of verification and the final state. -/
noncomputable def runAt {α : Type}
    (main : ByteArray → ByteArray → OracleComp (Spec ByteArray ByteArray ByteArray) α)
    (read : α → List (ByteArray × ByteArray) × ByteArray × ByteArray) (a : Scalar) :
    ProbComp ((α × G2Sub × List G2Sub) × State Scalar G1Sub ByteArray) :=
  (do
    let hpk ← keyHash g2 (a • g1)
    simulateQ (impl g2 a) (do
      let out ← encodedMain main (a • g1) (a • hpk)
      let h ← query (spec := GroupSpec) (.inr (.inl (.inl (read out).2.1)))
      let hs ← (decodeKeys (read out).1).mapM fun (k : G1Sub × G2Sub) =>
        query (spec := GroupSpec) (.inr (.inr k.1))
      return (out, h, hs))).run State.init

/-- The group forger decodes the byte output.

A signature or proof that fails to decode becomes zero, which can only add wins. -/
noncomputable def ByteAdversary.toGroup (adversary : ByteAdversary) :
    Adversary G1Sub G2Sub ByteArray where
  main pk proof := (fun out => (decodeKeys out.1, out.2.1, (decodeSignature out.2.2).getD 0)) <$>
    byteMain adversary pk proof

/-- Whether a byte forgery wins against the key `pk`, given the hashes of verification.

The hashes are that of the message and that of each decoded key, in order.

The honest key's encoding is among the keys, and the message was never signed.

Every proof passes the proof check on its key's hash.

The aggregate passes fast aggregate verification on the message hash. -/
noncomputable def byteWins (pk : G1Sub) (signed : List ByteArray)
    (out : List (ByteArray × ByteArray) × ByteArray × ByteArray) (h : G2Sub) (hs : List G2Sub) :
    Bool :=
  let (keys, m, sig) := out
  decide (G1Sub.encode pk ∈ keys.map Prod.fst) && decide (m ∉ signed) &&
    decide (hs.length = keys.length) &&
    (keys.zip hs).all (fun (k, h') => byteVerify k.1 k.2 h') &&
    byteFastAggregateVerify (keys.map Prod.fst).toArray sig h

/-- The byte game for the secret scalar `a`.

The honest proof is `a • H'(pk)`, with the key hash of the group game.

After the forger's run, verification hashes the message and each decoded key. -/
noncomputable def byteExperimentAt (adversary : ByteAdversary) (a : Scalar) :
    ProbComp (Bool × State Scalar G1Sub ByteArray) :=
  (fun z => (byteWins (a • g1) z.2.msg.signed z.1.1 z.1.2.1 z.1.2.2, z.2)) <$>
    runAt adversary.main id a

/-- The byte game draws the secret scalar uniformly, as the group game does.

It includes the scalar 0, which is not an EthLib secret key. -/
noncomputable def byteExperiment (adversary : ByteAdversary) :
    ProbComp (Bool × State Scalar G1Sub ByteArray) := do
  let a ← $ᵗ Scalar
  byteExperimentAt adversary a

/-- The probability that a byte forger wins. -/
noncomputable def byteForgeAdvantage (adversary : ByteAdversary) : ℝ≥0∞ :=
  Pr{let z ← byteExperiment adversary}[z.1 = true]

/-- Every run of the byte game makes at most `q` message hash calls and `qK` key hash calls.

The counts include signing, the honest proof and verification.

The key count leaves out the hashes of bytes that do not decode to a multiple of `g1`. -/
def ByteHashCallBound (adversary : ByteAdversary) (q qK : ℕ) : Prop :=
  ∀ z ∈ support (byteExperiment adversary), z.2.msg.calls ≤ q ∧ z.2.keyCalls ≤ qK

/-! ## From bytes to the group game -/

/-- If every key decodes, the keys and proofs decode, with the decoded keys first. -/
private theorem exists_mapM_decode : ∀ (keys : List (ByteArray × ByteArray)) (xs : List G1Sub),
    (keys.map Prod.fst).mapM decodeKey = some xs →
    ∃ ys, (keys.mapM fun k => (decodeKey k.1).map fun x => (x, (decodeSignature k.2).getD 0)) =
      some ys ∧ ys.map Prod.fst = xs
  | [], xs, h => by
    simp only [List.map_nil, List.mapM_nil, pure, Option.some.injEq] at h
    exact ⟨[], rfl, h⟩
  | k :: keys, xs, h => by
    simp only [List.map_cons, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h ⊢
    obtain ⟨x, hx, xs', hxs', rfl⟩ := h
    obtain ⟨ys, hys, rfl⟩ := exists_mapM_decode keys xs' hxs'
    exact ⟨_, ⟨_, by rw [hx]; rfl, ys, hys, rfl⟩, rfl⟩

/-- Proofs that pass the byte check pass the group test once decoded. -/
private theorem all_isDh_of_forall₂ {keys : List (ByteArray × ByteArray)}
    {ys : List (G1Sub × G2Sub)}
    (h : List.Forall₂ (fun k y =>
      ((decodeKey k.1).map fun x => (x, (decodeSignature k.2).getD 0)) = some y) keys ys) :
    ∀ hs : List G2Sub, (keys.zip hs).all (fun (k, h') => byteVerify k.1 k.2 h') = true →
      (ys.zip hs).all (fun (k, h') => blsScheme.isDh k.1 h' k.2) = true := by
  induction h with
  | nil => intro hs _; rfl
  | @cons k y keys ys hk _ ih =>
    rintro (_ | ⟨h', hs⟩) hv
    · rfl
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at hv ⊢
    obtain ⟨x, hx, hd⟩ := exists_decodeKey_isDh_of_byteVerify hv.1
    rw [hx, Option.map_some, Option.some.injEq] at hk
    subst hk
    exact ⟨hd, ih hs hv.2⟩

/-- A winning byte forgery decodes to a winning group forgery, on the same hashes. -/
theorem wins_of_byteWins {pk : G1Sub} {signed : List ByteArray}
    {out : List (ByteArray × ByteArray) × ByteArray × ByteArray} {h : G2Sub} {hs : List G2Sub}
    (hw : byteWins pk signed out h hs = true) :
    wins blsScheme pk signed
      ((decodeKeys out.1, out.2.1, (decodeSignature out.2.2).getD 0), h, hs) = true := by
  obtain ⟨keys, m, sig⟩ := out
  simp only [byteWins, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨hpk, hm⟩, hlen⟩, hv⟩, hfa⟩ := hw
  obtain ⟨xs, hxs, hagg⟩ := isDh_of_byteFastAggregateVerify hfa
  rw [List.toList_toArray] at hxs
  obtain ⟨ys, hys, rfl⟩ := exists_mapM_decode keys xs hxs
  have hrel := Base.forall₂_of_mapM_some hys
  have hdec : decodeKeys keys = ys := by rw [decodeKeys, hys, Option.getD_some]
  simp only [wins, hdec, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, hm⟩, hlen.trans hrel.length_eq⟩, all_isDh_of_forall₂ hrel hs hv⟩, hagg⟩
  obtain ⟨x, hx, hdx⟩ := Base.exists_mem_of_forall₂ (Base.forall₂_of_mapM_some hxs) hpk
  rw [decodeKey_encode, Option.some.injEq] at hdx
  exact hdx ▸ hx

/-- The group run is the byte run with the output decoded, before the same verification hashes. -/
private theorem run_toGroup (adversary : ByteAdversary) (pk : G1Sub) (proof : G2Sub) :
    run adversary.toGroup pk proof =
      (fun z => ((decodeKeys z.1.1, z.1.2.1, (decodeSignature z.1.2.2).getD 0), z.2.1, z.2.2)) <$>
        (do
          let out ← byteMain adversary pk proof
          let h ← query (spec := GroupSpec) (.inr (.inl (.inl out.2.1)))
          let hs ← (decodeKeys out.1).mapM fun (k : G1Sub × G2Sub) =>
            query (spec := GroupSpec) (.inr (.inr k.1))
          return (out, h, hs)) := by
  simp only [run, ByteAdversary.toGroup, map_bind, bind_map_left, map_pure]

/-- The group game for the scalar `a` is the byte run with its output decoded. -/
private theorem run_experiment_toGroup (adversary : ByteAdversary) (a : Scalar) :
    (do
      let hpk ← keyHash g2 (a • g1)
      simulateQ (impl g2 a) (run adversary.toGroup (a • g1) (a • hpk))).run State.init =
      (fun z => (((decodeKeys z.1.1.1, z.1.1.2.1, (decodeSignature z.1.1.2.2).getD 0),
        z.1.2.1, z.1.2.2), z.2)) <$> runAt adversary.main id a := by
  simp only [run_toGroup, simulateQ_map, StateT.run_bind, StateT.run_map]
  simp only [runAt, byteMain, id, StateT.run_bind, map_bind]

/-- A byte forger wins at most as often as its decoded group forger. -/
theorem byteForgeAdvantage_le (adversary : ByteAdversary) :
    byteForgeAdvantage adversary ≤ forgeAdvantage Scalar blsScheme adversary.toGroup := by
  unfold byteForgeAdvantage forgeAdvantage byteExperiment byteExperimentAt experiment
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro a
  dsimp only
  rw [show blsScheme.g₁ = g1 from rfl, show blsScheme.g₂ = g2 from rfl, run_experiment_toGroup]
  simp only [bind_pure_comp, Functor.map_map]
  exact prEvent_mono _ _ _ fun z hw => wins_of_byteWins hw

/-- The byte game and the game of the decoded forger end in the same states.

Both make the same oracle calls, including those of verification. -/
theorem snd_map_byteExperiment (adversary : ByteAdversary) :
    Prod.snd <$> byteExperiment adversary =
      Prod.snd <$> experiment (F := Scalar) blsScheme adversary.toGroup := by
  unfold byteExperiment byteExperimentAt experiment
  rw [show blsScheme.g₁ = g1 from rfl, show blsScheme.g₂ = g2 from rfl]
  simp only [run_experiment_toGroup, map_bind, bind_pure_comp, Functor.map_map]

/-- A byte forger has a hash-call bound exactly when its decoded forger has the same bound. -/
theorem byteHashCallBound_iff (adversary : ByteAdversary) (q qK : ℕ) :
    ByteHashCallBound adversary q qK ↔ HashCallBound Scalar blsScheme adversary.toGroup q qK :=
  Security.forall_mem_support_snd_iff (snd_map_byteExperiment adversary)
    fun s => s.msg.calls ≤ q ∧ s.keyCalls ≤ qK

/-! ## Forgers with any output -/

section Read

variable {α : Type}
  (main : ByteArray → ByteArray → OracleComp (Spec ByteArray ByteArray ByteArray) α)
  (read : α → List (ByteArray × ByteArray) × ByteArray × ByteArray)

/-- Reading the output after the run is the run of the forger that reads its own output. -/
theorem map_runAt_read (a : Scalar) :
    (fun z => ((read z.1.1, z.1.2), z.2)) <$> runAt main read a =
      runAt (fun pk proof => read <$> main pk proof) id a := by
  simp only [runAt, encodedMain, StateT.run_bind, simulateQ_bind, simulateQ_map, simulateQ_pure,
    StateT.run_map, StateT.run_pure, StateT.run'_eq, map_bind, map_pure,
    bind_map_left, id]

/-- A game on the run that wins only when the byte game wins is won at most as often.

The byte game is that of the forger that reads its own output. -/
theorem prEvent_runAt_le (W : G1Sub → List ByteArray → α → G2Sub → List G2Sub → Bool)
    (hW : ∀ {pk signed x h hs}, W pk signed x h hs = true →
      byteWins pk signed (read x) h hs = true) :
    Pr{let z ← (do
        let a ← $ᵗ Scalar
        (fun (z : (α × G2Sub × List G2Sub) × State Scalar G1Sub ByteArray) =>
          (W (a • g1) z.2.msg.signed z.1.1 z.1.2.1 z.1.2.2, z.2)) <$>
          runAt main read a)}[z.1 = true] ≤
      byteForgeAdvantage ⟨fun pk proof => read <$> main pk proof⟩ := by
  unfold byteForgeAdvantage byteExperiment byteExperimentAt
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  apply MeasureTheory.lintegral_mono
  intro a
  dsimp only
  rw [← map_runAt_read]
  simp only [Functor.map_map]
  exact prEvent_mono _ _ _ fun z hw => hW hw

/-- A game on the run ends in the same states as the byte game of the forger that reads. -/
theorem snd_map_runAt (W : G1Sub → List ByteArray → α → G2Sub → List G2Sub → Bool) :
    Prod.snd <$> (do
        let a ← $ᵗ Scalar
        (fun (z : (α × G2Sub × List G2Sub) × State Scalar G1Sub ByteArray) =>
          (W (a • g1) z.2.msg.signed z.1.1 z.1.2.1 z.1.2.2, z.2)) <$>
          runAt main read a) =
      Prod.snd <$> byteExperiment ⟨fun pk proof => read <$> main pk proof⟩ := by
  unfold byteExperiment byteExperimentAt
  simp only [← map_runAt_read, map_bind, Functor.map_map]

end Read

/-- **EthLib's BLS aggregates with proofs of possession are unforgeable on bytes, from co-CDH.**

This holds in the random oracle model, for the hashes under the message and key tags.

Each run makes at most `q` message hash calls and `qK` key hash calls, with `qK` at most `r`.

The counts include signing, the honest proof and verification.

The key count leaves out bytes that do not decode to a multiple of `g1`.

Its advantage is at most `q` times that of a co-CDH solver, plus `(q + qK - 1) / r`.

The honest scalar is drawn including 0, which is never an EthLib secret key.

Given a nonzero scalar, the advantage is at most `r / (r - 1)` times as large. -/
theorem byteForgeAdvantage_le_coCdhAdvantage (adversary : ByteAdversary) {q qK : ℕ}
    (hq0 : 0 < q) (hchar : qK ≤ Fr.modulus) (hq : ByteHashCallBound adversary q qK) :
    byteForgeAdvantage adversary ≤
      q * coCdhAdvantage Scalar g1 g2 (reduction (F := Scalar) g2 adversary.toGroup q) +
        ((q + qK - 1 : ℕ) : ℝ≥0∞) * (Fr.modulus : ℝ≥0∞)⁻¹ := by
  have hb := forgeAdvantage_le blsScheme blsScheme_sound G1Sub.exists_eq_smul_g1
    adversary.toGroup hq0 (by rwa [ZMod.ringChar_zmod_n])
    ((byteHashCallBound_iff adversary q qK).mp hq)
  rw [Nat.card_zmod] at hb
  exact (byteForgeAdvantage_le adversary).trans hb

end EthLib.Cryptography.Bls.Security.Pop
