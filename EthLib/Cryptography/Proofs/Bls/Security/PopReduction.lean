module

public import EthLib.Cryptography.Proofs.Bls.Security.PopEager
public import EthLib.Cryptography.Proofs.Bls.Security.PopExtract

/-!
# Proofs: the reduction for aggregates with proofs of possession, and its coupling

The reduction gets `X1 = a • g1`, `X2 = a • g2` and `Y = c • g2` from the co-CDH problem.

It gives the adversary the honest key `X1` and guesses a position `j` of the message table.

It answers the oracles itself, without the secret `a`.

- The new message at position `j` hashes to `Y`, any other to `s • g2` with `s` fresh.
- A signature on a message with hash `s • g2` is `s • X2`, which is `a • (s • g2)`.
- At position `j` it cannot sign, and returns 0.
- The honest key hashes to `s • g2`, so its proof is `s • X2`.
- Any other key hashes to `r • Y`, with `r` fresh and kept in the key table.

The reduction's answer is the extraction step, with the key scalars `r` read from its key table.

The coupling compares it with the game whose message scalar at `j` is drawn first, as `z`.

Let `c = z` and `z ≠ 0`.

Each step of the game, seen through a map of states, is at most as likely as the reduction's step.

- A message scalar is the same, except the one at `j`: the game keeps `z`, the reduction 0.
- A key scalar `t` of a key other than the honest one is `r * z`, a bijection in `r`.

This holds until the bad event of the single-key reduction: the message at `j` was signed.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

open OracleComp OracleSpec ENNReal

variable {F G₁ G₂ M : Type} [DecidableEq M] [DecidableEq G₁] [Field F] [SampleableType F]
  [AddCommGroup G₂] [Module F G₂]

/-! ## The reduction -/

/-- The reduction's message hash: the new message at position `j` hashes to `Y`.

Its table keeps the scalar 0 at position `j`, and every other new message gets a fresh scalar. -/
def embedHashAt (g₂ Y : G₂) (j : ℕ) (m : M) : StateT (Security.State F M) ProbComp G₂ :=
  fun st =>
    match lookup m st.table with
    | some (k, s) => pure (embed g₂ Y j k s, { st with calls := st.calls + 1 })
    | none =>
      if st.table.length = j then
        pure (Y, { st with table := st.table ++ [(m, 0)], calls := st.calls + 1 })
      else embedHash g₂ Y j m st

/-- The reduction's signing oracle: `s • X2` for a message with hash `s • g2`, and 0 at `j`. -/
def embedSignAt (g₂ X₂ Y : G₂) (j : ℕ) (m : M) : StateT (Security.State F M) ProbComp G₂ :=
  fun st =>
    (fun w => (embedSignature X₂ j m w.2, { w.2 with signed := w.2.signed ++ [m] })) <$>
      embedHashAt g₂ Y j m st

/-- The reduction's answer for a key hash with scalar `s`: `s • g2` for `pk`, `s • Y` otherwise. -/
def keyAnswer (g₂ Y : G₂) (pk x : G₁) (s : F) : G₂ := if x = pk then s • g₂ else s • Y

/-- The reduction's key hash: a new key gets a fresh scalar `s`, kept in the key table. -/
def embedKeyHash (g₂ Y : G₂) (pk x : G₁) : StateT (State F G₁ M) ProbComp G₂ := fun st =>
  match lookup x st.keyTable with
  | some (_, s) => pure (keyAnswer g₂ Y pk x s, { st with keyCalls := st.keyCalls + 1 })
  | none =>
    (fun s => (keyAnswer g₂ Y pk x s,
      { st with keyTable := st.keyTable ++ [(x, s)], keyCalls := st.keyCalls + 1 })) <$>
      ($ᵗ F)

/-- The oracles of the reduction, for the honest key `pk` and the guess `j`. -/
def embedImpl (g₂ X₂ Y : G₂) (pk : G₁) (j : ℕ) :
    QueryImpl (Spec M G₁ G₂) (StateT (State F G₁ M) ProbComp)
  | .inl n => fun st => (·, st) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl (.inl m)) => (onMsg (embedHashAt g₂ Y j m) : StateT (State F G₁ M) ProbComp G₂)
  | .inr (.inl (.inr m)) =>
    (onMsg (embedSignAt g₂ X₂ Y j m) : StateT (State F G₁ M) ProbComp G₂)
  | .inr (.inr x) => (embedKeyHash g₂ Y pk x : StateT (State F G₁ M) ProbComp G₂)

/-- The state after the hash of the honest key `pk` with scalar `s`, the first key hash call. -/
def State.withKey (pk : G₁) (s : F) : State F G₁ M := ⟨Security.State.init, [(pk, s)], 1⟩

/-- The scalar of the key hash of `x` in the key table, or 0 when `x` was never hashed. -/
def keyScalar (x : G₁) (st : State F G₁ M) : F :=
  match lookup x st.keyTable with
  | some (_, s) => s
  | none => 0

/-- The reduction's answer: the extraction step, when the forged message is at position `j`.

It reads the scalar of each key hash from the final key table.

Otherwise it is 0. -/
def extract (pk : G₁) (j : ℕ) (w : (List (G₁ × G₂) × M × G₂) × G₂ × List G₂)
    (st : State F G₁ M) : G₂ :=
  match lookup w.1.2.1 st.msg.table with
  | some (k, _) => if k = j then extractAggregate pk (keyScalar · st) w.1.1 w.1.2.2 else 0
  | none => 0

/-- The co-CDH solver built from an aggregate forger, for a budget of `q` message hash calls.

It guesses `j`, records a fresh scalar `s` for the honest key, and gives the proof `s • X2`. -/
def reduction (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (q : ℕ) : CoCdhAdversary G₁ G₂ :=
  fun X₁ X₂ Y => do
    let j ← $[0..q - 1]
    let s ← $ᵗ F
    let (w, st) ← (simulateQ (embedImpl g₂ X₂ Y X₁ j) (run adversary X₁ (s • X₂))).run
      (State.withKey X₁ s)
    return extract X₁ j w st

/-! ## The coupling with the game -/

/-- The key table with the scalar of every key other than `pk` multiplied by `u`. -/
def scaleKeys (pk : G₁) (u : F) (l : List (G₁ × F)) : List (G₁ × F) :=
  l.map fun e => (e.1, if e.1 = pk then e.2 else e.2 * u)

/-- The game's state as the reduction sees it, when the message scalar at `j` is `z`.

The message scalar at `j` becomes 0.

The scalar of every key other than `pk` is divided by `z`.

This is meant for `z ≠ 0`; at `z = 0` those scalars become 0. -/
def projectState (pk : G₁) (j : ℕ) (z : F) (st : State F G₁ M) : State F G₁ M :=
  ⟨shiftState z j st.msg, scaleKeys pk z⁻¹ st.keyTable, st.keyCalls⟩

omit [SampleableType F] in
/-- The scaling keeps every position, and scales the scalar of a key other than `pk`. -/
theorem lookup_scaleKeys (pk x : G₁) (u : F) (l : List (G₁ × F)) :
    lookup x (scaleKeys pk u l) =
      (lookup x l).map fun p => (p.1, if x = pk then p.2 else p.2 * u) := by
  induction l with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨y, t⟩ := e
    simp only [scaleKeys, List.map_cons] at ih ⊢
    simp only [lookup]
    by_cases hy : y = x
    · subst hy
      simp
    · simp only [hy, ↓reduceIte, ih, Option.map_map]
      rfl

omit [DecidableEq M] [SampleableType F] in
/-- The projection keeps the state after the honest key hash. -/
theorem projectState_withKey (pk : G₁) (j : ℕ) (z s : F) :
    projectState pk j z (State.withKey (M := M) pk s) = State.withKey pk s := by
  simp [projectState, State.withKey, scaleKeys, shiftState, shift, Security.State.init]

/-- Away from a new message at position `j`, the reduction's message hash is the one for one key. -/
theorem embedHashAt_eq_embedHash {g₂ Y : G₂} {j : ℕ} {m : M} {st : Security.State F M}
    (h : lookup m st.table = none → st.table.length ≠ j) :
    embedHashAt g₂ Y j m st = embedHash g₂ Y j m st := by
  unfold embedHashAt
  split
  · next k s hl => rw [embedHash_of_lookup_some hl]
  · next hl => simp [h hl]

/-- The reduction hashes a new message at position `j` to `Y`, with the scalar 0. -/
theorem embedHashAt_of_new {g₂ Y : G₂} {j : ℕ} {m : M} {st : Security.State F M}
    (hl : lookup m st.table = none) (hj : st.table.length = j) :
    embedHashAt g₂ Y j m st =
      pure (Y, { st with table := st.table ++ [(m, 0)], calls := st.calls + 1 }) := by
  unfold embedHashAt
  simp [hl, hj]

/-- One message hash call of the game with the scalar `z` at `j` is one call of the reduction.

The reduction gets `Y = z • g2`.

This holds once the game's table is shifted by `z` at `j`. -/
theorem prEvent_hashAt_shift (g₂ : G₂) (j : ℕ) (z : F) (m : M) (st : Security.State F M)
    (Φ : G₂ × Security.State F M → Prop) :
    Pr{let w ← hashAt g₂ j z m st}[Φ (w.1, shiftState z j w.2)] =
      Pr{let w ← embedHashAt g₂ (z • g₂) j m (shiftState z j st)}[Φ w] := by
  by_cases hnew : lookup m st.table = none ∧ st.table.length = j
  · have hl : lookup m (shiftState z j st).table = none := by
      simp [shiftState, lookup_shift, hnew.1]
    have hlen : (shiftState z j st).table.length = j := by
      simp [shiftState, length_shift, hnew.2]
    rw [hashAt_of_new hnew.1 hnew.2, embedHashAt_of_new hl hlen]
    simp [shiftState, shift_append, hnew.2]
  · have hl : lookup m (shiftState z j st).table = none →
        (shiftState z j st).table.length ≠ j := by
      intro hl hj
      simp only [shiftState, lookup_shift, Option.map_eq_none_iff, length_shift] at hl hj
      exact hnew ⟨hl, hj⟩
    rw [hashAt_eq_hash fun hl hj => hnew ⟨hl, hj⟩, embedHashAt_eq_embedHash hl]
    exact prEvent_hash_shift g₂ z j m st Φ

/-- Under the oracles with a fixed scalar at `j`, a signed message at `j` stays signed. -/
theorem implAt_preservesInv_bad (g₂ : G₂) (a : F) (j : ℕ) (z : F) :
    QueryImpl.PreservesInv (implAt (M := M) (G₁ := G₁) g₂ a j z) fun st => Bad j st.msg := by
  intro t st hbad x hx
  obtain ⟨r, hr, hsub⟩ : ∃ r, x.2.msg.table = st.msg.table ++ r ∧
      st.msg.signed ⊆ x.2.msg.signed := by
    rcases t with n | (m | m) | y
    · change x ∈ support ((·, st) <$> _) at hx
      simp only [support_map, Set.mem_image] at hx
      obtain ⟨_, -, rfl⟩ := hx
      exact ⟨[], by simp, fun _ h => h⟩
    · change x ∈ support ((fun w => _) <$> hashAt g₂ j z m st.msg) at hx
      simp only [support_map, Set.mem_image] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨-, ⟨r, hr⟩, hsigned⟩ := mem_support_hashAt hw
      exact ⟨r, hr, fun _ h => hsigned ▸ h⟩
    · change x ∈ support ((fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg)) at hx
      simp only [support_map, Set.mem_image] at hx
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
      obtain ⟨-, ⟨r, hr⟩, hsigned⟩ := mem_support_hashAt hw
      exact ⟨r, hr, fun _ h => by simp [hsigned, h]⟩
    · change x ∈ support (keyHash g₂ y st) at hx
      unfold keyHash at hx
      split at hx
      · simp only [support_pure, Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨[], by simp, fun _ h => h⟩
      · simp only [support_map, Set.mem_image] at hx
        obtain ⟨_, -, rfl⟩ := hx
        exact ⟨[], by simp, fun _ h => h⟩
  exact hbad.mono hr hsub

omit [DecidableEq M] in
/-- One key hash call of the game, seen through the projection, is one of the reduction.

The reduction gets `Y = z • g2`. -/
theorem prEvent_keyHash_projectState (g₂ : G₂) (pk : G₁) (j : ℕ) {z : F} (hz : z ≠ 0) (x : G₁)
    (st : State F G₁ M) (Φ : G₂ × State F G₁ M → Prop) :
    Pr{let w ← keyHash g₂ x st}[Φ (w.1, projectState pk j z w.2)] =
      Pr{let w ← embedKeyHash g₂ (z • g₂) pk x (projectState pk j z st)}[Φ w] := by
  have hl : lookup x (projectState pk j z st).keyTable =
      (lookup x st.keyTable).map fun p => (p.1, if x = pk then p.2 else p.2 * z⁻¹) :=
    lookup_scaleKeys pk x z⁻¹ st.keyTable
  unfold keyHash embedKeyHash
  cases h : lookup x st.keyTable with
  | some p =>
    rw [h, Option.map_some] at hl
    rw [hl]
    obtain ⟨k, t⟩ := p
    dsimp only
    by_cases hx : x = pk
    · simp [projectState, keyAnswer, hx]
    · simp [projectState, keyAnswer, hx, smul_smul, hz]
  | none =>
    rw [h, Option.map_none] at hl
    rw [hl]
    dsimp only
    rw [prEvent_map, prEvent_map]
    by_cases hx : x = pk
    · refine prEvent_congr _ _ _ fun t => ?_
      simp [projectState, scaleKeys, keyAnswer, hx]
    · conv_rhs => rw [← SampleableType.prEvent_uniformSample_equiv
        (Equiv.mulRight₀ z⁻¹ (inv_ne_zero hz))]
      refine prEvent_congr _ _ _ fun t => ?_
      simp [projectState, scaleKeys, keyAnswer, hx, smul_smul, hz]

/-- Before the bad event, each step of the game is at most as likely as the reduction's step.

The game has the scalar `z ≠ 0` at `j`, and its states are seen through the projection.

The reduction gets `X2 = a • g2` and `Y = z • g2`. -/
theorem dominatedUntilBad (g₂ : G₂) (pk : G₁) (a : F) {z : F} (hz : z ≠ 0) (j : ℕ) :
    QueryImpl.DominatedUntilBad (implAt (M := M) (G₁ := G₁) g₂ a j z)
      (embedImpl g₂ (a • g₂) (z • g₂) pk j) (projectState pk j z) (fun _ => True)
      (fun st => Bad j st.msg) := by
  intro t st _ hst Q
  rcases t with n | (m | m) | x
  · change Pr{let w ← (·, st) <$> _}[_] ≤ Pr{let w ← (·, projectState pk j z st) <$> _}[_]
    rw [prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · change Pr{let w ← (fun w => (w.1, { st with msg := w.2 })) <$> hashAt g₂ j z m st.msg}[
        Q (w.1, projectState pk j z w.2) ∧ _] ≤
      Pr{let w ← (fun w => (w.1, { projectState pk j z st with msg := w.2 })) <$>
        embedHashAt g₂ (z • g₂) j m (shiftState z j st.msg)}[Q w]
    rw [prEvent_map, prEvent_map]
    exact (prEvent_mono _ _ _ fun _ h => h.1).trans (prEvent_hashAt_shift g₂ j z m st.msg
      fun w => Q (w.1, { projectState pk j z st with msg := w.2 })).le
  · change Pr{let w ← (fun w => (w.1, { st with msg := w.2 })) <$>
          ((fun w => (a • w.1, { w.2 with signed := w.2.signed ++ [m] })) <$>
            hashAt g₂ j z m st.msg)}[Q (w.1, projectState pk j z w.2) ∧ ¬Bad j w.2.msg] ≤
      Pr{let w ← (fun w => (w.1, { projectState pk j z st with msg := w.2 })) <$>
        ((fun w => (embedSignature (a • g₂) j m w.2, { w.2 with signed := w.2.signed ++ [m] })) <$>
          embedHashAt g₂ (z • g₂) j m (shiftState z j st.msg))}[Q w]
    rw [prEvent_map, prEvent_map, prEvent_map, prEvent_map]
    let Q' : G₂ × State F G₁ M → Prop := Q
    have hshift := prEvent_hashAt_shift g₂ j z m st.msg fun w =>
      Q' (embedSignature (a • g₂) j m w.2,
        { projectState pk j z st with msg := { w.2 with signed := w.2.signed ++ [m] } })
    refine le_trans ?_ hshift.le
    refine prEvent_mono_of_support _ _ _ fun w hw ⟨hQ, hbad⟩ => ?_
    obtain ⟨⟨k, t, hk, hw1⟩, -⟩ := mem_support_hashAt hw
    rw [embedSignature_shiftState_of_not_bad hk hbad, ← hw1]
    exact hQ
  · change Pr{let w ← keyHash g₂ x st}[Q (w.1, projectState pk j z w.2) ∧ _] ≤
      Pr{let w ← embedKeyHash g₂ (z • g₂) pk x (projectState pk j z st)}[Q w]
    exact (prEvent_mono _ _ _ fun _ h => h.1).trans
      (prEvent_keyHash_projectState g₂ pk j hz x st Q).le

/-- The game's run with the scalar `z ≠ 0` at `j` is bounded by the reduction's run.

An event of the game, seen through the projection and without the bad event, is at most as likely.

The reduction starts from the projected state. -/
theorem prEvent_run_projectState_le (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (pk : G₁) (a : F)
    {z : F} (hz : z ≠ 0) (j : ℕ) (proof : G₂) (st : State F G₁ M)
    (P : ((List (G₁ × G₂) × M × G₂) × G₂ × List G₂) × State F G₁ M → Prop) :
    Pr{let w ← (simulateQ (implAt g₂ a j z) (run adversary pk proof)).run st}[
        P (w.1, projectState pk j z w.2) ∧ ¬Bad j w.2.msg] ≤
      Pr{let w ← (simulateQ (embedImpl g₂ (a • g₂) (z • g₂) pk j)
          (run adversary pk proof)).run (projectState pk j z st)}[P w] :=
  (dominatedUntilBad g₂ pk a hz j).prEvent_simulateQ_run_map_and_not_bad_le
    (fun _ _ _ _ _ => trivial) (implAt_preservesInv_bad g₂ a j z) _ st trivial P

end EthLib.Cryptography.Bls.Security.Pop
