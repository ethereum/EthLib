module

public import EthLib.Cryptography.Proofs.Bls.Security.Game
public import VCVio.OracleComp.SimSemantics.StateT.UntilBad
public import VCVio.OracleComp.Constructions.UniformFinMeasure

/-!
# Proofs: a BLS forger solves co-CDH

The reduction follows [Boneh, Lynn, Shacham](https://hovav.net/ucsd/dist/sigs.pdf), Theorem 3.2.

It takes the simple form: it guesses which hash entry the forgery uses.

The reduction gets `X1 = a • g1`, `X2 = a • g2` and `Y = c • g2`.

It gives the adversary the public key `X1`, guesses a position `j`, and answers the oracles itself.

The `j`-th new message hashes to `Y + s • g2`, any other to `s • g2`, with `s` fresh.

It signs a message with hash `s • g2` as `s • X2`, which is `a • (s • g2)`.

A forgery `σ` on the `j`-th message is `a • (Y + s • g2)`, so `σ - s • X2` is `(a * c) • g2`.

A run of at most `q` hash calls fills at most `q` positions, and the guess is uniform among them.

So a forger that wins with probability `ε` gives a solver that wins with at least `ε / q`.

The source's theorem has the factor `e * (qS + 1)` instead, for `qS` signing requests.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security

open OracleComp OracleSpec ENNReal MeasureTheory

variable {F G₁ G₂ M : Type} [DecidableEq M]

/-! ## Tables -/

/-- The entry that a lookup finds sits at the position it returns. -/
theorem getElem?_of_lookup {m : M} : ∀ {l : List (M × F)} {k : ℕ} {t : F},
    lookup m l = some (k, t) → l[k]? = some (m, t)
  | [], _, _, h => by simp [lookup] at h
  | (m', t') :: rest, k, t, h => by
    simp only [lookup] at h
    split_ifs at h with hm
    · cases h
      simp [hm]
    · obtain ⟨⟨k', t''⟩, h', he⟩ := Option.map_eq_some_iff.mp h
      cases he
      simpa using getElem?_of_lookup h'

/-- A new message appended to a table is found at the end. -/
theorem lookup_append_of_none {m : M} : ∀ {l : List (M × F)}, lookup m l = none →
    ∀ t, lookup m (l ++ [(m, t)]) = some (l.length, t)
  | [], _, t => by simp [lookup]
  | (m', t') :: rest, h, t => by
    rw [List.cons_append]
    simp only [lookup] at h ⊢
    split_ifs at h ⊢ with hm
    rw [lookup_append_of_none (by simpa using h) t]
    simp

/-- An entry that a lookup finds is still found after more entries are appended. -/
theorem lookup_append_of_some {x : M} {v : ℕ × F} :
    ∀ {l : List (M × F)} (r : List (M × F)), lookup x l = some v → lookup x (l ++ r) = some v
  | [], _, h => by simp [lookup] at h
  | (y, t) :: rest, r, h => by
    simp only [List.cons_append, lookup] at h ⊢
    split_ifs at h ⊢ with hy
    · exact h
    · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [lookup_append_of_some r hw]
      rfl


variable [CommRing F]

/-- The table with the scalar at position `j` lowered by `c`. -/
def shift (c : F) : List (M × F) → ℕ → List (M × F)
  | [], _ => []
  | (m, t) :: rest, 0 => (m, t - c) :: rest
  | e :: rest, j + 1 => e :: shift c rest j

omit [DecidableEq M] in
/-- The shift keeps the length of the table. -/
theorem length_shift (c : F) : ∀ (l : List (M × F)) (j : ℕ), (shift c l j).length = l.length
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: rest, j + 1 => congrArg (· + 1) (length_shift c rest j)

omit [DecidableEq M] in
/-- Shifting a table with one more entry shifts that entry when it sits at position `j`. -/
theorem shift_append (c : F) (e : M × F) : ∀ (l : List (M × F)) (j : ℕ),
    shift c (l ++ [e]) j = shift c l j ++ [(e.1, if l.length = j then e.2 - c else e.2)]
  | [], 0 => rfl
  | [], j + 1 => by simp [shift]
  | _ :: _, 0 => by simp [shift]
  | _ :: rest, j + 1 => by simp [shift, shift_append c e rest j]

/-- The shift keeps every position, and lowers the scalar at position `j`. -/
theorem lookup_shift (c : F) (m : M) : ∀ (l : List (M × F)) (j : ℕ),
    lookup m (shift c l j) = (lookup m l).map fun x => (x.1, if x.1 = j then x.2 - c else x.2)
  | [], _ => rfl
  | (m', t) :: rest, 0 => by
    simp only [shift, lookup]
    split_ifs <;> simp [Option.map_map, Function.comp_def]
  | (m', t) :: rest, j + 1 => by
    simp only [shift, lookup]
    split_ifs
    · simp
    · simp [lookup_shift c m rest j, Option.map_map, Function.comp_def]

variable [AddCommGroup G₂] [Module F G₂]

/-! ## The reduction -/

/-- The hash that the reduction answers for the entry at position `k` with scalar `s`. -/
def embed (g₂ Y : G₂) (j k : ℕ) (s : F) : G₂ := if k = j then Y + s • g₂ else s • g₂

/-- The reduction's answer for a shifted entry is the game's answer. -/
theorem embed_shift (g₂ : G₂) (c t : F) (j k : ℕ) :
    embed g₂ (c • g₂) j k (if k = j then t - c else t) = t • g₂ := by
  unfold embed
  split_ifs
  · rw [← add_smul, add_sub_cancel]
  · rfl

variable [SampleableType F]

/-- The reduction's random oracle: the entry at position `j` hides `Y`. -/
def embedHash (g₂ Y : G₂) (j : ℕ) (m : M) : StateT (State F M) ProbComp G₂ := fun st =>
  match lookup m st.table with
  | some (k, s) => pure (embed g₂ Y j k s, { st with calls := st.calls + 1 })
  | none =>
    (fun s => (embed g₂ Y j st.table.length s,
      { st with table := st.table ++ [(m, s)], calls := st.calls + 1 })) <$> ($ᵗ F)

/-- The reduction's answer to a signing request, from the state after the hash call.

At an entry other than `j` it is `s • X2`.

At `j` the reduction cannot sign, and returns 0. -/
def embedSignature (X₂ : G₂) (j : ℕ) (m : M) (st : State F M) : G₂ :=
  match lookup m st.table with
  | some (k, s) => if k = j then 0 else s • X₂
  | none => 0

/-- The reduction's signing oracle. -/
def embedSign (g₂ X₂ Y : G₂) (j : ℕ) (m : M) : StateT (State F M) ProbComp G₂ := fun st =>
  (fun z => (embedSignature X₂ j m z.2, { z.2 with signed := z.2.signed ++ [m] })) <$>
    embedHash g₂ Y j m st

/-- The oracles of the reduction. -/
def embedImpl (g₂ X₂ Y : G₂) (j : ℕ) : QueryImpl (Spec M G₂) (StateT (State F M) ProbComp)
  | .inl n => fun st => (·, st) <$> (query (spec := unifSpec) n : ProbComp (Fin (n + 1)))
  | .inr (.inl m) => (embedHash g₂ Y j m : StateT (State F M) ProbComp G₂)
  | .inr (.inr m) => (embedSign g₂ X₂ Y j m : StateT (State F M) ProbComp G₂)

/-- The reduction's answer: `σ - s • X2` when the forged message is the entry at `j`. -/
def extract (X₂ : G₂) (j : ℕ) (m : M) (σ : G₂) (st : State F M) : G₂ :=
  match lookup m st.table with
  | some (k, s) => if k = j then σ - s • X₂ else 0
  | none => 0

/-- The co-CDH solver built from a forger, for a budget of `q` hash calls. -/
def reduction (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (q : ℕ) : CoCdhAdversary G₁ G₂ :=
  fun X₁ X₂ Y => do
    let j ← $[0..q - 1]
    let ((m, σ, _), st) ←
      (simulateQ (embedImpl (F := F) g₂ X₂ Y j) (run adversary X₁)).run State.init
    return extract X₂ j m σ st

/-! ## The coupling with the game -/

/-- The game's state with the table shifted by `c` at position `j`. -/
def shiftState (c : F) (j : ℕ) (st : State F M) : State F M :=
  { st with table := shift c st.table j }

/-- The bad event: the message at position `j` was signed, so the reduction could not answer. -/
def Bad (j : ℕ) (st : State F M) : Prop := ∃ e, st.table[j]? = some e ∧ e.1 ∈ st.signed

omit [DecidableEq M] [CommRing F] [SampleableType F] in
/-- A state that appends to the table and keeps every signed message keeps the bad event. -/
theorem Bad.mono {j : ℕ} {st st' : State F M} {r : List (M × F)}
    (htable : st'.table = st.table ++ r) (hsigned : st.signed ⊆ st'.signed) (h : Bad j st) :
    Bad j st' := by
  obtain ⟨e, he, hs⟩ := h
  refine ⟨e, ?_, hsigned hs⟩
  rw [htable, List.getElem?_append_left (List.getElem?_eq_some_iff.mp he).1, he]

omit [SampleableType F] in
/-- Before the bad event, the reduction signs a hashed message as the game does, after the shift.

The game's signature on the hash `t • g2` is `a • (t • g2)`. -/
theorem embedSignature_shiftState_of_not_bad {g₂ : G₂} {a c : F} {j k : ℕ} {m : M} {t : F}
    {w : State F M} (hk : lookup m w.table = some (k, t))
    (hbad : ¬Bad j { w with signed := w.signed ++ [m] }) :
    embedSignature (a • g₂) j m (shiftState c j w) = a • (t • g₂) := by
  have hkj : k ≠ j := by
    rintro rfl
    exact hbad ⟨(m, t), getElem?_of_lookup hk, by simp⟩
  simp [embedSignature, shiftState, lookup_shift, hk, hkj, smul_comm a t]

/-- One hash call of the game: the answer is the scalar of the entry, times `g2`. -/
theorem mem_support_hash {g₂ : G₂} {m : M} {st : State F M} {z : G₂ × State F M}
    (hz : z ∈ support ((hash g₂ m).run st)) :
    (∃ k t, lookup m z.2.table = some (k, t) ∧ z.1 = t • g₂) ∧
      (z.2.table = st.table ∨ ∃ e, z.2.table = st.table ++ [e]) ∧
      z.2.signed = st.signed ∧ z.2.calls = st.calls + 1 := by
  change z ∈ support (hash g₂ m st) at hz
  unfold hash at hz
  split at hz
  · next k t h =>
    simp only [support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨⟨k, t, h, rfl⟩, Or.inl rfl, rfl, rfl⟩
  · next h =>
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨t, -, rfl⟩ := hz
    exact ⟨⟨_, t, lookup_append_of_none h t, rfl⟩, Or.inr ⟨_, rfl⟩, rfl, rfl⟩

/-- A step of the game only appends to the table and to the signed messages. -/
def Grows (st st' : State F M) : Prop :=
  (∃ r, st'.table = st.table ++ r) ∧ st.signed ⊆ st'.signed ∧
    st'.table.length + st.calls ≤ st.table.length + st'.calls

theorem grows_of_mem_support_impl {g₂ : G₂} {a : F} {t : (Spec M G₂).Domain}
    {st : State F M} {z} (hz : z ∈ support ((impl g₂ a t).run st)) : Grows st z.2 := by
  rcases t with n | m | m
  · change z ∈ support ((·, st) <$> _) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨x, -, rfl⟩ := hz
    exact ⟨⟨[], by simp⟩, fun _ h => h, le_refl _⟩
  · change z ∈ support ((hash (F := F) g₂ m).run st) at hz
    obtain ⟨-, htable, hsigned, hcalls⟩ := mem_support_hash hz
    refine ⟨?_, fun _ h => hsigned ▸ h, ?_⟩
    · rcases htable with h | ⟨e, h⟩
      · exact ⟨[], by simp [h]⟩
      · exact ⟨[e], h⟩
    · rcases htable with h | ⟨e, h⟩
      · simp [h, hcalls]
      · simp only [h, hcalls, List.length_append, List.length_singleton]
        omega
  · change z ∈ support ((fun z => _) <$> hash (F := F) g₂ m st) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    obtain ⟨-, htable, hsigned, hcalls⟩ := mem_support_hash (st := st) hz'
    refine ⟨?_, ?_, ?_⟩
    · rcases htable with h | ⟨e, h⟩
      · exact ⟨[], by simp [h]⟩
      · exact ⟨[e], h⟩
    · intro x hx
      simp [hsigned, hx]
    · rcases htable with h | ⟨e, h⟩
      · simp [h, hcalls]
      · simp only [h, hcalls, List.length_append, List.length_singleton]
        omega

/-- Once the message at position `j` is signed, it stays signed. -/
theorem impl_preservesInv_bad (g₂ : G₂) (a : F) (j : ℕ) :
    QueryImpl.PreservesInv (impl (M := M) g₂ a) (Bad j) := by
  intro t st hbad z hz
  obtain ⟨⟨r, hr⟩, hsigned, -⟩ := grows_of_mem_support_impl hz
  exact hbad.mono hr hsigned

/-- The table never has more entries than there were hash calls. -/
theorem impl_preservesInv_length (g₂ : G₂) (a : F) :
    QueryImpl.PreservesInv (impl (M := M) g₂ a) fun st => st.table.length ≤ st.calls := by
  intro t st hst z hz
  have := (grows_of_mem_support_impl hz).2.2
  omega

theorem hash_of_lookup_some {g₂ : G₂} {m : M} {st : State F M} {k : ℕ} {t : F}
    (h : lookup m st.table = some (k, t)) :
    hash g₂ m st = pure (t • g₂, { st with calls := st.calls + 1 }) := by
  unfold hash
  rw [h]

theorem hash_of_lookup_none {g₂ : G₂} {m : M} {st : State F M} (h : lookup m st.table = none) :
    hash g₂ m st = (fun t => (t • g₂,
      { st with table := st.table ++ [(m, t)], calls := st.calls + 1 })) <$> ($ᵗ F) := by
  unfold hash
  rw [h]

theorem embedHash_of_lookup_some {g₂ Y : G₂} {j : ℕ} {m : M} {st : State F M} {k : ℕ} {s : F}
    (h : lookup m st.table = some (k, s)) :
    embedHash g₂ Y j m st = pure (embed g₂ Y j k s, { st with calls := st.calls + 1 }) := by
  unfold embedHash
  rw [h]

theorem embedHash_of_lookup_none {g₂ Y : G₂} {j : ℕ} {m : M} {st : State F M}
    (h : lookup m st.table = none) :
    embedHash g₂ Y j m st = (fun s => (embed g₂ Y j st.table.length s,
      { st with table := st.table ++ [(m, s)], calls := st.calls + 1 })) <$> ($ᵗ F) := by
  unfold embedHash
  rw [h]

/-- One hash call of the game, seen through the shift, is one hash call of the reduction. -/
theorem prEvent_hash_shift (g₂ : G₂) (c : F) (j : ℕ) (m : M) (st : State F M)
    (Φ : G₂ × State F M → Prop) :
    Pr{let z ← hash g₂ m st}[Φ (z.1, shiftState c j z.2)] =
      Pr{let z ← embedHash g₂ (c • g₂) j m (shiftState c j st)}[Φ z] := by
  have hl : lookup m (shiftState c j st).table =
      (lookup m st.table).map fun x => (x.1, if x.1 = j then x.2 - c else x.2) :=
    lookup_shift c m st.table j
  cases h : lookup m st.table with
  | some x =>
    rw [h, Option.map_some] at hl
    rw [hash_of_lookup_some h, embedHash_of_lookup_some hl, embed_shift]
    rfl
  | none =>
    rw [h, Option.map_none] at hl
    rw [hash_of_lookup_none h, embedHash_of_lookup_none hl, prEvent_map, prEvent_map]
    -- The reduction's scalar `s` is the game's scalar `t` minus `c` at position `j`.
    rw [← SampleableType.prEvent_uniformSample_equiv
      (Equiv.addRight (if st.table.length = j then c else 0)) fun t => Φ (t • g₂, _)]
    refine prEvent_congr _ _ _ fun s => ?_
    simp only [Equiv.coe_addRight, shiftState, shift_append, length_shift, embed]
    split_ifs <;> simp [add_smul, add_comm]

theorem impl_sign_run (g₂ : G₂) (a : F) (m : M) (st : State F M) :
    (impl g₂ a (.inr (.inr m))).run st =
      (fun z => (a • z.1, { z.2 with signed := z.2.signed ++ [m] })) <$> hash g₂ m st :=
  rfl

theorem embedImpl_sign_run (g₂ X₂ Y : G₂) (j : ℕ) (m : M) (st : State F M) :
    (embedImpl g₂ X₂ Y j (.inr (.inr m))).run st =
      (fun z => (embedSignature X₂ j m z.2, { z.2 with signed := z.2.signed ++ [m] })) <$>
        embedHash g₂ Y j m st :=
  rfl

/-- Before the bad event, each step of the game, seen through the shift, is a step of the reduction.

The reduction gets `X2 = a • g2` and `Y = c • g2`. -/
theorem dominatedUntilBad (g₂ : G₂) (a c : F) (j : ℕ) :
    QueryImpl.DominatedUntilBad (impl (M := M) g₂ a) (embedImpl g₂ (a • g₂) (c • g₂) j)
      (shiftState c j) (fun _ => True) (Bad j) := by
  intro t st _ hst Q
  rcases t with n | m | m
  · change Pr{let z ← (·, st) <$> _}[_] ≤ Pr{let z ← (·, shiftState c j st) <$> _}[_]
    rw [prEvent_map, prEvent_map]
    exact prEvent_mono _ _ _ fun _ h => h.1
  · change Pr{let z ← hash (F := F) (G₂ := G₂) g₂ m st}[Q (z.1, shiftState c j z.2) ∧ _] ≤
      Pr{let z ← embedHash (F := F) (G₂ := G₂) g₂ (c • g₂) j m (shiftState c j st)}[Q z]
    exact (prEvent_mono _ _ _ fun _ h => h.1).trans (prEvent_hash_shift g₂ c j m st Q).le
  · rw [impl_sign_run, embedImpl_sign_run, prEvent_map, prEvent_map]
    let Q' : G₂ × State F M → Prop := Q
    have hshift := prEvent_hash_shift g₂ c j m st fun z =>
      Q' (embedSignature (a • g₂) j m z.2, { z.2 with signed := z.2.signed ++ [m] })
    refine le_trans ?_ hshift.le
    refine prEvent_mono_of_support _ _ _ fun z hz ⟨hQ, hbad⟩ => ?_
    obtain ⟨⟨k, t, hk, hz1⟩, -⟩ := mem_support_hash (st := st) hz
    rw [embedSignature_shiftState_of_not_bad hk hbad, ← hz1]
    exact hQ

/-- The game's run on the public key `pk`, under the secret key `a`. -/
abbrev gameRun (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (pk : G₁) (a : F) :
    ProbComp ((M × G₂ × G₂) × State F M) :=
  (simulateQ (impl g₂ a) (run adversary pk)).run State.init

/-- The reduction's run on the public key `pk`, with its guess `j`. -/
abbrev embedRun (g₂ X₂ Y : G₂) (j : ℕ) (adversary : Adversary G₁ G₂ M) (pk : G₁) :
    ProbComp ((M × G₂ × G₂) × State F M) :=
  (simulateQ (embedImpl g₂ X₂ Y j) (run adversary pk)).run State.init

/-- The game's run, seen through the shift and before the bad event, is the reduction's run. -/
theorem prEvent_run_shift_le (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (pk : G₁) (a c : F)
    (j : ℕ) (P : (M × G₂ × G₂) × State F M → Prop) :
    Pr{let z ← gameRun g₂ adversary pk a}[P (z.1, shiftState c j z.2) ∧ ¬Bad j z.2] ≤
      Pr{let z ← embedRun g₂ (a • g₂) (c • g₂) j adversary pk}[P z] :=
  (dominatedUntilBad g₂ a c j).prEvent_simulateQ_run_map_and_not_bad_le
    (fun _ _ _ _ _ => trivial) (impl_preservesInv_bad g₂ a j) _ State.init trivial P

/-- At the end of the game, the hash of the forged message is in the table. -/
theorem mem_support_gameRun {g₂ : G₂} {a : F} {adversary : Adversary G₁ G₂ M} {pk : G₁}
    {z : (M × G₂ × G₂) × State F M} (hz : z ∈ support (gameRun g₂ adversary pk a)) :
    ∃ k t, lookup z.1.1 z.2.table = some (k, t) ∧ z.1.2.2 = t • g₂ := by
  simp only [gameRun, run, simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hz
  obtain ⟨⟨⟨m, σ⟩, st⟩, -, hz⟩ := hz
  simp only [simulateQ_pure] at hz
  obtain ⟨⟨h, st'⟩, hi, hz⟩ := hz
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  rw [simulateQ_HasQuery_query] at hi
  exact (mem_support_hash (G₂ := G₂) hi).1

/-- The reduction succeeds with the average, over its guess `j`, of the runs with that guess. -/
theorem prEvent_reduction (g₂ : G₂) (adversary : Adversary G₁ G₂ M) (n : ℕ) (X₁ : G₁)
    (X₂ Y T : G₂) :
    Pr{let g ← reduction (F := F) g₂ adversary (n + 1) X₁ X₂ Y}[g = T] =
      (∑ j : Fin (n + 1), Pr{let z ← embedRun (F := F) g₂ X₂ Y j adversary X₁}[
        extract X₂ j z.1.1 z.1.2.1 z.2 = T]) / (n + 1) := by
  let : MeasurableSpace (Fin (n + 1)) := ⊤
  unfold reduction
  rw [prEvent_bind_eq_lintegral_of_discrete, ProbComp.lintegral_evalDist_uniformFin]
  congr 2
  funext j
  let mx := embedRun (F := F) g₂ X₂ Y j adversary X₁
  change Pr{let g ← mx >>= fun x => pure (extract X₂ j x.1.1 x.1.2.1 x.2)}[g = T] = _
  rw [bind_pure_comp, prEvent_map]

variable [AddCommGroup G₁] [Module F G₁]

/-! ## The bound -/

/-- The adversary wins a run: the message was never signed, and the signature verifies. -/
def Wins (scheme : Scheme G₁ G₂) (a : F) (z : (M × G₂ × G₂) × State F M) : Prop :=
  z.1.1 ∉ z.2.signed ∧ scheme.isDh (a • scheme.g₁) z.1.2.2 z.1.2.1 = true

/-- A winning run whose forged message sits at position `j` gives the reduction its answer.

The reduction never had to sign at `j` in that run. -/
theorem extract_of_wins {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    {adversary : Adversary G₁ G₂ M} {a c : F} {j : ℕ} {z : (M × G₂ × G₂) × State F M}
    (hz : z ∈ support (gameRun scheme.g₂ adversary (a • scheme.g₁) a)) (hwin : Wins scheme a z)
    (hj : ∃ t, lookup z.1.1 z.2.table = some (j, t)) :
    extract (a • scheme.g₂) j z.1.1 z.1.2.1 (shiftState c j z.2) = (a * c) • scheme.g₂ ∧
      ¬Bad j z.2 := by
  obtain ⟨k, t, hk, hh⟩ := mem_support_gameRun hz
  obtain ⟨t', ht'⟩ := hj
  obtain ⟨rfl, rfl⟩ : k = j ∧ t = t' := by simpa [hk] using ht'
  have hσ : z.1.2.1 = a • (t • scheme.g₂) := hh ▸ (hsound a _ _).mp hwin.2
  refine ⟨?_, fun ⟨e, he, hs⟩ => hwin.1 ?_⟩
  · simp only [extract, shiftState, lookup_shift, hk, Option.map_some, ite_true, hσ, smul_smul,
      ← sub_smul]
    congr 1
    ring
  · obtain rfl : e = (z.1.1, t) := by simpa [getElem?_of_lookup hk] using he.symm
    exact hs

theorem forgeAdvantage_eq (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) :
    letI : MeasurableSpace F := ⊤
    forgeAdvantage F scheme adversary = ∫⁻ a,
      Pr{let z ← gameRun scheme.g₂ adversary (a • scheme.g₁) a}[Wins scheme a z] ∂𝒟[$ᵗ F] := by
  let : MeasurableSpace F := ⊤
  unfold forgeAdvantage experiment
  rw [prEvent_bind_eq_lintegral_of_discrete]
  refine lintegral_congr fun a => ?_
  let mx := gameRun scheme.g₂ adversary (a • scheme.g₁) a
  let check := fun x : (M × G₂ × G₂) × State F M =>
    (decide (x.1.1 ∉ x.2.signed) && scheme.isDh (a • scheme.g₁) x.1.2.2 x.1.2.1, x.2)
  change Pr{let z ← mx >>= fun x => pure (check x)}[z.1 = true] = _
  rw [bind_pure_comp, prEvent_map]
  exact prEvent_congr _ _ _ fun x => by simp [check, Wins]

/-- The forged message sits at position `j` of the table. -/
def At (j : ℕ) (z : (M × G₂ × G₂) × State F M) : Prop := ∃ t, lookup z.1.1 z.2.table = some (j, t)

/-- A winning run of the game is, for some guess `j`, a winning run at position `j`. -/
theorem prEvent_wins_le_sum (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) (a : F)
    {n : ℕ} (hlen : ∀ z ∈ support (gameRun scheme.g₂ adversary (a • scheme.g₁) a),
      z.2.table.length ≤ n + 1) :
    Pr{let z ← gameRun scheme.g₂ adversary (a • scheme.g₁) a}[Wins scheme a z] ≤
      ∑ j : Fin (n + 1),
        Pr{let z ← gameRun scheme.g₂ adversary (a • scheme.g₁) a}[At j z ∧ Wins scheme a z] := by
  refine le_trans (prEvent_mono_of_support _ _ (fun z => ∃ j ∈ Finset.univ,
    At (j : Fin (n + 1)) z ∧ Wins scheme a z) fun z hz hw => ?_) (prEvent_exists_finset_le _ _ _)
  obtain ⟨k, t, hk, -⟩ := mem_support_gameRun hz
  have hlt : k < z.2.table.length := (List.getElem?_eq_some_iff.mp (getElem?_of_lookup hk)).1
  exact ⟨⟨k, by have := hlen z hz; omega⟩, Finset.mem_univ _, ⟨t, hk⟩, hw⟩

/-- A winning run at position `j` is a success of the reduction with the guess `j`. -/
theorem prEvent_at_le_extract {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    (adversary : Adversary G₁ G₂ M) (a c : F) (j : ℕ) :
    Pr{let z ← gameRun scheme.g₂ adversary (a • scheme.g₁) a}[At j z ∧ Wins scheme a z] ≤
      Pr{let z ← embedRun (F := F) scheme.g₂ (a • scheme.g₂) (c • scheme.g₂) j adversary
                  (a • scheme.g₁)}[
        extract (a • scheme.g₂) j z.1.1 z.1.2.1 z.2 = (a * c) • scheme.g₂] :=
  (prEvent_mono_of_support _ _ _ fun _ hz ⟨hj, hw⟩ => extract_of_wins hsound hz hw hj).trans
    (prEvent_run_shift_le scheme.g₂ adversary _ a c j
      fun z => extract (a • scheme.g₂) j z.1.1 z.1.2.1 z.2 = (a * c) • scheme.g₂)

/-- **Unforgeability of BLS signatures from co-CDH**, in the random oracle model.

Let every run of the game make at most `q >= 1` hash calls.

Then the forger's advantage is at most `q` times the advantage of the reduction at co-CDH. -/
theorem forgeAdvantage_le [DecidableEq G₂] (scheme : Scheme G₁ G₂) (hsound : scheme.Sound F)
    (adversary : Adversary G₁ G₂ M) {q : ℕ} (hq0 : 0 < q)
    (hq : HashCallBound F scheme adversary q) :
    forgeAdvantage F scheme adversary ≤
      q * coCdhAdvantage F scheme.g₁ scheme.g₂ (reduction (F := F) scheme.g₂ adversary q) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  let : MeasurableSpace F := ⊤
  -- The table of every run has at most `n + 1` entries.
  have hlen : ∀ a : F, ∀ z ∈ support (gameRun scheme.g₂ adversary (a • scheme.g₁) a),
      z.2.table.length ≤ n + 1 := by
    intro a z hz
    refine (simulateQ_run_preservesInv _ _ (impl_preservesInv_length scheme.g₂ a) _
      State.init (le_refl 0) z hz).trans (hq (decide (z.1.1 ∉ z.2.signed) &&
        scheme.isDh (a • scheme.g₁) z.1.2.2 z.1.2.1, z.2) ?_)
    unfold experiment
    rw [mem_support_bind_iff]
    refine ⟨a, by simp, ?_⟩
    rw [mem_support_bind_iff]
    exact ⟨z, hz, by simp⟩
  -- For each key and each challenge, the forger's win is at most `n + 1` reduction successes.
  have key : ∀ a c : F,
      Pr{let z ← gameRun scheme.g₂ adversary (a • scheme.g₁) a}[Wins scheme a z] ≤
        (n + 1 : ℕ) * Pr{let g ← reduction (F := F) scheme.g₂ adversary (n + 1) (a • scheme.g₁)
                            (a • scheme.g₂) (c • scheme.g₂)}[g = (a * c) • scheme.g₂] := by
    intro a c
    rw [prEvent_reduction, Nat.cast_add, Nat.cast_one,
      ENNReal.mul_div_cancel (by positivity) (by simp)]
    exact (prEvent_wins_le_sum scheme adversary a (hlen a)).trans
      (Finset.sum_le_sum fun j _ => prEvent_at_le_extract hsound adversary a c j)
  rw [forgeAdvantage_eq, coCdhAdvantage, coCdhExperiment, prEvent_bind_eq_lintegral_of_discrete,
    ← lintegral_const_mul _ Measurable.of_discrete]
  refine lintegral_mono fun a => ?_
  rw [prEvent_bind_eq_lintegral_of_discrete, ← lintegral_const_mul _ Measurable.of_discrete]
  -- The forger's win does not depend on the challenge, so it is its own average over `c`.
  calc _ = ∫⁻ _ : F, Pr{let z ← gameRun scheme.g₂ adversary (a • scheme.g₁) a}[Wins scheme a z]
          ∂𝒟[$ᵗ F] := by
        rw [lintegral_const, ← prEvent_true_eq_evalDist_apply_univ, prEvent_true_eq_one, mul_one]
    _ ≤ _ := lintegral_mono fun c => (key a c).trans_eq (by rw [bind_pure_comp, prEvent_map]; simp)

end EthLib.Cryptography.Bls.Security
