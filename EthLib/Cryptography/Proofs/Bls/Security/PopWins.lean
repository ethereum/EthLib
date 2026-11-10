module

public import EthLib.Cryptography.Proofs.Bls.Security.PopZeroKey
public import EthLib.Cryptography.Proofs.Bls.Security.PopReduction

/-!
# Proofs: a winning aggregate forgery gives the reduction its answer

The game here draws the scalar `z` of the message hash at position `j` first.

Take a run that wins with its forged message at position `j`.

The message hash is then `z • g2`, and each key hash is its table scalar times `g2`.

Through the projection, every key other than the honest one has the scalar `t * z⁻¹`.

Its hash `t • g2` is then that scalar times `z • g2`, as the extraction step needs.

So the reduction's answer is `(a * z) • g2`, when the following hold.

- Every element of `G1` is a multiple of `g1`.
- `z ≠ 0`, and no key other than the honest one hashes with the scalar 0.
- The number of copies of the honest key is not zero in the scalars.

A winning run never signed its message, so it is before the bad event of the coupling.

So a winning run at `j` is at most as likely as a success of the reduction with the guess `j`.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

open OracleComp OracleSpec ENNReal

variable {F G₁ G₂ M : Type} [DecidableEq M] [DecidableEq G₁] [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- The output of a run: the adversary's keys, message and aggregate, then the hashes. -/
abbrev Output (G₁ G₂ M : Type) := (List (G₁ × G₂) × M × G₂) × G₂ × List G₂

/-- The forged message sits at position `j` of the message table. -/
def At (j : ℕ) (p : Output G₁ G₂ M × State F G₁ M) : Prop :=
  ∃ s, lookup p.1.1.2.1 p.2.msg.table = some (j, s)

/-- The number of copies of the key `pk` among the adversary's keys. -/
def honestCount (pk : G₁) (p : Output G₁ G₂ M × State F G₁ M) : ℕ :=
  (p.1.1.1.map Prod.fst).count pk

omit [DecidableEq M] [SampleableType F] [AddCommGroup G₁] [Module F G₁] in
/-- The projection divides the scalar of every key other than `pk` by `z`. -/
theorem keyScalar_projectState (pk x : G₁) (j : ℕ) (z : F) (st : State F G₁ M) :
    keyScalar x (projectState pk j z st) =
      if x = pk then keyScalar x st else keyScalar x st * z⁻¹ := by
  simp only [keyScalar, projectState, lookup_scaleKeys]
  cases lookup x st.keyTable with
  | none => simp
  | some p => by_cases hx : x = pk <;> simp [hx]

omit [Field F] [SampleableType F] [AddCommGroup G₁] [Module F G₁] in
/-- An entry that a lookup finds is still found after more entries are appended. -/
theorem lookup_append_of_some {x : G₁} {v : ℕ × F} :
    ∀ {l : List (G₁ × F)} (r : List (G₁ × F)), lookup x l = some v → lookup x (l ++ r) = some v
  | [], _, h => by simp [lookup] at h
  | (y, t) :: rest, r, h => by
    simp only [List.cons_append, lookup] at h ⊢
    split_ifs at h ⊢ with hy
    · exact h
    · obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [lookup_append_of_some r hw]
      rfl

omit [DecidableEq M] [AddCommGroup G₁] [Module F G₁] in
/-- One key hash call answers the scalar of its key times `g2`, and only appends to the key table.

It keeps the message part of the state, and adds one key hash call. -/
theorem mem_support_keyHash {g₂ : G₂} {x : G₁} {st : State F G₁ M} {w : G₂ × State F G₁ M}
    (hw : w ∈ support (keyHash g₂ x st)) :
    w.1 = keyScalar x w.2 • g₂ ∧ (∃ i s, lookup x w.2.keyTable = some (i, s)) ∧
      (∃ r, w.2.keyTable = st.keyTable ++ r) ∧ w.2.msg = st.msg ∧
        w.2.keyCalls = st.keyCalls + 1 := by
  unfold keyHash at hw
  split at hw
  · next i s h =>
    simp only [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    exact ⟨by simp [keyScalar, h], ⟨i, s, h⟩, ⟨[], by simp⟩, rfl, rfl⟩
  · next h =>
    simp only [support_map, Set.mem_image] at hw
    obtain ⟨s, -, rfl⟩ := hw
    have hl := lookup_append_of_none h s
    exact ⟨by simp [keyScalar, hl], ⟨_, s, hl⟩, ⟨_, rfl⟩, rfl, rfl⟩

/-- A message hash call with the scalar `z` fixed at `j` keeps the scalar `z` at position `j`. -/
theorem scalarAt_of_mem_support_hashAt {g₂ : G₂} {j : ℕ} {z : F} {m : M}
    {st : Security.State F M} {w : G₂ × Security.State F M}
    (hw : w ∈ support (hashAt g₂ j z m st)) (hst : ∀ e, st.table[j]? = some e → e.2 = z) :
    ∀ e, w.2.table[j]? = some e → e.2 = z := by
  intro e he
  by_cases hnew : lookup m st.table = none ∧ st.table.length = j
  · rw [hashAt_of_new hnew.1 hnew.2] at hw
    simp only [support_pure, Set.mem_singleton_iff] at hw
    subst hw
    simp [← hnew.2] at he
    rw [← he]
  · rw [hashAt_eq_hash fun hl hj => hnew ⟨hl, hj⟩] at hw
    unfold hash at hw
    split at hw
    · simp only [support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact hst e he
    · next hl =>
      simp only [support_map, Set.mem_image] at hw
      obtain ⟨t, -, rfl⟩ := hw
      have hj : st.table.length ≠ j := fun hj => hnew ⟨hl, hj⟩
      rcases lt_or_gt_of_ne hj with h | h
      · simp [List.getElem?_append_right h.le] at he
        rw [List.getElem?_eq_none (by simp; omega)] at he
        simp at he
      · rw [List.getElem?_append_left h] at he
        exact hst e he

omit [AddCommGroup G₁] [Module F G₁] in
/-- With the message scalar at `j` fixed to `z`, the message table entry at `j` has scalar `z`. -/
theorem implAt_preservesInv_scalarAt (g₂ : G₂) (a : F) (j : ℕ) (z : F) :
    QueryImpl.PreservesInv (implAt (M := M) (G₁ := G₁) g₂ a j z)
      fun st => ∀ e, st.msg.table[j]? = some e → e.2 = z := by
  intro t st hst x hx
  rcases t with n | (m | m) | y
  · change x ∈ support ((·, st) <$> _) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨_, -, rfl⟩ := hx
    exact hst
  · change x ∈ support ((fun w => _) <$> hashAt g₂ j z m st.msg) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact scalarAt_of_mem_support_hashAt hw hst
  · change x ∈ support ((fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg)) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
    exact scalarAt_of_mem_support_hashAt hw hst
  · change x ∈ support (keyHash g₂ y st) at hx
    rw [(mem_support_keyHash hx).2.2.2.1]
    exact hst

omit [AddCommGroup G₁] [Module F G₁] in
/-- A step of the oracles never lowers the number of key hash calls. -/
theorem implAt_preservesInv_keyCalls (g₂ : G₂) (a : F) (j : ℕ) (z : F) (c : ℕ) :
    QueryImpl.PreservesInv (implAt (M := M) (G₁ := G₁) g₂ a j z) fun st => c ≤ st.keyCalls := by
  intro t st hst x hx
  rcases t with n | (m | m) | y
  · change x ∈ support ((·, st) <$> _) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨_, -, rfl⟩ := hx
    exact hst
  · change x ∈ support ((fun w => _) <$> hashAt g₂ j z m st.msg) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨w, -, rfl⟩ := hx
    exact hst
  · change x ∈ support ((fun w => _) <$> ((fun w => _) <$> hashAt g₂ j z m st.msg)) at hx
    simp only [support_map, Set.mem_image] at hx
    obtain ⟨_, ⟨w, -, rfl⟩, rfl⟩ := hx
    exact hst
  · change x ∈ support (keyHash g₂ y st) at hx
    rw [(mem_support_keyHash hx).2.2.2.2]
    omega

omit [AddCommGroup G₁] [Module F G₁] in
/-- The key hash calls of verification answer the table scalar of each key times `g2`.

They keep the message part of the state, and make one key hash call per key. -/
theorem mem_support_mapM_keyHash {g₂ : G₂} {a : F} {j : ℕ} {z : F} :
    ∀ (l : List (G₁ × G₂)) (st : State F G₁ M) (p : List G₂ × State F G₁ M),
      p ∈ support ((simulateQ (implAt g₂ a j z)
        (l.mapM fun k => query (spec := Spec M G₁ G₂) (.inr (.inr k.1)))).run st) →
      p.1 = l.map (fun k => keyScalar k.1 p.2 • g₂) ∧
        (∀ k ∈ l, ∃ i s, lookup k.1 p.2.keyTable = some (i, s)) ∧
        (∃ r, p.2.keyTable = st.keyTable ++ r) ∧ p.2.msg = st.msg ∧
        p.2.keyCalls = st.keyCalls + l.length
  | [], st, p, hp => by
    simp at hp
    subst hp
    simp
  | k :: rest, st, p, hp => by
    rw [List.mapM_cons] at hp
    simp only [simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hp
    obtain ⟨w, hw, v, hv, hp⟩ := hp
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
    subst hp
    rw [simulateQ_HasQuery_query] at hw
    change w ∈ support (keyHash g₂ k.1 st) at hw
    obtain ⟨hw1, ⟨i, s, hl⟩, ⟨r, hr⟩, hmsg, hcalls⟩ := mem_support_keyHash hw
    obtain ⟨hv1, hvl, ⟨r', hr'⟩, hvmsg, hvcalls⟩ := mem_support_mapM_keyHash rest w.2 v hv
    have hl' : lookup k.1 v.2.keyTable = some (i, s) := by
      rw [hr']
      exact lookup_append_of_some r' hl
    refine ⟨?_, fun k' hk' => ?_, ⟨r ++ r', by rw [hr', hr, List.append_assoc]⟩,
      hvmsg.trans hmsg, by rw [hvcalls, hcalls, List.length_cons]; omega⟩
    · rw [List.map_cons, ← hv1, hw1]
      simp [keyScalar, hl, hl']
    · rcases List.mem_cons.1 hk' with rfl | hk'
      · exact ⟨i, s, hl'⟩
      · exact hvl k' hk'

omit [AddCommGroup G₁] [Module F G₁] in
/-- A run is the adversary's run, then the message hash call, then one key hash call per key.

The adversary's run never lowers the number of key hash calls. -/
theorem mem_support_run_implAt {g₂ : G₂} {a : F} {j : ℕ} {z : F}
    {adversary : Adversary G₁ G₂ M} {pk : G₁} {proof : G₂} {st₀ : State F G₁ M}
    {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (implAt g₂ a j z) (run adversary pk proof)).run st₀)) :
    ∃ st₁ : State F G₁ M, st₀.keyCalls ≤ st₁.keyCalls ∧
      ∃ w ∈ support (hashAt g₂ j z p.1.1.2.1 st₁.msg), p.1.2.1 = w.1 ∧
        (p.1.2.2, p.2) ∈ support ((simulateQ (implAt g₂ a j z)
          (p.1.1.1.mapM fun k => query (spec := Spec M G₁ G₂) (.inr (.inr k.1)))).run
            { st₁ with msg := w.2 }) := by
  simp only [run, simulateQ_bind, StateT.run_bind, support_bind, Set.mem_iUnion] at hp
  obtain ⟨o, ho, w, hw, v, hv, hp⟩ := hp
  simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hp
  subst hp
  rw [simulateQ_HasQuery_query] at hw
  change w ∈ support ((fun x => (x.1, { o.2 with msg := x.2 })) <$>
    hashAt g₂ j z o.1.2.1 o.2.msg) at hw
  simp only [support_map, Set.mem_image] at hw
  obtain ⟨w', hw', rfl⟩ := hw
  exact ⟨o.2, simulateQ_run_preservesInv _ _ (implAt_preservesInv_keyCalls g₂ a j z st₀.keyCalls)
    _ _ le_rfl o ho, w', hw', rfl, hv⟩

omit [AddCommGroup G₁] [Module F G₁] in
/-- At the end of a run, the message hash is its table scalar times `g2`. -/
theorem msgHash_of_mem_support {g₂ : G₂} {a : F} {j : ℕ} {z : F}
    {adversary : Adversary G₁ G₂ M} {pk : G₁} {proof : G₂} {st₀ : State F G₁ M}
    {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (implAt g₂ a j z) (run adversary pk proof)).run st₀)) :
    ∃ k s, lookup p.1.1.2.1 p.2.msg.table = some (k, s) ∧ p.1.2.1 = s • g₂ := by
  obtain ⟨st₁, -, w, hw, hh, hv⟩ := mem_support_run_implAt hp
  obtain ⟨⟨k, s, hk, hw1⟩, -⟩ := mem_support_hashAt hw
  obtain ⟨-, -, -, hmsg, -⟩ := mem_support_mapM_keyHash _ _ _ hv
  have hmsg' : p.2.msg = w.2 := hmsg
  exact ⟨k, s, hmsg' ▸ hk, hh.trans hw1⟩

omit [AddCommGroup G₁] [Module F G₁] in
/-- At the end of a run, each key hash of the verification is its table scalar times `g2`. -/
theorem keyHashes_of_mem_support {g₂ : G₂} {a : F} {j : ℕ} {z : F}
    {adversary : Adversary G₁ G₂ M} {pk : G₁} {proof : G₂} {st₀ : State F G₁ M}
    {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (implAt g₂ a j z) (run adversary pk proof)).run st₀)) :
    p.1.2.2 = p.1.1.1.map (fun k => keyScalar k.1 p.2 • g₂) ∧
      ∀ k ∈ p.1.1.1, ∃ i s, lookup k.1 p.2.keyTable = some (i, s) := by
  obtain ⟨st₁, -, w, -, -, hv⟩ := mem_support_run_implAt hp
  obtain ⟨h₁, h₂, -⟩ := mem_support_mapM_keyHash _ _ _ hv
  exact ⟨h₁, h₂⟩

omit [AddCommGroup G₁] [Module F G₁] in
/-- The verification makes one key hash call per key. -/
theorem keyCalls_of_mem_support {g₂ : G₂} {a : F} {j : ℕ} {z : F}
    {adversary : Adversary G₁ G₂ M} {pk : G₁} {proof : G₂} {st₀ : State F G₁ M}
    {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (implAt g₂ a j z) (run adversary pk proof)).run st₀)) :
    st₀.keyCalls + p.1.1.1.length ≤ p.2.keyCalls := by
  obtain ⟨st₁, h₁, w, -, -, hv⟩ := mem_support_run_implAt hp
  obtain ⟨-, -, -, -, h₂⟩ := mem_support_mapM_keyHash _ _ _ hv
  have h₃ : p.2.keyCalls = st₁.keyCalls + p.1.1.1.length := h₂
  omega

/-- A winning run whose forged message sits at position `j` gives the reduction `(a * z) • g2`.

Every element of `G1` is a multiple of `g1`, and `z ≠ 0`.

No key other than the honest one hashes with the scalar 0.

The number of copies of the honest key is not zero in the scalars.

The run never signed the message at `j`, so it is before the bad event. -/
theorem extract_of_wins {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    (hgen : ∀ x : G₁, ∃ sk : F, x = sk • scheme.g₁) {adversary : Adversary G₁ G₂ M}
    {a z t : F} (hz : z ≠ 0) {j : ℕ} {p : Output G₁ G₂ M × State F G₁ M}
    (hp : p ∈ support ((simulateQ (implAt scheme.g₂ a j z)
      (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
        (State.withKey (a • scheme.g₁) t)))
    (hwin : wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true) (hj : At j p)
    (hzero : ¬ZeroKey (a • scheme.g₁) p.2)
    (hcount : (honestCount (a • scheme.g₁) p : F) ≠ 0) :
    extract (a • scheme.g₁) j p.1 (projectState (a • scheme.g₁) j z p.2) =
        (a * z) • scheme.g₂ ∧ ¬Bad j p.2.msg := by
  obtain ⟨k, s, hk, hh⟩ := msgHash_of_mem_support hp
  obtain ⟨s', hj'⟩ := hj
  rw [hk] at hj'
  obtain ⟨rfl, rfl⟩ : k = j ∧ s = s' := by simpa using hj'
  have hentry : p.2.msg.table[k]? = some (p.1.1.2.1, s) := getElem?_of_lookup hk
  have hsz : s = z := simulateQ_run_preservesInv _ _
    (implAt_preservesInv_scalarAt scheme.g₂ a k z) _ _
    (by simp [State.withKey, Security.State.init]) p hp _ hentry
  subst hsz
  obtain ⟨hhs, hlk⟩ := keyHashes_of_mem_support hp
  simp only [wins, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwin
  obtain ⟨⟨⟨⟨-, hm⟩, -⟩, hproofs⟩, hagg⟩ := hwin
  refine ⟨?_, fun ⟨e, he, hs⟩ => hm ?_⟩
  · have hext : extract (a • scheme.g₁) k p.1 (projectState (a • scheme.g₁) k s p.2) =
        extractAggregate (a • scheme.g₁)
          (fun x => keyScalar x (projectState (a • scheme.g₁) k s p.2)) p.1.1.1 p.1.1.2.2 := by
      simp [extract, projectState, shiftState, lookup_shift, hk]
    rw [hext, extractAggregate_eq hsound (Z := s • scheme.g₂) (fun x _ => hgen x.1) ?_ hcount
      (hh ▸ hagg), smul_smul]
    intro x hx hne
    obtain ⟨i, u, hu⟩ := hlk x hx
    have hu0 : keyScalar x.1 p.2 ≠ 0 := by
      rw [keyScalar, hu]
      rintro rfl
      exact hzero ⟨(x.1, 0), List.mem_of_getElem? (getElem?_of_lookup hu), hne, rfl⟩
    rw [keyScalar_projectState]
    simp only [hne, ↓reduceIte]
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hz, mul_one]
    refine ⟨mul_ne_zero hu0 (inv_ne_zero hz), hproofs (x, keyScalar x.1 p.2 • scheme.g₂) ?_⟩
    rw [hhs, ← List.map_prod_left_eq_zip]
    exact List.mem_map_of_mem hx
  · rw [hentry] at he
    cases he
    exact hs

/-- **A winning run at `j` is a success of the reduction with the guess `j`.**

The game draws the message scalar `z ≠ 0` at `j`, and the honest key scalar `t`.

The reduction gets `X2 = a • g2` and the challenge `Y = z • g2`, and uses `t` for the honest key.

The event also asks that no other key hashes to 0, and that the honest count is not zero. -/
theorem prEvent_wins_le_extract {scheme : Scheme G₁ G₂} (hsound : scheme.Sound F)
    (hgen : ∀ x : G₁, ∃ sk : F, x = sk • scheme.g₁) (adversary : Adversary G₁ G₂ M)
    (a t : F) {z : F} (hz : z ≠ 0) (j : ℕ) :
    Pr{let p ← (simulateQ (implAt scheme.g₂ a j z)
        (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
          (State.withKey (a • scheme.g₁) t)}[
        At j p ∧ wins scheme (a • scheme.g₁) p.2.msg.signed p.1 = true ∧
          ¬ZeroKey (a • scheme.g₁) p.2 ∧ (honestCount (a • scheme.g₁) p : F) ≠ 0] ≤
      Pr{let p ← (simulateQ (embedImpl scheme.g₂ (a • scheme.g₂) (z • scheme.g₂)
          (a • scheme.g₁) j) (run adversary (a • scheme.g₁) (t • (a • scheme.g₂)))).run
            (State.withKey (a • scheme.g₁) t)}[
        extract (a • scheme.g₁) j p.1 p.2 = (a * z) • scheme.g₂] := by
  conv_rhs => rw [smul_comm t a, ← projectState_withKey (a • scheme.g₁) j z t]
  exact (prEvent_mono_of_support _ _ _ fun p hp ⟨hj, hw, hzk, hc⟩ =>
    extract_of_wins hsound hgen hz hp hw hj hzk hc).trans
      (prEvent_run_projectState_le scheme.g₂ adversary _ a hz j _ _
        fun p => extract (a • scheme.g₁) j p.1 p.2 = (a * z) • scheme.g₂)

end EthLib.Cryptography.Bls.Security.Pop
