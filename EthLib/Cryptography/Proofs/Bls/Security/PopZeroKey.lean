module

public import EthLib.Cryptography.Proofs.BadOnGrowth
public import EthLib.Cryptography.Proofs.Bls.Security.PopReduction

/-!
# Proofs: a key hash of the aggregate game is rarely zero

A key whose hash is 0 has the proof 0 for any secret, so its proof says nothing.

The reduction for aggregates needs every key other than the honest one to have a nonzero hash.

Each new key gets a fresh uniform scalar, which is 0 with probability `1 / |F|`.

The honest key is the first entry of the key table, and the key table has at most `qK` entries.

So some other key gets the scalar 0 with probability at most `(qK - 1) / |F|`.

The bound is the union bound over the new entries of a table, proved for any stateful oracle.
-/

@[expose] public section

namespace EthLib.Cryptography.Bls.Security.Pop

open OracleComp OracleSpec ENNReal

variable {F G₁ G₂ M : Type} [DecidableEq M] [DecidableEq G₁] [Field F] [SampleableType F]
  [AddCommGroup G₁] [Module F G₁] [AddCommGroup G₂] [Module F G₂]

/-- Some key other than `pk` hashes with the scalar 0. -/
def ZeroKey (pk : G₁) (st : State F G₁ M) : Prop := ∃ e ∈ st.keyTable, e.1 ≠ pk ∧ e.2 = 0

omit [DecidableEq M] [AddCommGroup G₁] [Module F G₁] in
/-- The hash of the honest key, from the empty state, draws its scalar `t` into the key table. -/
theorem keyHash_init (g₂ : G₂) (pk : G₁) :
    (keyHash (M := M) g₂ pk).run State.init =
      (fun t : F => (t • g₂, State.withKey pk t)) <$> ($ᵗ F) := by
  rfl

omit [AddCommGroup G₁] [Module F G₁] in
/-- A step keeps the key table and does not lower the key calls, or adds one entry and one call. -/
theorem keyTable_of_mem_support_impl {g₂ : G₂} {a : F} {t : (Spec M G₁ G₂).Domain}
    {st : State F G₁ M} {z : (Spec M G₁ G₂).Range t × State F G₁ M}
    (hz : z ∈ support ((impl g₂ a t).run st)) :
    (z.2.keyTable = st.keyTable ∧ st.keyCalls ≤ z.2.keyCalls) ∨
      (∃ e, z.2.keyTable = st.keyTable ++ [e] ∧ z.2.keyCalls = st.keyCalls + 1) := by
  rcases t with n | (m | m) | x
  · change z ∈ support ((·, st) <$> _) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact Or.inl ⟨rfl, le_rfl⟩
  · change z ∈ support ((fun w => _) <$> hash g₂ m st.msg) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨w, -, rfl⟩ := hz
    exact Or.inl ⟨rfl, le_rfl⟩
  · change z ∈ support ((fun w => _) <$> ((fun w => _) <$> hash g₂ m st.msg)) at hz
    simp only [support_map, Set.mem_image] at hz
    obtain ⟨_, ⟨w, -, rfl⟩, rfl⟩ := hz
    exact Or.inl ⟨rfl, le_rfl⟩
  · change z ∈ support (keyHash g₂ x st) at hz
    unfold keyHash at hz
    split at hz
    · simp only [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl ⟨rfl, Nat.le_succ _⟩
    · simp only [support_map, Set.mem_image] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact Or.inr ⟨(x, u), rfl, rfl⟩

omit [AddCommGroup G₁] [Module F G₁] in
/-- The key table never has more entries than there were key hash calls. -/
theorem impl_preservesInv_keyLength (g₂ : G₂) (a : F) :
    QueryImpl.PreservesInv (impl (M := M) (G₁ := G₁) g₂ a)
      fun st => st.keyTable.length ≤ st.keyCalls := by
  intro t st hst z hz
  rcases keyTable_of_mem_support_impl hz with ⟨h₁, h₂⟩ | ⟨e, h₁, h₂⟩
  · rw [h₁]; omega
  · rw [h₁, List.length_append, h₂]; simp; omega

omit [AddCommGroup G₁] [Module F G₁] in
/-- Only a new key changes the key table, and its scalar is 0 with probability `1 / |F|`. -/
theorem badOnGrowth_impl (g₂ : G₂) (a : F) (pk : G₁) :
    BadOnGrowth (impl (M := M) g₂ a) (fun st => st.keyTable.length) (ZeroKey pk)
      (Nat.card F : ℝ≥0∞)⁻¹ := by
  refine ⟨fun t s z hz => ?_, fun t s hs => ?_⟩
  · rcases keyTable_of_mem_support_impl hz with ⟨h₁, -⟩ | ⟨e, h₁, -⟩
    · rw [h₁]
    · simp [h₁]
  · have keep : (∀ z ∈ support ((impl (M := M) g₂ a t).run s), z.2.keyTable = s.keyTable) →
        ∀ z ∈ support ((impl (M := M) g₂ a t).run s),
          z.2.keyTable.length = s.keyTable.length ∧ ¬ZeroKey pk z.2 := fun h z hz =>
      ⟨by rw [h z hz], by unfold ZeroKey; rw [h z hz]; exact hs⟩
    rcases t with n | (m | m) | x
    · refine Or.inl (keep fun z hz => ?_)
      change z ∈ support ((·, s) <$> _) at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, -, rfl⟩ := hz
      rfl
    · refine Or.inl (keep fun z hz => ?_)
      change z ∈ support ((fun w => _) <$> hash g₂ m s.msg) at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨w, -, rfl⟩ := hz
      rfl
    · refine Or.inl (keep fun z hz => ?_)
      change z ∈ support ((fun w => _) <$> ((fun w => _) <$> hash g₂ m s.msg)) at hz
      simp only [support_map, Set.mem_image] at hz
      obtain ⟨_, ⟨w, -, rfl⟩, rfl⟩ := hz
      rfl
    · cases hl : lookup x s.keyTable with
      | some p =>
        refine Or.inl (keep fun z hz => ?_)
        change z ∈ support (keyHash g₂ x s) at hz
        unfold keyHash at hz
        rw [hl] at hz
        simp only [support_pure, Set.mem_singleton_iff] at hz
        subst hz
        rfl
      | none =>
        right
        have he : (impl (M := M) g₂ a (.inr (.inr x))).run s = (fun u : F => (u • g₂,
            { s with keyTable := s.keyTable ++ [(x, u)], keyCalls := s.keyCalls + 1 })) <$>
              ($ᵗ F) := by
          change keyHash g₂ x s = _
          unfold keyHash
          rw [hl]
        rw [he]
        refine ⟨fun z hz => ?_, ?_⟩
        · simp only [support_map, Set.mem_image] at hz
          obtain ⟨_, -, rfl⟩ := hz
          simp
        · rw [prEvent_map]
          refine (prEvent_mono _ _ (· = 0) fun u hu => ?_).trans
            (SampleableType.prEvent_uniformSample_eq_singleton_natCard 0).le
          obtain ⟨e, he, hne, he0⟩ := hu
          rcases List.mem_append.1 he with he | he
          · exact (hs ⟨e, he, hne, he0⟩).elim
          · rw [List.mem_singleton.1 he] at he0
            exact he0

/-- **A key hash other than the honest one is zero with probability at most `(qK - 1) / |F|`.**

This holds for the run after the honest key hash, for every secret `a` and honest scalar `t`. -/
theorem prEvent_zeroKey_le (scheme : Scheme G₁ G₂) (adversary : Adversary G₁ G₂ M) {q qK : ℕ}
    (hq : HashCallBound F scheme adversary q qK) (a t : F) :
    Pr{let w ← (simulateQ (impl scheme.g₂ a)
        (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
          (State.withKey (a • scheme.g₁) t)}[ZeroKey (a • scheme.g₁) w.2] ≤
      ((qK - 1 : ℕ) : ℝ≥0∞) * (Nat.card F : ℝ≥0∞)⁻¹ := by
  have hsz : ∀ z ∈ support ((simulateQ (impl scheme.g₂ a)
      (run adversary (a • scheme.g₁) (a • (t • scheme.g₂)))).run
        (State.withKey (a • scheme.g₁) t)), z.2.keyTable.length ≤ qK := by
    intro z hz
    refine (simulateQ_run_preservesInv _ _ (impl_preservesInv_keyLength scheme.g₂ a) _ _
      (by simp [State.withKey]) z hz).trans
      (hq (wins scheme (a • scheme.g₁) z.2.msg.signed z.1, z.2) ?_).2
    unfold experiment
    rw [mem_support_bind_iff]
    refine ⟨a, by simp, ?_⟩
    rw [mem_support_bind_iff]
    refine ⟨z, ?_, by simp⟩
    rw [StateT.run_bind, keyHash_init, bind_map_left, mem_support_bind_iff]
    exact ⟨t, by simp, hz⟩
  have h := (badOnGrowth_impl (M := M) scheme.g₂ a (a • scheme.g₁)).prEvent_bad_le _
    (State.withKey (a • scheme.g₁) t) (fun ⟨e, he, hne, _⟩ => hne (by
      simp only [State.withKey, List.mem_singleton] at he
      rw [he])) hsz
  simpa [State.withKey] using h

end EthLib.Cryptography.Bls.Security.Pop
