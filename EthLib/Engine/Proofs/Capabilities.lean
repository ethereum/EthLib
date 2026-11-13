module

public import EthLib.Engine.Capabilities
public import EthLib.Engine.Proofs.Json

/-!
# Proofs: `engine_exchangeCapabilities` and `engine_getClientVersionV1`

A full method name gives back its method and its version, since a version has no letter `V`.

Every name that EthLib lists has a version, and no name appears twice.

So the list does not hold `engine_exchangeCapabilities`, which has no version.

The list holds a method at a version exactly when EthLib defines that method up to that version.

The version table reads a name back to the version it was built from.

The parameters of each method read back from their JSON.

Each method succeeds exactly when its request decodes, and then answers what the node holds.

A version object reads back from its JSON when its code is two letters, and only then.
-/

public section

namespace EthLib.Engine

open EthLib.Base
open EthLib.Serialization.JsonRpc

/-! ## Method names -/

/-- A list cut at an element that occurs in neither tail is cut in one way only. -/
private theorem append_cons_inj {α : Type} {c : α} :
    ∀ {l₁ l₂ r₁ r₂ : List α}, l₁ ++ c :: r₁ = l₂ ++ c :: r₂ → c ∉ r₁ → c ∉ r₂ →
      l₁ = l₂ ∧ r₁ = r₂
  | [], [], _, _, h, _, _ => by simpa using h
  | [], b :: l₂, r₁, r₂, h, h₁, _ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.2 ▸ List.mem_append_right _ List.mem_cons_self) h₁
  | a :: l₁, [], r₁, r₂, h, _, h₂ => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.2.symm ▸ List.mem_append_right _ List.mem_cons_self) h₂
  | a :: l₁, b :: l₂, r₁, r₂, h, h₁, h₂ => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hl, hr⟩ := append_cons_inj h.2 h₁ h₂
    exact ⟨by rw [h.1, hl], hr⟩

/-- The decimal digits of a number hold no letter `V`. -/
private theorem V_not_mem_toDigits (n : Nat) : 'V' ∉ Nat.toDigits 10 n := fun h =>
  absurd (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h) (by decide)

/-- The characters of a full method name. -/
private theorem toList_versionedMethod (method : String) (version : Nat) :
    (versionedMethod method version).toList =
      ("engine_".toList ++ method.toList) ++ 'V' :: Nat.toDigits 10 version := by
  simp [versionedMethod, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]

/-- Reading a list up to the first element that fails a test. -/
private theorem span_loop_append {α : Type} {p : α → Bool} {c : α} {r : List α}
    (hc : p c = false) : ∀ (l acc : List α), (∀ a ∈ l, p a = true) →
      List.span.loop p (l ++ c :: r) acc = (acc.reverse ++ l, c :: r)
  | [], acc, _ => by simp [List.span.loop, hc]
  | a :: l, acc, h => by
    simp only [List.cons_append, List.span.loop, h a List.mem_cons_self]
    rw [span_loop_append hc l (a :: acc) fun b hb => h b (List.mem_cons_of_mem _ hb)]
    simp

/-- The first decimal digit of a positive number is not zero. -/
private theorem head?_toDigits (n : Nat) (h : 0 < n) :
    (Nat.toDigits 10 n).head?.any (· ≠ '0') = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp
      omega
    · have ih' := ih (n / 10) (by omega) (by omega)
      cases hd : Nat.toDigits 10 (n / 10) with
      | nil => exact absurd hd Nat.toDigits_ne_nil
      | cons x l => simpa [hd] using ih'

/-- Two full method names are equal exactly when their methods and their versions are. -/
theorem versionedMethod_inj {method method' : String} {version version' : Nat} :
    versionedMethod method version = versionedMethod method' version' ↔
      method = method' ∧ version = version' := by
  constructor
  · intro h
    have h' := congrArg String.toList h
    rw [toList_versionedMethod, toList_versionedMethod] at h'
    obtain ⟨hl, hr⟩ := append_cons_inj h' (V_not_mem_toDigits _) (V_not_mem_toDigits _)
    refine ⟨String.toList_inj.mp (List.append_cancel_left hl), ?_⟩
    have := congrArg (Nat.ofDigitChars 10 · 0) hr
    simpa [Nat.ofDigitChars_ten_toDigits] using this
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A method of letters at a positive version has a full name of the expected form. -/
theorem isVersionedMethod_versionedMethod {method : String} {version : Nat}
    (hne : method ≠ "") (letters : method.toList.all Char.isAlpha = true) (pos : 0 < version) :
    IsVersionedMethod (versionedMethod method version) := by
  have hl : (versionedMethod method version).toList = 'e' :: 'n' :: 'g' :: 'i' :: 'n' :: 'e' ::
      '_' :: (method.toList ++ 'V' :: Nat.toDigits 10 version) := by
    rw [toList_versionedMethod]
    simp
  have hs : (method.toList ++ 'V' :: Nat.toDigits 10 version).reverse.span Char.isDigit =
      ((Nat.toDigits 10 version).reverse, 'V' :: method.toList.reverse) := by
    have hr : (method.toList ++ 'V' :: Nat.toDigits 10 version).reverse =
        (Nat.toDigits 10 version).reverse ++ 'V' :: method.toList.reverse := by
      simp
    rw [hr]
    unfold List.span
    rw [span_loop_append (by decide) _ _ fun a ha =>
      Nat.isDigit_of_mem_toDigits (by decide) (by decide) (List.mem_reverse.mp ha)]
    simp
  unfold IsVersionedMethod isVersionedMethod
  rw [hl]
  have hm : method.toList ≠ [] := by simpa [String.toList_eq_nil_iff] using hne
  simp only [hs, List.getLast?_reverse, List.all_reverse, letters, head?_toDigits version pos]
  simp [hm]

/-- Every name that EthLib lists has a version, and no name appears twice. -/
theorem isVersionedMethod_specifiedMethods :
    (∀ name ∈ specifiedMethods, IsVersionedMethod name) ∧ specifiedMethods.Nodup := by
  refine ⟨?_, ?_⟩
  · intro name h
    simp only [specifiedMethods, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨⟨method, last⟩, hm, i, -, rfl⟩ := h
    have key : ∀ p ∈ methodVersions, p.1 ≠ "" ∧ p.1.toList.all Char.isAlpha = true := by
      decide
    exact isVersionedMethod_versionedMethod (key _ hm).1 (key _ hm).2 (Nat.succ_pos i)
  · have hd : methodVersions.Pairwise fun a b => a.1 ≠ b.1 := by decide
    unfold specifiedMethods
    rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
    refine ⟨fun ⟨method, last⟩ _ => ?_, hd.imp fun {a b} hab => ?_⟩
    · simp only [List.pairwise_map]
      exact (List.nodup_iff_pairwise_ne.mp List.nodup_range).imp fun hij h =>
        hij (by have := (versionedMethod_inj.mp h).2; omega)
    · obtain ⟨a₁, a₂⟩ := a
      obtain ⟨b₁, b₂⟩ := b
      simp only [List.mem_map]
      rintro _ ⟨i, -, rfl⟩ _ ⟨j, -, rfl⟩ h
      exact hab (versionedMethod_inj.mp h).1

/-- The name of the method, which has no version, is not of the versioned form. -/
theorem not_isVersionedMethod_exchangeCapabilities :
    ¬ IsVersionedMethod "engine_exchangeCapabilities" := by
  decide

/-- The list does not hold `engine_exchangeCapabilities`, as step 3 of the method requires. -/
theorem exchangeCapabilities_not_mem_specifiedMethods :
    "engine_exchangeCapabilities" ∉ specifiedMethods := by
  intro h
  exact not_isVersionedMethod_exchangeCapabilities
    (isVersionedMethod_specifiedMethods.1 "engine_exchangeCapabilities" h)

/-- No two entries of the table name the same method. -/
private theorem methodVersions_pairwise : methodVersions.Pairwise fun a b => a.1 ≠ b.1 := by
  decide

/-- In a list of distinct keys, a key looks up a value exactly when the pair is in the list. -/
private theorem lookup_eq_some_iff {k : String} {x : Nat} :
    ∀ {l : List (String × Nat)}, l.Pairwise (fun a b => a.1 ≠ b.1) →
      (l.lookup k = some x ↔ (k, x) ∈ l)
  | [], _ => by simp
  | (a, b) :: t, h => by
    rw [List.pairwise_cons] at h
    by_cases hk : k = a
    · subst hk
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq, List.mem_cons,
        Prod.mk.injEq, true_and]
      constructor
      · rintro rfl
        exact Or.inl rfl
      · rintro (rfl | hm)
        · rfl
        · exact absurd rfl (h.1 (k, x) hm)
    · have hb : (k == a) = false := by simpa using hk
      simp [List.lookup_cons, hb, hk, lookup_eq_some_iff h.2]

/-- The list holds a method at a version exactly when EthLib defines it up to that version. -/
theorem mem_specifiedMethods {method : String} {version : Nat} :
    versionedMethod method version ∈ specifiedMethods ↔
      ∃ last, methodVersions.lookup method = some last ∧ 1 ≤ version ∧ version ≤ last := by
  simp only [specifiedMethods, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨⟨m, last⟩, hm, i, hi, h⟩
    obtain ⟨rfl, rfl⟩ := versionedMethod_inj.mp h
    exact ⟨last, (lookup_eq_some_iff methodVersions_pairwise).mpr hm, by omega, by omega⟩
  · rintro ⟨last, hl, h1, h2⟩
    refine ⟨(method, last), (lookup_eq_some_iff methodVersions_pairwise).mp hl, version - 1,
      by omega, ?_⟩
    exact versionedMethod_inj.mpr ⟨rfl, by omega⟩

/-- The table reads a full name back to its version, and only a name in the list. -/
theorem methodVersion_eq_some_iff {method name : String} {version : Nat} :
    methodVersion method name = some version ↔
      name = versionedMethod method version ∧
        ∃ last, methodVersions.lookup method = some last ∧ 1 ≤ version ∧ version ≤ last := by
  unfold methodVersion
  rcases hl : methodVersions.lookup method with _ | last
  · simp
  · simp only [Option.map_eq_some_iff, Option.some.injEq, exists_eq_left']
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hp := List.find?_some hi
      have hm := List.mem_of_find?_eq_some hi
      simp only [beq_iff_eq, List.mem_range] at hp hm
      exact ⟨hp.symm, by omega, by omega⟩
    · rintro ⟨rfl, h1, h2⟩
      let p := fun i => versionedMethod method (i + 1) == versionedMethod method version
      have hsome : ((List.range last).find? p).isSome := List.find?_isSome.mpr
        ⟨version - 1, List.mem_range.mpr (by omega),
          beq_iff_eq.mpr (versionedMethod_inj.mpr ⟨rfl, by omega⟩)⟩
      obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
      have hp := List.find?_some hj
      simp only [p, beq_iff_eq, versionedMethod_inj, true_and] at hp
      exact ⟨j, hj, hp⟩

/-- The versions of `engine_newPayload` are 1 to 5. -/
theorem specifiedMethods_newPayload {version : Nat} :
    versionedMethod "newPayload" version ∈ specifiedMethods ↔ 1 ≤ version ∧ version ≤ 5 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "newPayload" = some 5 by decide]
  simp only [Option.some.injEq, exists_eq_left']

/-- The versions of `engine_forkchoiceUpdated` are 1 to 4. -/
theorem specifiedMethods_forkchoiceUpdated {version : Nat} :
    versionedMethod "forkchoiceUpdated" version ∈ specifiedMethods ↔
      1 ≤ version ∧ version ≤ 4 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "forkchoiceUpdated" = some 4 by decide]
  simp only [Option.some.injEq, exists_eq_left']

/-- The versions of `engine_getPayload` are 1 to 6. -/
theorem specifiedMethods_getPayload {version : Nat} :
    versionedMethod "getPayload" version ∈ specifiedMethods ↔ 1 ≤ version ∧ version ≤ 6 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "getPayload" = some 6 by decide]
  simp only [Option.some.injEq, exists_eq_left']

/-- The versions of `engine_getPayloadBodiesByHash` are 1 and 2. -/
theorem specifiedMethods_getPayloadBodiesByHash {version : Nat} :
    versionedMethod "getPayloadBodiesByHash" version ∈ specifiedMethods ↔
      1 ≤ version ∧ version ≤ 2 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "getPayloadBodiesByHash" = some 2 by decide]
  simp only [Option.some.injEq, exists_eq_left']

/-- The versions of `engine_getPayloadBodiesByRange` are 1 and 2. -/
theorem specifiedMethods_getPayloadBodiesByRange {version : Nat} :
    versionedMethod "getPayloadBodiesByRange" version ∈ specifiedMethods ↔
      1 ≤ version ∧ version ≤ 2 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "getPayloadBodiesByRange" = some 2 by decide]
  simp only [Option.some.injEq, exists_eq_left']

/-- The versions of `engine_getBlobs` are 1 to 4. -/
theorem specifiedMethods_getBlobs {version : Nat} :
    versionedMethod "getBlobs" version ∈ specifiedMethods ↔ 1 ≤ version ∧ version ≤ 4 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "getBlobs" = some 4 by decide]
  simp only [Option.some.injEq, exists_eq_left']

/-- The only version of `engine_exchangeTransitionConfiguration` is 1. -/
theorem specifiedMethods_exchangeTransitionConfiguration {version : Nat} :
    versionedMethod "exchangeTransitionConfiguration" version ∈ specifiedMethods ↔
      version = 1 := by
  rw [mem_specifiedMethods,
    show methodVersions.lookup "exchangeTransitionConfiguration" = some 1 by decide]
  simp only [Option.some.injEq, exists_eq_left']
  omega

/-- The only version of `engine_getClientVersion` is 1. -/
theorem specifiedMethods_getClientVersion {version : Nat} :
    versionedMethod "getClientVersion" version ∈ specifiedMethods ↔ version = 1 := by
  rw [mem_specifiedMethods, show methodVersions.lookup "getClientVersion" = some 1 by decide]
  simp only [Option.some.injEq, exists_eq_left']
  omega

/-! ## `engine_exchangeCapabilities` -/

/-- Reading each string of a list as itself succeeds with the list. -/
private theorem mapM_ok (l : List String) :
    l.mapM (fun x => (Except.ok x : Read String)) = .ok l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.mapM_cons, ih, bind, Except.bind, pure, Except.pure]

/-- A list of names reads back from the parameters that hold it. -/
theorem exchangeCapabilitiesParams_json (methods : List String) :
    exchangeCapabilitiesParams (exchangeCapabilitiesParamsJson methods) = .ok methods := by
  simp [exchangeCapabilitiesParams, exchangeCapabilitiesParamsJson, paramsArray, array_listJson,
    string, mapM_ok, Json.lift, Except.mapError, bind, Except.bind, pure, Except.pure]

/-- The method succeeds exactly when the request decodes, and then answers the supported names.
-/
theorem exchangeCapabilities_eq_ok_iff {supported r : List String} {params : Lean.Json} :
    exchangeCapabilities supported params = .ok r ↔
      r = supported ∧ ∃ methods, exchangeCapabilitiesParams params = .ok methods := by
  unfold exchangeCapabilities
  rcases exchangeCapabilitiesParams params with e | m <;>
    simp [bind, Except.bind, pure, Except.pure, eq_comm]

/-- The request that a consensus node writes gets the names that the execution node supports. -/
theorem exchangeCapabilities_paramsJson (supported methods : List String) :
    exchangeCapabilities supported (exchangeCapabilitiesParamsJson methods) = .ok supported :=
  exchangeCapabilities_eq_ok_iff.mpr ⟨rfl, methods, exchangeCapabilitiesParams_json methods⟩

/-! ## `engine_getClientVersionV1` -/

/-- A version object whose code is two letters reads back from its JSON. -/
theorem clientVersionOfJson_json (v : ClientVersion) (h : IsClientCode v.code) :
    clientVersionOfJson (clientVersionJson v) = .ok v := by
  have hd : [("code", Lean.Json.str v.code), ("name", .str v.name),
      ("version", .str v.version), ("commit", dataJson v.commit.toList)].Pairwise
      fun a b => a.1 ≠ b.1 := by simp
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "clientVersion" hd (by simp [dataJson, isNull_str])
  have hex : hasExactly fs clientVersionFields = true := hasExactly_of_perm hp
  have r1 := field_of_perm (what := "clientVersion") hp hd (List.mem_cons_self ..)
  have r2 := field_of_perm (what := "clientVersion") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have r3 := field_of_perm (what := "clientVersion") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have r4 := field_of_perm (what := "clientVersion") hp hd
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_self ..))))
  have hc : decide (IsClientCode v.code) = true := decide_eq_true h
  unfold clientVersionOfJson clientVersionJson
  simp only [hfs, hex, r1, r2, r3, r4, hc, string, fixed_dataJson, Json.liftM_ok, bind,
    Except.bind, pure, Except.pure, ite_true]

/-- A version object that decodes has a code of two letters. -/
theorem isClientCode_of_clientVersionOfJson {j : Lean.Json} {v : ClientVersion}
    (h : clientVersionOfJson j = .ok v) : IsClientCode v.code := by
  unfold clientVersionOfJson at h
  rcases hf : fields "clientVersion" j with e | fs
  · simp [hf, bind, Except.bind] at h
  cases hx : hasExactly fs clientVersionFields
  · simp [hf, hx, bind, Except.bind] at h
  rcases hc : field "clientVersion" fs "code" with e | cj
  · simp [hf, hx, hc, bind, Except.bind] at h
  rcases hs : string "code" cj with e | code
  · simp [hf, hx, hc, hs, bind, Except.bind] at h
  by_cases hcc : IsClientCode code
  case neg => simp [hf, hx, hc, hs, hcc, bind, Except.bind] at h
  simp only [hf, hx, hc, hs, Json.liftM_ok, bind, Except.bind, decide_eq_true hcc, ite_true,
    pure, Except.pure] at h
  repeat' split at h
  all_goals cases h <;> exact hcc

/-- The method succeeds exactly on one parameter that decodes, and then answers its own object.
-/
theorem getClientVersion_eq_ok_iff {own : ClientVersion} {r : List ClientVersion}
    {params : Lean.Json} :
    getClientVersion own params = .ok r ↔
      r = [own] ∧ ∃ j v, params = .arr #[j] ∧ clientVersionOfJson j = .ok v := by
  unfold getClientVersion
  constructor
  · intro h
    cases params with
    | arr items =>
      simp only [paramsArray, bind, Except.bind, pure, Except.pure] at h
      match hi : items.toList, h with
      | [j], h =>
        simp only [Json.liftM_ok] at h
        rcases hj : clientVersionOfJson j with e | v
        · simp [hj] at h
        · simp only [hj, Except.ok.injEq] at h
          refine ⟨h.symm, j, v, ?_, hj⟩
          congr 1
          exact Array.toList_inj.mp hi
      | [], h => simp [Json.liftM_ok, Json.invalid_eq] at h
      | _ :: _ :: _, h => simp [Json.liftM_ok, Json.invalid_eq] at h
    | _ => simp [paramsArray, bind, Except.bind] at h
  · rintro ⟨rfl, j, v, rfl, hj⟩
    simp [paramsArray, hj, bind, Except.bind, pure, Except.pure]

/-- The request that a consensus node writes gets the object of the execution node alone. -/
theorem getClientVersion_paramsJson (own v : ClientVersion) (h : IsClientCode v.code) :
    getClientVersion own (getClientVersionParamsJson v) = .ok [own] :=
  getClientVersion_eq_ok_iff.mpr ⟨rfl, _, v, rfl, clientVersionOfJson_json v h⟩

end EthLib.Engine
