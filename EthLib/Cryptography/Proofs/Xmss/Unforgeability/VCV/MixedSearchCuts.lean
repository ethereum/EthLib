module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.MixedSignerProgram

/-!
# Private and public states around each signing search

The randomizer lookup runs from a named private table.

Its result is the base of the public finder on the same path.

A failed finder retains the private cache and the complete public search prefix.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open EthLib.Cryptography HashSig Constants TwoLayerGraph Honest OracleComp OracleSpec
variable {G : Type}

@[expose] def MixedRun {pp : PublicParam} {α : Type}
    (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (p : MixedLocal pp α) (r : ResidualCache pp) (s : G) (a : α) (next : ResidualCache pp)
    (t : G) : Prop :=
  ((a, next), t) ∈ support ((simulateQ impl (p.run r)).run s)

protected theorem MixedRun.bind {pp : PublicParam} {α β : Type}
    {impl : QueryImpl MixedWorld (StateT G ProbComp)}
    {p : MixedLocal pp α} {f : α → MixedLocal pp β} {r s a next t}
    (ran : MixedRun impl (p >>= f) r s a next t) :
    ∃ b mid g, MixedRun impl p r s b mid g ∧ MixedRun impl (f b) mid g a next t := by
  unfold MixedRun at ran ⊢
  simp only [StateT.run_bind, simulateQ_bind, mem_support_bind_iff] at ran
  obtain ⟨⟨⟨b, mid⟩, g⟩, h, k⟩ := ran
  exact ⟨b, mid, g, h, k⟩

protected theorem MixedRun.pure_result {pp : PublicParam} {α : Type}
    {impl : QueryImpl MixedWorld (StateT G ProbComp)} {r s a b next t}
    (ran : MixedRun impl (pure a : MixedLocal pp α) r s b next t) : b = a ∧ next = r ∧ t = s := by
  unfold MixedRun at ran
  simpa [and_assoc] using ran

protected theorem MixedRun.lifted {pp : PublicParam} {α : Type}
    {impl : QueryImpl MixedWorld (StateT G ProbComp)}
    {p : OracleComp MixedWorld α} {r s a next t}
    (ran : MixedRun impl (liftM p : MixedLocal pp α) r s a next t) :
    next = r ∧ (a,t) ∈ support ((simulateQ impl p).run s) := by
  unfold MixedRun at ran
  simp only [StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_pure, StateT.run_bind,
    StateT.run_pure, mem_support_bind_iff, mem_support_pure_iff] at ran
  obtain ⟨⟨val, g⟩, hv, eq⟩ := ran
  cases eq
  exact ⟨rfl, hv⟩

abbrev FindAnswer := Option (Randomizer × Vector (Fin CHAIN_LENGTH) V)

/-- The source of the base and the result of the complete bounded search share one cut. -/
@[expose] def SearchCut (pp : PublicParam) (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (l : Layer) (e : UInt32) (msg : ByteArray) (r : ResidualCache pp) (s : G)
    (out : FindAnswer) (next : ResidualCache pp) (t : G) : Prop :=
  ∃ (bytes : Vector UInt8 32) (afterRandomizer : G),
    MixedRun impl (mixedRandomizer pp l e msg) r s bytes next afterRandomizer ∧
    (out, t) ∈ support ((simulateQ impl (Xmss.Internal.findCodeword mixedHash pp l e msg
      (halfOf 0 bytes) 0 MAX_RANDOMIZER_TRIALS)).run afterRandomizer)

/-- The lower row in the supplied table is the row inspected by this exact private request. -/
theorem find_cut (pp : PublicParam) (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (l : Layer) (e : UInt32) (msg : ByteArray) {r s out next t}
    (ran : MixedRun impl (mixedFind pp l e msg) r s out next t) :
      SearchCut pp impl l e msg r s out next t := by
  unfold mixedFind at ran
  obtain ⟨bytes, mid, graph, seed, finder⟩ := ran.bind
  obtain ⟨rfl, actual⟩ := finder.lifted
  exact ⟨bytes, graph, seed, actual⟩

/-- The top finder is reached before the authentication path is read.

Its private output table is already the final one, on success and on failure. -/
theorem upper_cut (emit : Structural) (pp : PublicParam)
    (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (e : Nat) (msg : ByteArray) {r s ans next t}
    (ran : MixedRun impl (mixedTop emit pp e msg) r s ans next t) :
    ∃ (found : FindAnswer) (finish : G),
      SearchCut pp impl .top (UInt32.ofNat e) msg r s found next finish ∧
      match found with
      | none => ans = .error (.noAdmissibleEncoding .top e)
      | some (rho, _) => ∃ sig, ans = .ok sig ∧ sig.randomizer = rho := by
  unfold mixedTop at ran
  obtain ⟨ots, mid, g, signing, finish⟩ := ran.bind
  unfold mixedOts at signing
  obtain ⟨found, saved, cut, finder, after⟩ := signing.bind
  have physical := find_cut pp impl .top _ msg finder
  cases found with
  | none =>
    obtain ⟨rfl, rfl, rfl⟩ := after.pure_result
    obtain ⟨rfl, rfl, rfl⟩ := finish.pure_result
    exact ⟨none, _, physical, rfl⟩
  | some pair =>
    obtain ⟨rho, digits⟩ := pair
    obtain ⟨ys, still, g₁, chain, returned⟩ := after.bind
    obtain ⟨rfl, _, _⟩ := returned.pure_result
    obtain ⟨unchanged, _⟩ := chain.lifted
    obtain ⟨path, finalState, g₂, pathCall, packed⟩ := finish.bind
    obtain ⟨eq, back, _⟩ := packed.pure_result
    obtain ⟨same, _⟩ := pathCall.lifted
    subst ans
    subst next
    subst finalState
    subst mid
    subst still
    exact ⟨some (rho, digits), _, physical, _, rfl, rfl⟩

/-- The message of the upper search is the bottom root read immediately before it. -/
theorem tree_cut (emit : Structural) (pp : PublicParam)
    (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (idx : LeafIndex) {r s ans next t}
    (ran : MixedRun impl (mixedTree emit pp idx) r s ans next t) :
    ∃ (root : Digest) (atRoot : G) (found : FindAnswer) (finish : G),
      (root, atRoot) ∈ support ((simulateQ impl (emit (bottomRootSchedule pp idx))).run s) ∧
      SearchCut pp impl .top (UInt32.ofNat (bottomTree idx))
        (packBytes root) r atRoot found next finish ∧
      match found with
      | none => ans = .error (.noAdmissibleEncoding .top (bottomTree idx))
      | some (rho, _) => ∃ path sig, ans = .ok (path, sig) ∧ sig.randomizer = rho := by
  unfold mixedTree at ran
  obtain ⟨root, localRoot, atRoot, rootRun, suffix⟩ := ran.bind
  obtain ⟨rfl, actualRoot⟩ := rootRun.lifted
  obtain ⟨top, localTop, afterTop, topRun, pathRun⟩ := suffix.bind
  obtain ⟨found, finish, search, result⟩ := upper_cut emit pp impl _ _ topRun
  cases found with
  | none =>
    subst top
    obtain ⟨rfl, rfl, _⟩ := pathRun.pure_result
    exact ⟨root, atRoot, none, finish, actualRoot, search, rfl⟩
  | some pair =>
    obtain ⟨rho, x⟩ := pair
    obtain ⟨sig, rfl, rhoEq⟩ := result
    obtain ⟨path, rest, g, reveal, pack⟩ := pathRun.bind
    obtain ⟨rfl, rfl, _⟩ := pack.pure_result
    obtain ⟨rfl, _⟩ := reveal.lifted
    exact ⟨root, atRoot, some (rho,x), finish, actualRoot, search, path, sig, rfl, rhoEq⟩

/-- The first lookup is always attempted.

After a successful lower search, the upper lookup uses the private table left by the lower one.

Both failed and successful upper searches retain their original base and public finder endpoint. -/
theorem signature_cuts (emit : Structural) (pp : PublicParam)
    (impl : QueryImpl MixedWorld (StateT G ProbComp))
    (idx : LeafIndex) (msg : Message) {r s ans next t}
    (ran : MixedRun impl (mixedSignature emit pp idx msg) r s ans next t) :
    let e := UInt32.ofNat idx.toNat
    ∃ (low : FindAnswer) (mid : ResidualCache pp) (endLow : G),
      SearchCut pp impl .bottom e (packBytes msg) r s low mid endLow ∧
      match low with
      | none => ans = .error (.noAdmissibleEncoding .bottom idx.toNat) ∧ next = mid
      | some (lowerRho, x) => ∃ (beforeRoot : G) (root : Digest) (atRoot : G)
          (high : FindAnswer) (endHigh : G),
          ((), beforeRoot) ∈
            support ((simulateQ impl (emit (simulateQ (selection pp .bottom).liftQuery
            (LayerGraph.Hidden.beforeValues pp .bottom e x)))).run endLow) ∧
          (root, atRoot) ∈
            support ((simulateQ impl (emit (bottomRootSchedule pp idx))).run beforeRoot) ∧
          SearchCut pp impl .top (UInt32.ofNat (bottomTree idx))
            (packBytes root) mid atRoot high next endHigh ∧
          match high with
          | none => ans = .error (.noAdmissibleEncoding .top (bottomTree idx))
          | some (upperRho, _) => ∃ sig, ans = .ok sig ∧ sig.bottom.randomizer = lowerRho ∧
              sig.top.randomizer = upperRho := by
  dsimp only
  unfold mixedSignature at ran
  obtain ⟨low, mid, endLow, lowerRun, rest⟩ := ran.bind
  refine ⟨low, mid, endLow, find_cut pp impl .bottom _ _ lowerRun, ?_⟩
  cases low with
  | none =>
    obtain ⟨a, localEq, _⟩ := rest.pure_result
    exact ⟨a, localEq⟩
  | some pair =>
    obtain ⟨rho, x⟩ := pair
    obtain ⟨u, before, g, touch, signed⟩ := rest.bind
    obtain ⟨rfl, touched⟩ := touch.lifted
    obtain ⟨upper, localTree, g₂, upperRun, reply⟩ := signed.bind
    obtain ⟨root, afterRoot, high, endHigh, stored, physical,
      answer⟩ := tree_cut emit pp impl idx upperRun
    refine ⟨g, root, afterRoot, high, endHigh, touched, stored, ?_⟩
    cases high with
    | none =>
      subst upper
      obtain ⟨rfl, rfl, _⟩ := reply.pure_result
      exact ⟨physical, rfl⟩
    | some pair =>
      obtain ⟨topRho, y⟩ := pair
      obtain ⟨path, top, rfl, observed⟩ := answer
      obtain ⟨ys, still, last, revelation, packing⟩ := reply.bind
      obtain ⟨rfl, rfl, _⟩ := packing.pure_result
      obtain ⟨rfl, _⟩ := revelation.lifted
      exact ⟨physical, _, rfl, rfl, observed⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
