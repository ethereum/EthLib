module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderFinish
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.FinderIntervals

/-!
# Finder returns in the native two-layer forgery experiment

The root passed to the upper finder is the root built after lower selection.

A failed lower finder skips the upper call, and both raw errors reach the client log.
-/

@[expose] public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches

open EthLib.Cryptography HashSig Constants OracleComp OracleSpec TwoLayerGraph
    Honest LayerGraph.Hidden

abbrev Body (pp : PublicParam) := StateT (ResidualCache pp) (OracleComp (Ops pp))

/-- Forward an ordinary segment, preserving each public, private or notice operation. -/
noncomputable def physical {pp : PublicParam} {α : Type} (p : Program pp α) : Body pp α :=
  StateT.mk fun r => simulateQ (fun t => liftM ((Ops pp).query (.inl t))) (p.run r)

/-- Run and observe one whole finder. -/
noncomputable def search (pp : PublicParam) (l : Layer) (e : UInt32)
    (msg : ByteArray) : Body pp Answer :=
  StateT.mk fun r => liftM ((Ops pp).query (.inr ⟨l,e,msg,r⟩))

/-- Replace a whole finder operation by its underlying native calls. -/
noncomputable def realize {pp : PublicParam} {α : Type} (p : Body pp α) : Program pp α :=
  StateT.mk fun r => simulateQ (expandCall pp) (p.run r)

@[simp] theorem realize_physical {pp : PublicParam} {α : Type} (p : Program pp α) : realize
    (physical p) = p := by
  ext1 r
  change simulateQ (expandCall pp) (simulateQ _ (p.run r)) = p.run r
  rw [← QueryImpl.simulateQ_compose]
  have eq : QueryImpl.compose (expandCall pp) (fun t => liftM ((Ops pp).query (.inl t))) =
    QueryImpl.id' Queries := by
    funext t
    simp [QueryImpl.compose, expandCall, QueryImpl.id']
  rw [eq, simulateQ_id']

@[simp] theorem realize_search (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray) :
    realize (search pp l e msg) = find pp l e msg := by
  ext1 r
  simp [realize, search, expandCall]

@[simp] theorem realize_pure {pp : PublicParam} {α : Type} (a : α) : realize
    (pure a : Body pp α) = pure a := by
  ext1 r
  simp [realize, StateT.run_pure]

@[simp] theorem realize_bind {pp : PublicParam} {α β : Type} (p : Body pp α) (f : α → Body pp β) :
    realize (p >>= f) = (realize p >>= fun a => realize (f a)) := by
  ext1 r
  simp [realize, StateT.run_bind, simulateQ_bind]

@[simp] theorem realize_map {pp : PublicParam} {α β : Type} (p : Body pp α) (f : α → β) :
    realize (f <$> p) = f <$> realize p := by simp only [map_eq_pure_bind,
      realize_bind, realize_pure]

/-- The two calls retain the same returned words, paths and signature as the normalized signer. -/
noncomputable def signing (pp : PublicParam) (idx : LeafIndex) (msg : Message) : Body pp
    (Except XmssError Signature) := do
  let lower := packBytes msg
  let e := UInt32.ofNat idx.toNat
  let some (rho,x) ← search pp .bottom e lower
    | return .error (.noAdmissibleEncoding .bottom idx.toNat)
  physical (carry (emitted emitStructure pp (simulateQ (selection pp .bottom).liftQuery
    (beforeValues pp .bottom e x))))
  let root ← physical (carry (emitted emitStructure pp (bottomRootSchedule pp idx)))
  let j := bottomTree idx
  let upper := packBytes root
  let some (tau,y) ← search pp .top (UInt32.ofNat j) upper
    | return .error (.noAdmissibleEncoding .top j)
  physical (afterUpper pp idx lower upper rho tau x y)

theorem realize_signing (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    realize (signing pp idx msg) = signature pp idx msg := by
  unfold signing signature afterLower
  simp only [realize_bind, realize_search]
  apply bind_congr
  intro ans
  rcases ans with _ | ⟨rho,x⟩
  · simp
  · simp only [realize_bind, realize_physical, realize_search]
    apply bind_congr
    intro u
    apply bind_congr
    intro root
    apply bind_congr
    intro upper
    rcases upper with _ | ⟨tau,y⟩ <;> simp

noncomputable def clientOracle (pp : PublicParam) : QueryImpl (World + SigningSpec)
    (WriterT RawLog (Body pp))
  | .inl t => liftM (physical (carry (mixedWorldPass pp t)))
  | .inr req => WriterT.mk (do
    let _ ← physical (carry (mixedTick pp))
    let _ ← physical (carry (mixedParameter pp))
    let ans ← signing pp req.leafIndex req.message
    return (ans.toOption, [(req,ans)]))

private theorem realize_client {α : Type} (pp : PublicParam)
    (p : OracleComp (World + SigningSpec) α) :
    realize ((simulateQ (clientOracle pp) p).run) = (simulateQ (oracle pp) p).run := by
  have same (t : (World + SigningSpec).Domain) : realize ((clientOracle pp t).run) =
    (oracle pp t).run := by
    rcases t with t | r
    · simp [clientOracle, oracle]
    · simp [clientOracle, oracle, request, realize_signing]
  induction p using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind',
      realize_bind, same, realize_map, ih]

noncomputable def caller (pp : PublicParam) (A : Adversary) : Body pp Outcome := do
  let root ← physical (carry (liftM (emitStructure (simulateQ (selection pp .top).liftQuery
    (beforeNode pp .top LAYER_HEIGHT 0 >>= fun _ => LayerGraph.readOutput
      (LayerGraph.treeRole LAYER_HEIGHT 0))))))
  let pk : PublicKey := ⟨root, pp⟩
  let (candidate,records) ← (simulateQ (clientOracle pp) (A.main pk)).run
  let verified ← physical
    (carry (liftM (verifyWith mixedHash pk candidate.message candidate.signature)))
  return ⟨pk,candidate,records,verified⟩

theorem realize_caller (pp : PublicParam) (A : Adversary) : realize (caller pp A) = game pp A := by
  simp [caller, game, realize_client]

/-- The stopped caller records each completed finder and the physical query history. -/
noncomputable def observedGame (pp : PublicParam) (A : Adversary) (q : Nat)
    (r : ResidualCache pp) :=
  (((simulateQ (observeCall pp q) ((caller pp A).run r)).run).run q).run (initial,[])

/-- Removing the extra observations recovers the original capped joint experiment exactly. -/
theorem erase_observedGame (pp : PublicParam) (A : Adversary) (q : Nat) (r : ResidualCache pp) :
    (fun z => (z.1.1,z.2.1)) <$> observedGame pp A q r = chronicleGame pp A q r := by
  have same := congrArg (fun (p : Program pp Outcome) => p.run r) (realize_caller pp A)
  simp only [realize, StateT.run_mk] at same
  unfold observedGame chronicleGame
  rw [erase q ((caller pp A).run r) q (initial,[]), same]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix.FinderNotices.Searches
