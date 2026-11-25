module

public import EthLib.Cryptography.Proofs.IndependentAnswers
public import EthLib.Cryptography.Proofs.RandomOracleWithCoins
public import EthLib.Cryptography.Proofs.Sponge.Simulator

/-!
# Proofs: the intermediate games between the two worlds of the sponge

The value at each rooted state comes from a random oracle on block paths.

So the sponge and the simulator see one value at a path, whichever asks it first.

The simulator simplifies Algorithm 3 of [Bertoni et al., Eurocrypt 2008][sponge], §4.3.

Here it takes the value at a new rooted state from the oracle on paths.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge.Indiff

open OracleComp OracleSpec LazyPermutation Indifferentiability

/-- The random oracle on block paths that gives the values at rooted states. -/
abbrev TSpec (Dg E C : Type) : OracleSpec (List (Dg × E)) :=
  List (Dg × E) →ₒ SpongeState Dg E C

/-- The random oracles of the intermediate games: the hash, then the oracle on paths. -/
abbrev ASpec (Msg Dg E C : Type) := (Msg →ₒ Dg) + TSpec Dg E C

variable {Dg E C Msg : Type}

/-- A coin of the intermediate games, passed through, beside a state `σ`. -/
abbrev coinQuery {σ : Type} (n : ℕ) :
    StateT σ (OracleComp (unifSpec + ASpec Msg Dg E C)) (Fin (n + 1)) :=
  (liftM ((unifSpec + ASpec Msg Dg E C).query (.inl n)) :
    OracleComp (unifSpec + ASpec Msg Dg E C) (Fin (n + 1)))

/-! ## Cached values of paths -/

/-- The cache of the random oracles of the intermediate games. -/
abbrev ACache (Msg Dg E C : Type) := (ASpec Msg Dg E C).QueryCache

/-- The cached value of a path, when the answers it reads are cached. -/
noncomputable def cachedPathValue (P : Padding Msg (Dg × E)) (c : ACache Msg Dg E C)
    (β : List (Dg × E)) : Option (SpongeState Dg E C) :=
  match P.unpad β with
  | some m => (c (.inl m)).bind fun d => (c (.inr β)).map fun t => ((d, t.1.2), t.2)
  | none => c (.inr β)

/-- The oracle points that the value of the path `β` reads. -/
def ValPt (P : Padding Msg (Dg × E)) (β : List (Dg × E)) : (ASpec Msg Dg E C).Domain → Prop
  | .inl m => P.unpad β = some m
  | .inr γ => γ = β

section Setting

variable [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- A uniform state, inside the intermediate games. -/
noncomputable abbrev drawSt : OracleComp (unifSpec + ASpec Msg Dg E C) (SpongeState Dg E C) :=
  liftM ($ᵗ (SpongeState Dg E C))

/-- The value at a path: the oracle on paths, with the hash as digest when the path pads. -/
noncomputable def pathValue (P : Padding Msg (Dg × E)) (β : List (Dg × E)) :
    OracleComp (unifSpec + ASpec Msg Dg E C) (SpongeState Dg E C) :=
  match P.unpad β with
  -- The path pads the message `m`: the digest is the hash of `m`, the rest comes from the path.
  | some m => do
    let d ← queryRight (hs := ASpec Msg Dg E C) (.inl m)
    let t ← queryRight (hs := ASpec Msg Dg E C) (.inr β)
    pure ((d, t.1.2), t.2)
  | none => queryRight (hs := ASpec Msg Dg E C) (.inr β)

/-! ## Random functions -/

/-- The real world with a random function in place of the permutation, in both directions. -/
def funImpl [XorOp Dg] [XorOp E] [FinEnum (SpongeState Dg E C)] (P : Padding Msg (Dg × E))
    (iv : SpongeState Dg E C) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (IndepState (SpongeState Dg E C)) ProbComp) :=
  -- A new answer is uniform over all states, and a repeated answer raises the flag.
  indepPermImpl (A := SpongeState Dg E C) + fun m =>
    sponge P iv (fun x => indepPermOracle (A := SpongeState Dg E C) (.inl x)) m

/-! ## The simulator over path values -/

variable [XorOp Dg] [XorOp E] [DecidableEq Dg] [DecidableEq E] [DecidableEq C]

/-- The forward step of the simulator, with the value of a path at a new rooted state.

It returns the answer, the new state, and the path and value of a new rooted state, if any. -/
noncomputable def visFwd (P : Padding Msg (Dg × E)) (x u : SpongeState Dg E C)
    (σ : SimState Dg E C) :
    OracleComp (unifSpec + ASpec Msg Dg E C)
      (SpongeState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpongeState Dg E C)) :=
  match σ.edges.lookup x with
  | some y => pure (y, σ, none)
  | none =>
    match chainOf σ.chains x with
    | some (s, β) => do
      let v ← pathValue P (β ++ [blockTo s x])
      pure (v, σ.recordRooted x v (β ++ [blockTo s x]), some (β ++ [blockTo s x], v))
    -- A new state that is not rooted gets the uniform draw `u`.
    | none => pure (u, σ.record x u, none)

/-- The inverse step of the simulator, with the uniform draw `u` for a new query. -/
def visInv (y u : SpongeState Dg E C) (σ : SimState Dg E C) :
    SpongeState Dg E C × SimState Dg E C :=
  match (σ.edges.map Prod.swap).lookup y with
  | some x => (x, σ)
  | none => (u, σ.record u y)

/-- The simulator with the values of paths at rooted states, and a uniform draw at each call. -/
noncomputable def idealTImpl (P : Padding Msg (Dg × E)) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (SimState Dg E C) (OracleComp (unifSpec + ASpec Msg Dg E C)))
  | .inl (.inl n) => coinQuery n
  | .inl (.inr (.inl x)) => StateT.mk fun σ => do
    let u ← drawSt
    let r ← visFwd P x u σ
    pure (r.1, r.2.1)
  | .inl (.inr (.inr y)) => StateT.mk fun σ => do
    let u ← drawSt
    pure (visInv y u σ)
  | .inr m => (liftM (queryRight (hs := ASpec Msg Dg E C) (.inl m)) :
      OracleComp (unifSpec + ASpec Msg Dg E C) Dg)

/-! ## The combined game -/

/-- The capacities a game sees: that of the initial state, and those of both ends of each pair. -/
def knownC (iv : SpongeState Dg E C) (σ : SimState Dg E C) : List C :=
  iv.2 :: σ.edges.flatMap fun e => [e.1.2, e.2.2]

/-- Whether a new answer of the simulator has a capacity `k` seen before the query. -/
abbrev hitsKnown (iv : SpongeState Dg E C) (σ : SimState Dg E C) (new : Bool) (k : C) : Bool :=
  new && decide (k ∈ knownC iv σ)

/-- Whether the value of a path was asked: a rooted path, or a prefix of a hashed padding. -/
def usedPath (P : Padding Msg (Dg × E)) (VC : List (SpongeState Dg E C × List (Dg × E)))
    (hashed : List Msg) (β : List (Dg × E)) : Bool :=
  decide (β ∈ VC.map Prod.snd) || hashed.any fun m => decide (β ≠ [] ∧ β <+: P.pad m)

/-- The state of the combined game. -/
structure CState (Dg E C Msg : Type) where
  /-- The full view: every pair of the real world, the most recent first. -/
  all : PermCache (SpongeState Dg E C)
  /-- The visible view: the state of the simulator. -/
  sim : SimState Dg E C
  /-- The hashed messages, the most recent first. -/
  hashed : List Msg
  /-- Some real answer differed from the ideal answer. -/
  diff : Bool
  /-- Some new answer of the simulator had a capacity seen before the query. -/
  bad : Bool

/-- The first state of the combined game. -/
def CState.init (iv : SpongeState Dg E C) : CState Dg E C Msg :=
  ⟨[], SimState.init iv, [], false, false⟩

/-- The walk of the full view along the sponge path of a list of blocks. -/
noncomputable def allWalk (P : Padding Msg (Dg × E)) (used : List (Dg × E) → Bool) :
    List (Dg × E) → SpongeState Dg E C → PermCache (SpongeState Dg E C) → List (Dg × E) →
      OracleComp (unifSpec + ASpec Msg Dg E C)
        (SpongeState Dg E C × PermCache (SpongeState Dg E C))
  | _, s, A, [] => pure (s, A)
  | pre, s, A, B :: bs => do
    -- Each block draws the value of the path so far and a uniform state.
    let v ← pathValue P (pre ++ [B])
    let u ← drawSt
    match A.lookup (absorb s B) with
    | some y => allWalk P used (pre ++ [B]) y A bs
    | none =>
      -- A new state takes the value of its path, or the uniform state if the path was used.
      let y := if used (pre ++ [B]) then u else v
      allWalk P used (pre ++ [B]) y ((absorb s B, y) :: A) bs

/-- The queries of the walk of the full view, with the answers discarded. -/
noncomputable def skel (P : Padding Msg (Dg × E)) :
    List (Dg × E) → List (Dg × E) → OracleComp (unifSpec + ASpec Msg Dg E C) Unit
  | _, [] => pure ()
  | pre, B :: bs => do
    let _ ← pathValue (C := C) P (pre ++ [B])
    let _ ← drawSt (Msg := Msg) (C := C)
    skel P (pre ++ [B]) bs

/-- The outcome of a combined forward step, from the uniform draw `u` and the simulator step `r`.

It returns the real answer, the ideal answer, and the new state. -/
def fwdOut (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (cs : CState Dg E C Msg)
    (x u : SpongeState Dg E C)
    (r : SpongeState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpongeState Dg E C)) :
    (SpongeState Dg E C × SpongeState Dg E C) × CState Dg E C Msg :=
  -- The real answer: the recorded one, or the value of a new unused rooted path, or `u`.
  let old := cs.all.lookup x
  let aR := match old with
    | some y => y
    | none => match r.2.2 with
      | some (β, v) => if usedPath P cs.sim.chains cs.hashed β then u else v
      | none => u
  let all' := match old with
    | some _ => cs.all
    | none => (x, aR) :: cs.all
  ((aR, r.1), ⟨all', r.2.1, cs.hashed, cs.diff || decide (aR ≠ r.1),
    cs.bad || hitsKnown iv cs.sim (cs.sim.edges.lookup x).isNone r.1.2⟩)

/-- The combined forward step: the real and the ideal answer, from one uniform draw. -/
noncomputable def combFwd (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C)
    (x : SpongeState Dg E C) :
    StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))
      (SpongeState Dg E C × SpongeState Dg E C) := StateT.mk fun cs => do
  let u ← drawSt
  let r ← visFwd P x u cs.sim
  pure (fwdOut P iv cs x u r)

/-- The outcome of a combined inverse step at `y`, from the uniform draw `u`. -/
def invOut (iv : SpongeState Dg E C) (cs : CState Dg E C Msg) (y u : SpongeState Dg E C) :
    (SpongeState Dg E C × SpongeState Dg E C) × CState Dg E C Msg :=
  let r := visInv y u cs.sim
  let old := (cs.all.map Prod.swap).lookup y
  let aR := match old with
    | some x => x
    | none => u
  let all' := match old with
    | some _ => cs.all
    | none => (u, y) :: cs.all
  ((aR, r.1), ⟨all', r.2, cs.hashed, cs.diff || decide (aR ≠ r.1),
    cs.bad || hitsKnown iv cs.sim ((cs.sim.edges.map Prod.swap).lookup y).isNone u.2⟩)

/-- The combined inverse step at `y`: the real and the ideal answer, from one uniform draw. -/
noncomputable def combInverse (iv : SpongeState Dg E C) (y : SpongeState Dg E C) :
    StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))
      (SpongeState Dg E C × SpongeState Dg E C) := StateT.mk fun cs => do
  let u ← drawSt
  pure (invOut iv cs y u)

/-- The outcome of a combined hash step at `m`, from the end `w` of the walk and the hash `d`. -/
def hashOut (cs : CState Dg E C Msg) (m : Msg)
    (w : SpongeState Dg E C × PermCache (SpongeState Dg E C)) (d : Dg) :
    (Dg × Dg) × CState Dg E C Msg :=
  ((w.1.1.1, d), ⟨w.2, cs.sim, m :: cs.hashed, cs.diff || decide (w.1.1.1 ≠ d), cs.bad⟩)

/-- The combined hash step: the digest at the end of the walk, and the hash. -/
noncomputable def combHash (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (m : Msg) :
    StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C)) (Dg × Dg) :=
  StateT.mk fun cs => do
    let w ← allWalk P (usedPath P cs.sim.chains cs.hashed) [] iv cs.all (P.pad m)
    let d ← queryRight (hs := ASpec Msg Dg E C) (.inl m)
    pure (hashOut cs m w d)

/-- The combined step: the real answer, then the ideal answer. -/
noncomputable def combStep (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) :
    (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain) →
      StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))
        ((GameSpec (SpongeState Dg E C) Msg Dg).Range t ×
          (GameSpec (SpongeState Dg E C) Msg Dg).Range t)
  | .inl (.inl n) => do
    let u ← coinQuery n
    pure (u, u)
  | .inl (.inr (.inl x)) => combFwd P iv x
  | .inl (.inr (.inr y)) => combInverse iv y
  | .inr m => combHash P iv m

/-- The combined game that answers each query with its real answer. -/
noncomputable def combReal (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))) :=
  fun t => Prod.fst <$> combStep P iv t

/-- The combined game that answers each query with its ideal answer. -/
noncomputable def combIdeal (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))) :=
  fun t => Prod.snd <$> combStep P iv t

/-! ## The visible games -/

/-- The visible state: the state of the simulator, the hashed messages and the collision flag. -/
abbrev VState (Dg E C Msg : Type) := SimState Dg E C × List Msg × Bool

/-- The visible part of a combined state. -/
def CState.vis (cs : CState Dg E C Msg) : VState Dg E C Msg := (cs.sim, cs.hashed, cs.bad)

/-- The ideal side of the combined game without the full view.

The flag `pre` says whether the sponge still asks the values of its paths. -/
noncomputable def visImpl (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (pre : Bool) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (VState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C)))
  | .inl (.inl n) => coinQuery n
  | .inl (.inr (.inl x)) => StateT.mk fun vs => do
    let u ← drawSt
    let r ← visFwd P x u vs.1
    pure (r.1, (r.2.1, vs.2.1, vs.2.2 || hitsKnown iv vs.1 (vs.1.edges.lookup x).isNone r.1.2))
  | .inl (.inr (.inr y)) => StateT.mk fun vs => do
    let u ← drawSt
    let r := visInv y u vs.1
    pure (r.1, (r.2, vs.2.1,
      vs.2.2 || hitsKnown iv vs.1 ((vs.1.edges.map Prod.swap).lookup y).isNone u.2))
  | .inr m => StateT.mk fun vs => do
    if pre then skel P [] (P.pad m) else pure ()
    let d ← queryRight (hs := ASpec Msg Dg E C) (.inl m)
    pure (d, (vs.1, m :: vs.2.1, vs.2.2))

/-! ## The walk of the full view as a function -/

/-- The walk of the full view, as a function of the path values `vf` and the uniform draws `us`. -/
def detWalk (used : List (Dg × E) → Bool) (vf : List (Dg × E) → SpongeState Dg E C) :
    List (Dg × E) → SpongeState Dg E C → PermCache (SpongeState Dg E C) → List (Dg × E) →
      List (SpongeState Dg E C) → SpongeState Dg E C × PermCache (SpongeState Dg E C)
  | _, s, A, [], _ => (s, A)
  | pre, s, A, B :: bs, us =>
    match A.lookup (absorb s B) with
    | some y => detWalk used vf (pre ++ [B]) y A bs us.tail
    | none =>
      let y := if used (pre ++ [B]) then us.headD s else vf (pre ++ [B])
      detWalk used vf (pre ++ [B]) y ((absorb s B, y) :: A) bs us.tail

end Setting

end EthLib.Cryptography.Sponge.Indiff
