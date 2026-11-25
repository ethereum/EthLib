module

public import EthLib.Cryptography.Proofs.IndependentAnswers
public import EthLib.Cryptography.Proofs.Sponge.Simulator

/-!
# Proofs: the intermediate games between the two worlds of the sponge

The value at each rooted state comes from a random oracle on block paths.

So the sponge and the game see one value at a path, whichever reaches it first.

The simulator is Algorithm 3 of [Bertoni, Daemen, Peeters, Van Assche, Eurocrypt 2008][sponge].

It is in their §4.3.

[sponge]: https://keccak.team/files/SpongeIndifferentiability.pdf
-/

@[expose] public section

namespace EthLib.Cryptography.Sponge

open OracleComp OracleSpec LazyPermutation Indifferentiability

/-- A query of the second summand, among coins and that summand. -/
abbrev hq {ι : Type} {hs : OracleSpec.{0, 0} ι} (t : ι) :
    OracleComp (unifSpec + hs) (hs.Range t) :=
  (unifSpec + hs).query (.inr t)

/-- The random oracle on block paths that gives the values at rooted states. -/
abbrev TSpec (Dg E C : Type) : OracleSpec (List (Dg × E)) :=
  List (Dg × E) →ₒ SpongeState Dg E C

/-- The random oracles of the intermediate games: the hash, then the oracle on paths. -/
abbrev ASpec (Msg Dg E C : Type) := (Msg →ₒ Dg) + TSpec Dg E C

variable {Dg E C Msg : Type}

section Setting

variable [SampleableType Dg] [SampleableType E] [SampleableType C]

/-- A uniform state, inside the intermediate games. -/
noncomputable abbrev drawSt : OracleComp (unifSpec + ASpec Msg Dg E C) (SpongeState Dg E C) :=
  liftM ($ᵗ (SpongeState Dg E C))

/-- The value at a path: the oracle on paths, with the hash as digest when the path pads. -/
noncomputable def val (P : Padding Msg (Dg × E)) (β : List (Dg × E)) :
    OracleComp (unifSpec + ASpec Msg Dg E C) (SpongeState Dg E C) :=
  match P.unpad β with
  -- The path pads the message `m`: the digest is the hash of `m`, the rest comes from the path.
  | some m => do
    let d ← hq (hs := ASpec Msg Dg E C) (.inl m)
    let t ← hq (hs := ASpec Msg Dg E C) (.inr β)
    pure ((d, t.1.2), t.2)
  | none => hq (hs := ASpec Msg Dg E C) (.inr β)

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
      let v ← val P (β ++ [blockTo s x])
      pure (v, ⟨(x, v) :: σ.edges, (v, β ++ [blockTo s x]) :: σ.chains⟩,
        some (β ++ [blockTo s x], v))
    -- A new state that is not rooted gets the uniform draw `u`.
    | none => pure (u, ⟨(x, u) :: σ.edges, σ.chains⟩, none)

/-- The inverse step of the simulator, with the uniform draw `u` for a new query. -/
def visInv (y u : SpongeState Dg E C) (σ : SimState Dg E C) :
    SpongeState Dg E C × SimState Dg E C :=
  match (σ.edges.map Prod.swap).lookup y with
  | some x => (x, σ)
  | none => (u, ⟨(u, y) :: σ.edges, σ.chains⟩)

/-- The simulator with the values of paths at rooted states, and a uniform draw at each call. -/
noncomputable def idealTImpl (P : Padding Msg (Dg × E)) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (SimState Dg E C) (OracleComp (unifSpec + ASpec Msg Dg E C)))
  | .inl (.inl n) =>
    (liftM ((unifSpec + ASpec Msg Dg E C).query (.inl n)) :
      OracleComp (unifSpec + ASpec Msg Dg E C) (Fin (n + 1)))
  | .inl (.inr (.inl x)) => StateT.mk fun σ => do
    let u ← drawSt
    let r ← visFwd P x u σ
    pure (r.1, r.2.1)
  | .inl (.inr (.inr y)) => StateT.mk fun σ => do
    let u ← drawSt
    pure (visInv y u σ)
  | .inr m => (liftM (hq (hs := ASpec Msg Dg E C) (.inl m)) :
      OracleComp (unifSpec + ASpec Msg Dg E C) Dg)

/-! ## The combined game -/

/-- The capacities a game sees: that of the initial state, and those of both ends of each pair. -/
def knownC (iv : SpongeState Dg E C) (σ : SimState Dg E C) : List C :=
  iv.2 :: σ.edges.flatMap fun e => [e.1.2, e.2.2]

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
  /-- Some answer of the full view differed from that of the visible view. -/
  diff : Bool
  /-- Some draw of the simulator hit a visible capacity. -/
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
    let v ← val P (pre ++ [B])
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
    let _ ← val (C := C) P (pre ++ [B])
    let _ ← drawSt (Msg := Msg) (C := C)
    skel P (pre ++ [B]) bs

/-- The outcome of a combined forward step, from the uniform draw `u` and the simulator step `r`.

It returns the real answer, the ideal answer, and the new state. -/
def fwdOut (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) (cs : CState Dg E C Msg)
    (x u : SpongeState Dg E C)
    (r : SpongeState Dg E C × SimState Dg E C × Option (List (Dg × E) × SpongeState Dg E C)) :
    (SpongeState Dg E C × SpongeState Dg E C) × CState Dg E C Msg :=
  -- The real answer: the recorded one, or the value of a new unused rooted path, or `u`.
  let aR := match cs.all.lookup x with
    | some y => y
    | none => match r.2.2 with
      | some (β, v) => if usedPath P cs.sim.chains cs.hashed β then u else v
      | none => u
  let all' := match cs.all.lookup x with
    | some _ => cs.all
    | none => (x, aR) :: cs.all
  ((aR, r.1), ⟨all', r.2.1, cs.hashed, cs.diff || decide (aR ≠ r.1),
    cs.bad || ((cs.sim.edges.lookup x).isNone && decide (r.1.2 ∈ knownC iv cs.sim))⟩)

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
  let aR := match (cs.all.map Prod.swap).lookup y with
    | some x => x
    | none => u
  let all' := match (cs.all.map Prod.swap).lookup y with
    | some _ => cs.all
    | none => (u, y) :: cs.all
  ((aR, r.1), ⟨all', r.2, cs.hashed, cs.diff || decide (aR ≠ r.1),
    cs.bad || (((cs.sim.edges.map Prod.swap).lookup y).isNone &&
      decide (u.2 ∈ knownC iv cs.sim))⟩)

/-- The combined inverse step. -/
noncomputable def combInv (iv : SpongeState Dg E C) (y : SpongeState Dg E C) :
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
    let d ← hq (hs := ASpec Msg Dg E C) (.inl m)
    pure (hashOut cs m w d)

/-- The combined step: the real answer, then the ideal answer. -/
noncomputable def combStep (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) :
    (t : (GameSpec (SpongeState Dg E C) Msg Dg).Domain) →
      StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))
        ((GameSpec (SpongeState Dg E C) Msg Dg).Range t ×
          (GameSpec (SpongeState Dg E C) Msg Dg).Range t)
  | .inl (.inl n) => do
    let u ← (liftM ((unifSpec + ASpec Msg Dg E C).query (.inl n)) :
      OracleComp (unifSpec + ASpec Msg Dg E C) (Fin (n + 1)))
    pure (u, u)
  | .inl (.inr (.inl x)) => combFwd P iv x
  | .inl (.inr (.inr y)) => combInv iv y
  | .inr m => combHash P iv m

/-- The combined game with the real answers: the real world over random functions. -/
noncomputable def combReal (P : Padding Msg (Dg × E)) (iv : SpongeState Dg E C) :
    QueryImpl (GameSpec (SpongeState Dg E C) Msg Dg)
      (StateT (CState Dg E C Msg) (OracleComp (unifSpec + ASpec Msg Dg E C))) :=
  fun t => Prod.fst <$> combStep P iv t

/-- The combined game with the ideal answers: the ideal world. -/
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
  | .inl (.inl n) =>
    (liftM ((unifSpec + ASpec Msg Dg E C).query (.inl n)) :
      OracleComp (unifSpec + ASpec Msg Dg E C) (Fin (n + 1)))
  | .inl (.inr (.inl x)) => StateT.mk fun vs => do
    let u ← drawSt
    let r ← visFwd P x u vs.1
    pure (r.1, (r.2.1, vs.2.1, vs.2.2 ||
      ((vs.1.edges.lookup x).isNone && decide (r.1.2 ∈ knownC iv vs.1))))
  | .inl (.inr (.inr y)) => StateT.mk fun vs => do
    let u ← drawSt
    let r := visInv y u vs.1
    pure (r.1, (r.2, vs.2.1, vs.2.2 ||
      (((vs.1.edges.map Prod.swap).lookup y).isNone && decide (u.2 ∈ knownC iv vs.1))))
  | .inr m => StateT.mk fun vs => do
    if pre then skel P [] (P.pad m) else pure ()
    let d ← hq (hs := ASpec Msg Dg E C) (.inl m)
    pure (d, (vs.1, m :: vs.2.1, vs.2.2))

end Setting

end EthLib.Cryptography.Sponge
