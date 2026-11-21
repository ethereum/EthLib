module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Proof.Bridge.Security

/-!
# Proofs: the theorem's game is the real game of the security proof

The theorem's game samples `S_0`, runs key generation, then the adversary with the signer.

Its signer keeps its key across requests, as a real signer does.

Key generation hashes `S_0` into the scheme seed `S` first.

The real game of the security proof samples `S_0`, queries that hash, then plays from `S`.

From `S`, it runs the rest of key generation and the same signer.

So the two games are one computation, and the bound of the real game is the theorem's.

The budget counts the hash calls of that one game.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants
open XmssSecurity (HashSpec OracleWorld MasterSeed seedHashInput romImpl HashQueryBound)
open XmssSecurity.Bridge (realGame realAfterSeed realKeygen)
open EthLib.Cryptography.Hash.Keccak (lanesBytes)

/-! ## Key generation from the seed hash -/

/-- The game's `H` is the query to the hash oracle. -/
theorem H_eq_queryH : H = queryH (m := OracleComp HashSpec) :=
  rfl

/-- `S = H("leanXMSS" | S_0)`, one query of the seed hash's input. -/
theorem schemeSeed_queryH (S0 : MasterSeed) :
    (schemeSeed queryH (ofSeed S0) : OracleComp HashSpec Seed)
      = liftM (HashSpec.query (seedHashInput S0)) >>= fun y => pure (ofSeed y) := by
  -- The name's lane is its 8 bytes, and the seed's lanes are its 32 bytes.
  have hinput : lanesBytes (#[SEED_TAG_LANE] ++ (ofSeed S0).toArray) = seedHashInput S0 := by
    rw [Hash.Keccak.lanesBytes_append, Hash.Keccak.lanesBytes_singleton, bytesOfLane_seedTagLane,
      toList_ofSeed]
    rfl
  unfold schemeSeed queryH HashSig.queryLanes
  rw [hinput, map_eq_bind_pure_comp]
  rfl

/-- Key generation in the game: the seed hash, then key generation from its answer `S`. -/
theorem liftM_keyGenWith_bind {β : Type} (S0 : MasterSeed)
    (k : PublicKey × SecretKey → OracleComp OracleWorld β) :
    (liftM (keyGenWith H (ofSeed S0)) : OracleComp OracleWorld _) >>= k
      = liftM (OracleWorld.query (.inr (seedHashInput S0))) >>= fun S =>
          (liftM (realKeygen S) : OracleComp OracleWorld _) >>= k := by
  unfold keyGenWith
  rw [H_eq_queryH, schemeSeed_queryH]
  simp only [liftM_bind, bind_assoc, pure_bind]
  rfl

/-- **The theorem's game is the real game of the security proof.** -/
theorem gameCore_eq_realGame (adversary : Adversary) :
    gameCore adversary = realGame adversary := by
  unfold gameCore realGame realAfterSeed sampleSeed
  rw [liftM_map, bind_map_left]
  refine bind_congr fun S0 => ?_
  rw [liftM_keyGenWith_bind]
  refine bind_congr fun S => bind_congr fun keys => ?_
  rcases keys with ⟨pk, sk⟩
  rfl

/-! ## The theorem -/

/-- An event of the counted experiment is the event of the plain random oracle's run.

It is stated for any game, so the kernel compares the two oracles once, not on a game. -/
theorem prEvent_countedOracle {α : Type} (game : OracleComp OracleWorld α) (P : α → Prop) :
    Pr{let result ← (simulateQ countedOracle game).run.run' ∅}[P result.1]
      = Pr{let x ← (simulateQ romImpl game).run' ∅}[P x] := by
  have h := congrArg (fun c : OracleComp OracleWorld α => (simulateQ romImpl c).run' ∅)
    (XmssSecurity.countHashQueries_forget game)
  simp only [simulateQ_map, StateT.run'_map'] at h
  rw [← h, prEvent_map, XmssSecurity.simulateQ_countHashQueries]
  rfl

/-- The adversary forges as often as it wins the real game. -/
theorem forgeAdvantage_eq (adversary : Adversary) :
    forgeAdvantage adversary
      = Pr{let x ← (simulateQ romImpl (realGame adversary)).run' ∅}[x = true] := by
  unfold forgeAdvantage experiment
  rw [← gameCore_eq_realGame]
  exact prEvent_countedOracle _ fun x : Bool => x = true

/-- A bound on the counted calls of a computation from the empty cache is one on its counted run.

It reads the count as a natural number, as the experiment does. -/
theorem hashQueryBound_iff_counted {α : Type} (oa : OracleComp OracleWorld α) {q : Nat} :
    XmssSecurity.HashQueryBound oa ∅ q ↔
      ∀ result : α × Nat, result ∈ @support ProbComp (α × Nat) _
        ((simulateQ countedOracle oa).run.run' ∅) → result.2 ≤ q := by
  simp only [XmssSecurity.HashQueryBound, XmssSecurity.simulateQ_countHashQueries]
  exact Iff.rfl

/-- The game's budget bounds the calls of the real game, which is the same computation. -/
theorem hashQueryBound_realGame (adversary : Adversary) (q : Nat)
    (h : HasHashQueryBound adversary q) : HashQueryBound (realGame adversary) ∅ q := by
  -- Rewrite the experiment to its run first: the kernel would run the game to compare them.
  have run : experiment adversary =
      ((simulateQ countedOracle (gameCore adversary)).run.run' ∅ :
        ProbComp (Bool × Nat)) := rfl
  unfold HasHashQueryBound at h
  rw [run] at h
  rw [← gameCore_eq_realGame]
  exact (hashQueryBound_iff_counted _).2 h

/-- **leanXMSS as EthLib computes it is strongly unforgeable in the random oracle model.**

The signer keeps its key across requests, as a real signer does.

Take an adversary whose game makes at most `q >= 1` hash calls on every run.

It forges with probability at most `q / 2^127`.

`q` counts the calls of key generation, of every signing request and of the verification.

A signing request can make more than `2^32` calls, when its randomizer trials keep missing.

It can make more than `2^33` when it also builds a bottom tree.

So `2^32` requests give `q > 2^64`, and over the key's lifetime the bound exceeds `2^-63`. -/
theorem unforgeable : HasClassicalSecurityBits 127 := fun q hq adversary hbound =>
  (forgeAdvantage_eq adversary).trans_le
    (XmssSecurity.Bridge.realGame_security q hq adversary
      (hashQueryBound_realGame adversary q hbound))

end EthLib.Cryptography.Xmss.Unforgeability
