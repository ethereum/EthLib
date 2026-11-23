module

public import EthLib.Cryptography.Proofs.Xmss.QueryBound
public import EthLib.Cryptography.Proofs.HashSig.Calls

/-!
# Proofs: the hash calls of leanXMSS key generation, signing and verification

For the bounds, each call of `H` makes at most one query on every path.

- Key generation takes at most `1 + 205 * 2^16 = 13434881` calls.
- Signing in a tree the key keeps takes at most `2^32 + 204 = 4294967500` calls.
- Signing with any key takes at most `2^33 + 205 * 2^16 + 407 = 8603369879` calls.
  That covers a tree the key must build, and the top key's signature of its root.
- Verification takes at most `384` calls, as the query bounds of the algorithms already prove.

The signing bounds charge each randomizer search all `2^32` trials.

The top key's path is read from the key, so signing never hashes the top tree.

Key generation does not search.

So under fixed answers, when each call of `H` makes exactly one query, it makes `13434881` calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Cost

open OracleSpec OracleComp
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.Xmss.Internal (signRootWith cacheTreeWith fetchTreeWith)
open EthLib.Cryptography.HashSig (queriesWith queriesWith_bind queriesWith_pure
  length_queriesWith_ofFnInOrder_const length_queriesWith_chain length_queriesWith_node
  queriesWith_build)

/-! ## The constants -/

/-- The bound `1 + 205 * 2^16` of key generation is `13434881`. -/
theorem keyGenCalls_eq : 1 + 205 * 2 ^ LAYER_HEIGHT = 13434881 := by
  decide

/-- The bound `2^32 + 204` of signing in a kept tree is `4294967500`. -/
theorem signKeptCalls_eq : MAX_RANDOMIZER_TRIALS + 204 = 4294967500 := by
  decide

/-- The bound `2^33 + 205 * 2^16 + 407` of signing is `8603369879`. -/
theorem signCalls_eq : 2 * MAX_RANDOMIZER_TRIALS + 205 * 2 ^ LAYER_HEIGHT + 407 = 8603369879 := by
  decide

/-! ## Upper bounds on every path -/

section Bounds

/- A concrete height would let Lean unfold a whole tree, so the height stays opaque. -/
attribute [local irreducible] LAYER_HEIGHT

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {H : Array UInt64 → OracleComp spec Lanes4}

/-- The scheme seed is one call of `H`. -/
theorem isQueryBoundP_schemeSeed (hH : ∀ x, IsQueryBoundP (H x) p 1) (seed : Seed) :
    IsQueryBoundP (schemeSeed H seed) p 1 :=
  hH _

/-- A derivation from the scheme seed is one call of `H`. -/
theorem isQueryBoundP_seedPrf (hH : ∀ x, IsQueryBoundP (H x) p 1) (s : Seed)
    (publicParam : PublicParam)
    (address : Address) (suffix : Array UInt64) :
    IsQueryBoundP (seedPrf H s publicParam address suffix) p 1 :=
  hH _

/-- Key generation is the scheme seed, the parameter and the top tree.

It makes at most `1 + 205 * 2^16` calls. -/
theorem isQueryBoundP_keyGenWith (hH : ∀ x, IsQueryBoundP (H x) p 1) (seed : Seed) :
    IsQueryBoundP (keyGenWith H seed) p (1 + 205 * 2 ^ LAYER_HEIGHT) := by
  unfold keyGenWith Internal.keyGenFrom
  refine isQueryBoundP_bind (isQueryBoundP_schemeSeed hH seed) fun s _ =>
    (isQueryBoundP_bind (isQueryBoundP_publicParamOf
      (isQueryBoundP_seedPrf hH s)) fun publicParam _ =>
      isQueryBoundP_bind (m := 0)
        (isQueryBoundP_build hH (isQueryBoundP_seedPrf hH s) publicParam .top LAYER_HEIGHT 0)
        fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp [LAYER_HEIGHT]

/-- The top key's signature of a root is one search: at most `2^32 + 204` calls. -/
theorem isQueryBoundP_signRootWith (hH : ∀ x, IsQueryBoundP (H x) p 1)
    {prf : SeedPrf (OracleComp spec)} (hprf : ∀ publicParam a suffix, IsQueryBoundP
      (prf publicParam a suffix) p 1)
    (sk : SecretKey) (b : Nat) (root : Digest) :
    IsQueryBoundP (signRootWith H prf sk b root) p (2 ^ 32 + 204) := by
  unfold signRootWith
  simp only [Internal.otsSignTrials_hashTrials]
  refine (isQueryBoundP_bind (m := 0)
    (isQueryBoundP_otsSign hH hprf _ _ _ _) fun r _ => ?_).mono
    (le_of_eq (Nat.add_zero _))
  rcases r with _ | ⟨rho, y⟩ <;> exact isQueryBoundP_pure _ _ _

/-- A bottom tree with its top signature: at most `205 * 2^16 - 1 + 2^32 + 204` calls. -/
theorem isQueryBoundP_cacheTreeWith (hH : ∀ x, IsQueryBoundP (H x) p 1)
    {prf : SeedPrf (OracleComp spec)} (hprf : ∀ publicParam a suffix, IsQueryBoundP
      (prf publicParam a suffix) p 1)
    (sk : SecretKey) (b : Nat) :
    IsQueryBoundP (cacheTreeWith H prf sk b) p (2 ^ LAYER_HEIGHT * 205 - 1 + (2 ^ 32 + 204)) := by
  unfold cacheTreeWith
  exact isQueryBoundP_bind
    (isQueryBoundP_build hH hprf _ .bottom LAYER_HEIGHT b) fun _ _ =>
      (isQueryBoundP_bind (m := 0) (isQueryBoundP_signRootWith hH hprf sk b _) fun _ _ =>
        isQueryBoundP_pure _ _ 0).mono (le_of_eq (Nat.add_zero _))

/-- Fetching a bottom tree costs at most building it. -/
theorem isQueryBoundP_fetchTreeWith (hH : ∀ x, IsQueryBoundP (H x) p 1)
    {prf : SeedPrf (OracleComp spec)} (hprf : ∀ publicParam a suffix, IsQueryBoundP
      (prf publicParam a suffix) p 1)
    (sk : SecretKey) (b : Nat) :
    IsQueryBoundP (fetchTreeWith H prf sk b) p (2 ^ LAYER_HEIGHT * 205 - 1 + (2 ^ 32 + 204)) := by
  unfold fetchTreeWith
  split
  · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
  · exact (isQueryBoundP_bind (m := 0) (isQueryBoundP_cacheTreeWith hH hprf sk b) fun _ _ =>
      isQueryBoundP_pure _ _ 0).mono (le_of_eq (Nat.add_zero _))

/-- Fetching a bottom tree that the key keeps makes no call. -/
theorem isQueryBoundP_fetchTreeWith_of_mem {prf : SeedPrf (OracleComp spec)} (sk : SecretKey)
    {b : Nat} (hb : ∃ t ∈ sk.cache, t.index = b) :
    IsQueryBoundP (fetchTreeWith H prf sk b) p 0 := by
  unfold fetchTreeWith
  split
  · exact isQueryBoundP_pure _ _ 0
  · next hnone =>
    obtain ⟨t, ht, rfl⟩ := hb
    exact absurd (List.find?_eq_none.1 hnone t ht) (by simp)

/-- Signing from any derivations: the bottom search, then at most one tree and the top search.

At most `2^33 + 205 * 2^16 + 407` calls, for any key, when each derivation is one call. -/
theorem isQueryBoundP_signWithTrials (hH : ∀ x, IsQueryBoundP (H x) p 1)
    {prf : SeedPrf (OracleComp spec)} (hprf : ∀ publicParam a suffix, IsQueryBoundP
      (prf publicParam a suffix) p 1)
    (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    IsQueryBoundP (Internal.signWithTrials H prf sk idx msg (hashTrials H)) p
      (2 * MAX_RANDOMIZER_TRIALS + 205 * 2 ^ LAYER_HEIGHT + 407) := by
  unfold Internal.signWithTrials
  simp only [Internal.otsSignTrials_hashTrials]
  refine (isQueryBoundP_bind (isQueryBoundP_otsSign hH hprf _ .bottom _ _)
    fun r _ => ?_).mono (n := 2 ^ 32 + 204 + (2 ^ LAYER_HEIGHT * 205 - 1 + (2 ^ 32 + 204)))
    (by simp [MAX_RANDOMIZER_TRIALS, LAYER_HEIGHT])
  rcases r with _ | ⟨rho, y⟩
  · exact (isQueryBoundP_pure _ _ 0).mono (Nat.zero_le _)
  · refine (isQueryBoundP_bind (m := 0) (isQueryBoundP_fetchTreeWith hH hprf sk _)
      fun r _ => ?_).mono (le_of_eq (Nat.add_zero _))
    obtain ⟨t, sk'⟩ := r
    dsimp only
    cases t.top <;> exact isQueryBoundP_pure _ _ _

/-- Signing: the bottom search, then at most one bottom tree and the top search.

At most `2^33 + 205 * 2^16 + 407` calls, for any key.

It bounds the calls of one signing request, whatever trees the key keeps. -/
theorem isQueryBoundP_signWith (hH : ∀ x, IsQueryBoundP (H x) p 1) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) :
    IsQueryBoundP (signWith H sk idx msg) p
      (2 * MAX_RANDOMIZER_TRIALS + 205 * 2 ^ LAYER_HEIGHT + 407) :=
  isQueryBoundP_signWithTrials hH (isQueryBoundP_seedPrf hH _) sk idx msg

/-- Signing in a bottom tree the key keeps is the bottom search alone: at most `2^32 + 204` calls.

A key that signing returned after a successful bottom search keeps that tree. -/
theorem isQueryBoundP_signWith_of_mem (hH : ∀ x, IsQueryBoundP (H x) p 1) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) (hkept : ∃ t ∈ sk.cache, t.index = bottomTree idx) :
    IsQueryBoundP (signWith H sk idx msg) p (MAX_RANDOMIZER_TRIALS + 204) := by
  unfold signWith Internal.signWithTrials
  simp only [Internal.otsSignTrials_hashTrials]
  refine (isQueryBoundP_bind (m := 0)
    (isQueryBoundP_otsSign hH (isQueryBoundP_seedPrf hH _) _ .bottom _ _) fun r _ => ?_).mono
    (by simp [MAX_RANDOMIZER_TRIALS])
  rcases r with _ | ⟨rho, y⟩
  · exact isQueryBoundP_pure _ _ 0
  · refine (isQueryBoundP_bind (m := 0)
      (isQueryBoundP_fetchTreeWith_of_mem (prf := seedPrf H _) sk hkept)
      fun r _ => ?_).mono le_rfl
    obtain ⟨t, sk'⟩ := r
    dsimp only
    cases t.top <;> exact isQueryBoundP_pure _ _ _

end Bounds

/-! ## The exact count of key generation under fixed answers -/

section Exact

variable {ι : Type} {spec : OracleSpec ι} (f : QueryImpl spec Id)
  (H : Array UInt64 → OracleComp spec Lanes4)
  (hH : ∀ x, (queriesWith f (H x)).length = 1)

include hH

/-- A tweakable hash call is one call of `H`. -/
theorem length_queriesWith_th (publicParam : PublicParam) (address : Address)
    (payload : Array UInt64) :
    (queriesWith f (th H publicParam address payload)).length = 1 := by
  rw [th, queriesWith_bind, List.length_append, hH, queriesWith_pure, List.length_nil]

/-- The starts of a key's chains are `29` derivations from the scheme seed. -/
theorem length_queriesWith_chainStarts (s : Seed) (publicParam : PublicParam) (layer : Layer)
    (e : UInt32) : (queriesWith f (chainStarts publicParam
      (seedPrf H s) layer e)).length = V / 2 := by
  rw [chainStarts, queriesWith_bind, List.length_append,
    length_queriesWith_ofFnInOrder_const f (V / 2) 1, queriesWith_pure, List.length_nil,
    Nat.mul_one, Nat.add_zero]
  exact fun _ => hH _

/-- A key's leaf is `29` derivations, `58 * 3` chain steps and one hash: `204` calls. -/
theorem length_queriesWith_otsPublicLeaf (s : Seed) (publicParam : PublicParam) (layer : Layer)
    (e : UInt32) : (queriesWith f (otsPublicLeaf H publicParam
      (seedPrf H s) layer e)).length = 204 := by
  rw [otsPublicLeaf, queriesWith_bind, List.length_append,
    length_queriesWith_chainStarts f H hH, queriesWith_bind, List.length_append,
    length_queriesWith_ofFnInOrder_const f V (CHAIN_LENGTH - 1), otsLeafHash,
    length_queriesWith_th f H hH]
  · decide
  · exact fun _ => length_queriesWith_chain f _ (fun _ _ => length_queriesWith_th f H hH _ _ _)
      _ _ _ _

/-- A node at `level` is `2^level` leaves and `2^level - 1` hashes: `205 * 2^level - 1` calls. -/
theorem length_queriesWith_xmssNode (s : Seed) (publicParam : PublicParam) (layer : Layer)
    (level j : Nat) :
    (queriesWith f (node H publicParam (seedPrf H s) layer level j)).length = 205 * 2 ^ level - 1 :=
  length_queriesWith_node f _ _ 204 (fun _ _ _ => length_queriesWith_th f H hH _ _ _)
    (fun _ => length_queriesWith_otsPublicLeaf f H hH s publicParam layer _) level j

/-- Key generation makes exactly `1 + 205 * 2^16` calls under fixed answers.

It does not search, so every run makes the same number of calls. -/
theorem length_queriesWith_keyGenWith (seed : Seed) :
    (queriesWith f (keyGenWith H seed)).length = 1 + 205 * 2 ^ LAYER_HEIGHT := by
  have hseed : (queriesWith f (schemeSeed H seed)).length = 1 := hH _
  have hpp : ∀ s, (queriesWith f (publicParamOf (seedPrf H s))).length = 1 := fun s => by
    -- The parameter has the type of a digest, but under another name.
    have h := queriesWith_bind f (seedPrf H s ⟨0, 0⟩ addrParam
      #[]) fun h => (pure (halfOf 0 h) : OracleComp spec PublicParam)
    exact (congrArg List.length h).trans (by rw [List.length_append]; exact congrArg (· + 0) (hH _))
  rw [keyGenWith, queriesWith_bind, List.length_append, hseed, Internal.keyGenFrom,
    queriesWith_bind,
    List.length_append, hpp, queriesWith_bind, List.length_append, build, queriesWith_build,
    ← node, length_queriesWith_xmssNode f H hH, queriesWith_pure, List.length_nil]
  have hpos : 1 ≤ 205 * 2 ^ LAYER_HEIGHT := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

end Exact

end EthLib.Cryptography.Xmss.Cost
