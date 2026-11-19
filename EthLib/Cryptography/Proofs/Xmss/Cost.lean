module

public import EthLib.Cryptography.Proofs.Xmss.QueryBound
public import EthLib.Cryptography.Proofs.HashSig.Calls

/-!
# Proofs: the hash calls of leanXMSS key generation, signing and verification

For the bounds, each call of `H` makes at most one query on every path.

- Key generation takes at most `1 + 205 * 2^16 = 13434881` calls.
- Signing takes at most `2 + 2^33 + 615 * 2^16 - 3 = 8630239231` calls.
- Verification takes at most `384` calls, as the query bounds of the algorithms already prove.

The signing bound charges each of its two randomizer searches all `2^32` trials.

Key generation does not search.

So under fixed answers, when each call of `H` makes exactly one query, it makes `13434881` calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Cost

open OracleSpec OracleComp
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.HashSig (queriesWith queriesWith_bind queriesWith_pure
  length_queriesWith_ofFnInOrder_const length_queriesWith_chain length_queriesWith_node)

/-! ## The constants -/

/-- The bound `1 + 205 * 2^16` of key generation is `13434881`. -/
theorem keyGenCalls_eq : 1 + 205 * 2 ^ LAYER_HEIGHT = 13434881 := by
  decide

/-- The bound `2 + 2^33 + 615 * 2^16 - 3` of signing is `8630239231`. -/
theorem signCalls_eq : 2 + (2 * MAX_RANDOMIZER_TRIALS + 615 * 2 ^ LAYER_HEIGHT - 3) =
    8630239231 := by
  decide

/-! ## Upper bounds on every path -/

section Bounds

variable {ι : Type} {spec : OracleSpec ι} {p : ι → Prop} [DecidablePred p]
  {H : ByteArray → OracleComp spec (Vector UInt8 32)}

/-- The scheme seed is one call of `H`. -/
theorem isQueryBoundP_schemeSeed (hH : ∀ x, IsQueryBoundP (H x) p 1) (seed : Seed) :
    IsQueryBoundP (schemeSeed H seed) p 1 :=
  hH _

/-- A derivation from the scheme seed is one call of `H`. -/
theorem isQueryBoundP_seedPrf (hH : ∀ x, IsQueryBoundP (H x) p 1) (s : Seed) (pp : PublicParam)
    (address : Address) (suffix : ByteArray) :
    IsQueryBoundP (seedPrf H s pp address suffix) p 1 :=
  hH _

/-- Key generation is the scheme seed and the public key: at most `1 + 205 * 2^16` calls.

It bounds the calls of key generation in a security game. -/
theorem isQueryBoundP_keyGenWith (hH : ∀ x, IsQueryBoundP (H x) p 1) (seed : Seed) :
    IsQueryBoundP (keyGenWith H seed) p (1 + 205 * 2 ^ LAYER_HEIGHT) := by
  unfold keyGenWith
  refine isQueryBoundP_bind (isQueryBoundP_schemeSeed hH seed) fun s _ =>
    (isQueryBoundP_bind (m := 0) (isQueryBoundP_publicKeyOf hH (isQueryBoundP_seedPrf hH s))
      fun _ _ => isQueryBoundP_pure _ _ 0).mono ?_
  simp [LAYER_HEIGHT]

/-- Signing is the scheme seed, the parameter and a signature: at most `8630239231` calls.

It bounds the calls of one signing request in a security game. -/
theorem isQueryBoundP_signWith (hH : ∀ x, IsQueryBoundP (H x) p 1) (sk : SecretKey)
    (idx : LeafIndex) (msg : Message) :
    IsQueryBoundP (signWith H sk idx msg) p
      (2 + (2 * MAX_RANDOMIZER_TRIALS + 615 * 2 ^ LAYER_HEIGHT - 3)) := by
  unfold signWith
  refine (isQueryBoundP_bind (isQueryBoundP_schemeSeed hH sk.seed) fun s _ =>
    isQueryBoundP_bind (isQueryBoundP_publicParamOf (isQueryBoundP_seedPrf hH s)) fun pp _ =>
      isQueryBoundP_signDerived hH (isQueryBoundP_seedPrf hH s) pp idx msg).mono ?_
  simp [MAX_RANDOMIZER_TRIALS, LAYER_HEIGHT]

end Bounds

/-! ## The exact count of key generation under fixed answers -/

section Exact

variable {ι : Type} {spec : OracleSpec ι} (f : QueryImpl spec Id)
  (H : ByteArray → OracleComp spec (Vector UInt8 32))
  (hH : ∀ x, (queriesWith f (H x)).length = 1)

include hH

/-- A tweakable hash call is one call of `H`. -/
theorem length_queriesWith_th (pp : PublicParam) (address : Address) (payload : ByteArray) :
    (queriesWith f (th H pp address payload)).length = 1 := by
  rw [th, queriesWith_bind, List.length_append, hH, queriesWith_pure, List.length_nil]

/-- The starts of a key's chains are `29` derivations from the scheme seed. -/
theorem length_queriesWith_chainStarts (s : Seed) (pp : PublicParam) (layer : Layer)
    (e : UInt32) : (queriesWith f (chainStarts pp (seedPrf H s) layer e)).length = V / 2 := by
  rw [chainStarts, queriesWith_bind, List.length_append,
    length_queriesWith_ofFnInOrder_const f (V / 2) 1, queriesWith_pure, List.length_nil,
    Nat.mul_one, Nat.add_zero]
  exact fun _ => hH _

/-- A key's leaf is `29` derivations, `58 * 3` chain steps and one hash: `204` calls. -/
theorem length_queriesWith_otsPublicLeaf (s : Seed) (pp : PublicParam) (layer : Layer)
    (e : UInt32) : (queriesWith f (otsPublicLeaf H pp (seedPrf H s) layer e)).length = 204 := by
  rw [otsPublicLeaf, queriesWith_bind, List.length_append,
    length_queriesWith_chainStarts f H hH, queriesWith_bind, List.length_append,
    length_queriesWith_ofFnInOrder_const f V (CHAIN_LENGTH - 1), otsLeafHash,
    length_queriesWith_th f H hH]
  · decide
  · exact fun _ => length_queriesWith_chain f _ (fun _ _ => length_queriesWith_th f H hH _ _ _)
      _ _ _ _

/-- A node at `level` is `2^level` leaves and `2^level - 1` hashes: `205 * 2^level - 1` calls. -/
theorem length_queriesWith_xmssNode (s : Seed) (pp : PublicParam) (layer : Layer)
    (level j : Nat) :
    (queriesWith f (node H pp (seedPrf H s) layer level j)).length = 205 * 2 ^ level - 1 :=
  length_queriesWith_node f _ _ 204 (fun _ _ _ => length_queriesWith_th f H hH _ _ _)
    (fun _ => length_queriesWith_otsPublicLeaf f H hH s pp layer _) level j

/-- Key generation makes exactly `1 + 205 * 2^16` calls under fixed answers.

It does not search, so every run makes the same number of calls. -/
theorem length_queriesWith_keyGenWith (seed : Seed) :
    (queriesWith f (keyGenWith H seed)).length = 1 + 205 * 2 ^ LAYER_HEIGHT := by
  have hseed : (queriesWith f (schemeSeed H seed)).length = 1 := hH _
  have hpp : ∀ s, (queriesWith f (publicParamOf (seedPrf H s))).length = 1 := fun s => by
    -- The parameter has the type of a digest, but under another name.
    have h := queriesWith_bind f (seedPrf H s (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam
      .empty) fun h => (pure (halfOf 0 h) : OracleComp spec PublicParam)
    exact (congrArg List.length h).trans (by rw [List.length_append]; exact congrArg (· + 0) (hH _))
  rw [keyGenWith, queriesWith_bind, List.length_append, hseed, queriesWith_bind,
    List.length_append, publicKeyOf, queriesWith_bind, List.length_append, hpp,
    queriesWith_bind, List.length_append, length_queriesWith_xmssNode f H hH, queriesWith_pure,
    List.length_nil, queriesWith_pure, List.length_nil]
  have hpos : 1 ≤ 205 * 2 ^ LAYER_HEIGHT := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

end Exact

end EthLib.Cryptography.Xmss.Cost
