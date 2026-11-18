module

public import EthLib.Cryptography.Proofs.Xmss.QueryBound
public import EthLib.Cryptography.Proofs.HashSig.Calls

/-!
# Proofs: the hash calls of leanXMSS key generation, signing and verification

Each call of `H` counts at most 1, on every path, as in the query bounds of the security games.

- Key generation takes at most `1 + 205 * 2^16 = 13434881` calls.
- Signing takes at most `2 + 2^33 + 615 * 2^16 - 3 = 8630239231` calls.
- Verification takes at most `384` calls, by the query bounds of the algorithms' parts.

The two randomizer searches of signing take at most `2^32` calls each.

Key generation does not search, so under fixed answers it makes exactly `13434881` calls.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Cost

open OracleSpec OracleComp
open EthLib.Cryptography.Xmss.Constants
open EthLib.Cryptography.HashSig (length_log_bind length_log_ofFnInOrder length_log_chain
  length_log_node log_pure)

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
  (hH : ∀ x, ((simulateQ f.withLogging (H x)).run).2.length = 1)

include hH

/-- A tweakable hash call is one call of `H`. -/
theorem length_log_th (pp : PublicParam) (address : Address) (payload : ByteArray) :
    ((simulateQ f.withLogging (th H pp address payload)).run).2.length = 1 := by
  rw [th, length_log_bind, hH, log_pure, List.length_nil]

/-- The starts of a key's chains are `29` derivations from the scheme seed. -/
theorem length_log_chainStarts (s : Seed) (pp : PublicParam) (layer : Layer) (e : UInt32) :
    ((simulateQ f.withLogging (chainStarts pp (seedPrf H s) layer e)).run).2.length = V / 2 := by
  rw [chainStarts, length_log_bind, length_log_ofFnInOrder f 1 (V / 2), log_pure,
    List.length_nil, Nat.mul_one, Nat.add_zero]
  exact fun _ => hH _

/-- A key's leaf is `29` derivations, `58 * 3` chain steps and one hash: `204` calls. -/
theorem length_log_otsPublicLeaf (s : Seed) (pp : PublicParam) (layer : Layer) (e : UInt32) :
    ((simulateQ f.withLogging (otsPublicLeaf H pp (seedPrf H s) layer e)).run).2.length =
      204 := by
  rw [otsPublicLeaf, length_log_bind, length_log_chainStarts f H hH, length_log_bind,
    length_log_ofFnInOrder f (CHAIN_LENGTH - 1) V, otsLeafHash, length_log_th f H hH]
  · decide
  · exact fun _ => length_log_chain f _ (fun _ _ => length_log_th f H hH _ _ _) _ _ _ _

/-- A node at `level` is `2^level` leaves and `2^level - 1` hashes: `205 * 2^level - 1` calls. -/
theorem length_log_node (s : Seed) (pp : PublicParam) (layer : Layer) (level j : Nat) :
    ((simulateQ f.withLogging (node H pp (seedPrf H s) layer level j)).run).2.length =
      205 * 2 ^ level - 1 :=
  HashSig.length_log_node f _ _ 204 (fun _ _ _ => length_log_th f H hH _ _ _)
    (fun _ => length_log_otsPublicLeaf f H hH s pp layer _) level j

/-- Key generation makes exactly `1 + 205 * 2^16` calls under fixed answers.

It does not search, so every run makes the same number of calls. -/
theorem length_log_keyGenWith (seed : Seed) :
    ((simulateQ f.withLogging (keyGenWith H seed)).run).2.length =
      1 + 205 * 2 ^ LAYER_HEIGHT := by
  have hseed : ((simulateQ f.withLogging (schemeSeed H seed)).run).2.length = 1 := hH _
  have hpp : ∀ s, ((simulateQ f.withLogging (publicParamOf (seedPrf H s))).run).2.length = 1 :=
    -- The parameter has the type of a digest, but under another name.
    fun s => (length_log_bind f (seedPrf H s (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam
      .empty) fun h => (pure (halfOf 0 h) : OracleComp spec PublicParam)).trans
        (congrArg (· + 0) (hH _))
  rw [keyGenWith, length_log_bind, hseed, length_log_bind, publicKeyOf, length_log_bind, hpp,
    length_log_bind, length_log_node f H hH, log_pure, List.length_nil, log_pure,
    List.length_nil]
  have hpos : 1 ≤ 205 * 2 ^ LAYER_HEIGHT := Nat.one_le_iff_ne_zero.2 (by positivity)
  omega

end Exact

end EthLib.Cryptography.Xmss.Cost
