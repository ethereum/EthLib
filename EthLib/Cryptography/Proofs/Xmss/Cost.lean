module

public import EthLib.Cryptography.Proofs.Xmss.QueryBound

/-!
# Proofs: the hash calls of leanXMSS key generation, signing and verification

Each call of `H` counts at most 1, on every path, as in the query bounds of the security games.

- Key generation takes at most `1 + 205 * 2^16 = 13434881` calls.
- Signing takes at most `2 + 2^33 + 615 * 2^16 - 3 = 8630239231` calls.
- Verification takes at most `384` calls.

The randomizer search of a one-time signature tries at most `2^32` trials, one call each.

Two searches take `2^33` of the signing calls, and the rest is a fixed amount of work.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Cost

open OracleSpec OracleComp
open EthLib.Cryptography.Xmss.Constants

/-! ## The constants -/

/-- A key's leaf is `29` derivations, `58 * 3` chain steps and one hash: `204` calls. -/
theorem leafCalls_eq : V / 2 + V * (CHAIN_LENGTH - 1) + 1 = 204 := by
  decide

/-- Key generation makes at most `1 + 205 * 2^16 = 13434881` calls. -/
theorem keyGenCalls_eq : 1 + 205 * 2 ^ LAYER_HEIGHT = 13434881 := by
  decide

/-- Signing makes at most `2 + 2^33 + 615 * 2^16 - 3 = 8630239231` calls. -/
theorem signCalls_eq : 2 + (2 * MAX_RANDOMIZER_TRIALS + 615 * 2 ^ LAYER_HEIGHT - 3) =
    8630239231 := by
  decide

/-! ## The algorithms -/

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

/-- The randomizer search of a one-time signature makes at most `2^32` calls. -/
theorem isQueryBoundP_findCodeword_max (hH : ∀ x, IsQueryBoundP (H x) p 1) (pp : PublicParam)
    (layer : Layer) (e : UInt32) (msg : ByteArray) (base : Randomizer) :
    IsQueryBoundP (Internal.findCodeword H pp layer e msg base 0 MAX_RANDOMIZER_TRIALS) p
      MAX_RANDOMIZER_TRIALS :=
  isQueryBoundP_findCodeword hH pp layer e msg base 0 MAX_RANDOMIZER_TRIALS

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

end EthLib.Cryptography.Xmss.Cost
