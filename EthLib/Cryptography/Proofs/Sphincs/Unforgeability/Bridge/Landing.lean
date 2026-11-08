module

public import EthLib.Cryptography.Proofs.Sphincs.Unforgeability.Bridge.Bytes

/-!
# Proofs: in EthLib's configuration every index lands

The model's signer tests the randomizers `R0, R0 + delta` and onwards.

Each test checks that the low 26 bits of the first digest call land in the kept subtree.

EthLib's key is layered, so the kept subtree is the whole key and every value lands.

So the model's walk stops at `R0` after one test call, and signs with the randomizer EthLib uses.
-/

@[expose] public section

namespace EthLib.Cryptography.Sphincs.Unforgeability.Bridge

open SphincsSecurity SphincsSecurity.Concrete

/-- Every index lands, whatever `PK.seed` is. -/
theorem landed (parameter : PublicParameter) (index : Index) : Landed parameter index := by
  have hi : index.val < 2 ^ 26 := index.isLt
  change index.val / 2 ^ 26 = parameter.toNat % 2 ^ (26 - 26)
  rw [Nat.div_eq_of_lt hi, Nat.sub_self, pow_zero, Nat.mod_one]

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasQuery HashSpec m]

/-- A signing attempt always succeeds, with the index of the first digest call. -/
theorem signAttempt_eq (secretKey : Seeded.SecretKey) (message : SphincsSecurity.Message)
    (randomness : Randomness) :
    Seeded.signAttempt (m := m) secretKey message randomness =
      (fun first => some (blockIndex first)) <$>
        messageDigestCall secretKey.parameter secretKey.root message randomness firstCall := by
  simp only [Seeded.signAttempt, landed, ↓reduceIte]
  rw [map_eq_bind_pure_comp]
  rfl

/-- The randomizer walk stops at its first randomizer, after one digest call. -/
theorem signDigestLoop_succ (secretKey : Seeded.SecretKey) (message : SphincsSecurity.Message)
    (step randomness : Randomness) (attempts : Nat) :
    Seeded.signDigestLoop (m := m) secretKey message step (attempts + 1) randomness =
      (fun first => some (randomness, blockIndex first)) <$>
        messageDigestCall secretKey.parameter secretKey.root message randomness firstCall := by
  rw [Seeded.signDigestLoop, signAttempt_eq, bind_map_left, map_eq_bind_pure_comp]
  rfl

end EthLib.Cryptography.Sphincs.Unforgeability.Bridge
