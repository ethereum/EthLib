module

public import EthLib.Cryptography.Xmss.KeyGen
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash

/-!
# Proofs: leanXMSS key generation

With the derivations from the scheme seed `S`, the public parameter is the hash the note defines.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

/-- With the derivations from `S`, the public parameter is `Th(0^128, A_param, S)`. -/
theorem publicParamOf_seedPrf {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)
    (s : Seed) :
    publicParamOf (seedPrf H s) =
      th H ⟨0, 0⟩ CallSite.param s.toArray := by
  rw [publicParamOf, seedPrf_empty]
  rfl

end EthLib.Cryptography.Xmss
