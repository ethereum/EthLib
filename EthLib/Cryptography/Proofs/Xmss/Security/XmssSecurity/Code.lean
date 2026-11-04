module

public import EthLib.Cryptography.Proofs.Xmss.CodeSize
public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Types

/-!
# The codewords

A digest is a codeword when two conditions hold.

Its top `128 - 2v = 12` bits are zero.

Its first `v = 58` base-4 digits sum to `T = 106`.

Its digits determine it, so codewords and digit words of sum `T` are in bijection.

The model's digit words are the digit strings that the specification counts.

So their number is the size of the code that the specification proves.
-/

@[expose] public section

namespace XmssSecurity.TargetSum

/-- The number of digit words of sum `s`. -/
def codeCount (s : Nat) : Nat := (Finset.univ.filter (fun x : Encoding => sum x = s)).card

/-- `[z^106](1 + z + z^2 + z^3)^58`. -/
theorem codeCount_target : codeCount targetSum = 323504418562481994618807509487594 := by
  -- A digit word of sum `T` is a digit string of sum `T`, which the specification counts.
  rw [codeCount, ← Fintype.card_subtype]
  exact EthLib.Cryptography.Xmss.card_digitStrings_code

end XmssSecurity.TargetSum
