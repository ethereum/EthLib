import EthLib.Cryptography.Vrf.Hash
import EthLib.Cryptography.Vrf.Tree

/-!
# `Vrf.Verify`

Verify an opening at an index, and return the output there.

```text
    leaf = leaf(s)
    accept when the path leads from leaf to the root
    output = output(s)
```

The output is a hash of the secret, not the leaf.
-/

namespace EthLib.Cryptography.Vrf

/-- `vrf.Verify(root, i, opening)`: the output at index `i`, or nothing if the opening is invalid. -/
def verify (root : Digest) (i : UInt32) (opening : Opening) : Option Digest :=
  -- The leaf commits to the secret.
  let leaf := leafHash opening.secret
  -- The opening is valid when its path leads from that leaf to the root.
  if Tree.climb nodeHash i.toNat leaf opening.path.toList = root then
    some (outputHash opening.secret)
  else none

end EthLib.Cryptography.Vrf
