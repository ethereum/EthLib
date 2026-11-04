module

public import EthLib.Cryptography.Vrf.Hash
public import EthLib.Cryptography.Merkle.Tree

/-!
# VRF verification

Verify an opening at an index, and return the output there.

```text
    leaf = leaf(s)
    accept when the path leads from leaf to the root
    output = output(s)
```

The output is a hash of the secret, not the leaf.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

/--
`vrf.Verify(root, i, opening)` of EIP-8450.

It returns the output at index `i`, or nothing if the opening is invalid.
-/
def verify (root : Digest) (i : UInt32) (opening : Opening) : Option Digest :=
  -- The leaf commits to the secret.
  let leaf := leafHash opening.secret
  -- The opening is valid when its path leads from that leaf to the root.
  if (Merkle.climb treeHash 0 i.toNat leaf opening.path.toList).run = root then
    some (outputHash opening.secret)
  else none

end EthLib.Cryptography.Vrf
