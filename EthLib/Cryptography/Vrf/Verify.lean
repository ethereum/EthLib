module

public import EthLib.Cryptography.Vrf.Hash
public import EthLib.Cryptography.Merkle.Tree

/-!
# VRF verification

Verify an opening at an index, and return the output there.

- The leaf is the leaf hash of the secret.
- The opening is valid when its path leads from that leaf to the root.
- The output is then the output hash of the index and the secret.

The output hashes the index and the secret, not the leaf.
-/

@[expose] public section

namespace EthLib.Cryptography.Vrf

/--
Verify an opening at index `i` against a root.

It returns the output at `i`, or nothing if the opening is invalid.
-/
def verify (root : Digest) (i : UInt32) (opening : Opening) : Option Digest :=
  -- The leaf commits to the secret.
  let leaf := leafHash opening.secret
  -- The opening is valid when its path leads from that leaf to the root.
  if (Merkle.climb treeHash 0 i.toNat leaf opening.path.toList).run = root then
    some (outputHash i opening.secret)
  else none

end EthLib.Cryptography.Vrf
