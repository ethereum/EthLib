import EthLib.Cryptography.Vrf.Verify

/-!
# `Vrf.Serialization`

An opening as 1056 bytes, and verification over bytes.

```text
    [ secret: 32 | 32 siblings: 1024 ]
```

The siblings run from the leaf up to the root.
-/

namespace EthLib.Cryptography.Vrf

open EthLib.Cryptography.Vrf.Constants

/-- Encode an opening as 1056 bytes. -/
def encodeOpening (o : Opening) : ByteArray :=
  packBytes o.secret ++ packBytes o.path.flatten

/-- Decode an opening from 1056 bytes.

Length is the only check: every 1056-byte string decodes. -/
def decodeOpening (bytes : ByteArray) : Option Opening :=
  if h : bytes.size = VRF_OPENING_SIZE then
    -- The secret, then sibling `l` at byte `32 + 32 l`.
    some { secret := readBytes bytes 0 VRF_HASH_SIZE (by simp only [h, VRF_OPENING_SIZE]; decide)
           path := Vector.ofFn fun l => readBytes bytes (VRF_HASH_SIZE + VRF_HASH_SIZE * l.val)
             VRF_HASH_SIZE (by
               have := l.isLt
               simp only [h, VRF_OPENING_SIZE, VRF_HASH_SIZE, VRF_TREE_HEIGHT] at *
               omega) }
  else
    none

/-- `vrf_verify(root, index, opening)`: verification over bytes.

Returns nothing for a root that is not 32 bytes, an opening that is not 1056 bytes, or an index outside `[0, 2^32)`. -/
def verifyBytes (root : ByteArray) (index : Nat) (opening : ByteArray) : Option Digest := do
  -- Each check rejects; none pads, truncates or reduces.
  if hr : root.size = VRF_HASH_SIZE then
    if index < 2 ^ VRF_TREE_HEIGHT then
      let o ← decodeOpening opening
      verify (readBytes root 0 VRF_HASH_SIZE (by omega)) (UInt32.ofNat index) o
    else none
  else none

end EthLib.Cryptography.Vrf
