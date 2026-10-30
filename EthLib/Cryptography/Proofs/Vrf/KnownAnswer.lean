import EthLib.Cryptography.Proofs.Vrf.Kernel
import EthLib.Cryptography.Proofs.Vrf.Serialization

/-!
# Proofs: VRF tree known answers

Two openings, at the first index and at the last.

- Each secret and sibling is a fixed byte pattern.
- Each root and output was computed outside EthLib, by an independent implementation of this specification.

Each opening is also rejected with a wrong secret, a wrong sibling, and at another index.

The kernel checks every answer, with no `native_decide`.

The answers at each index sit in their own file, so the two build in parallel.
-/

namespace EthLib.Cryptography.Vrf.KnownAnswer

open EthLib.Cryptography.Vrf
open EthLib.Cryptography.Vrf.Constants

/-- An opening whose bytes follow two patterns.

- Byte `k` of the secret is `(sa k + sb) mod 256`.
- Byte `k` of sibling `l` is `(pa l + pb k + pc) mod 256`.
-/
def patternOpening (sa sb pa pb pc : Nat) : Opening where
  secret := Vector.ofFn fun k => UInt8.ofNat (sa * k.val + sb)
  path := Vector.ofFn fun l => Vector.ofFn fun k => UInt8.ofNat (pa * l.val + pb * k.val + pc)

/-- The opening with its first secret byte flipped. -/
def wrongSecret (o : Opening) : Opening :=
  { o with secret := o.secret.set 0 (o.secret[0] ^^^ 1) }

/-- The opening with the last byte of its top sibling flipped. -/
def wrongSibling (o : Opening) : Opening :=
  { o with path := o.path.set 31 (o.path[31].set 31 (o.path[31][31] ^^^ 1)) }

end EthLib.Cryptography.Vrf.KnownAnswer
