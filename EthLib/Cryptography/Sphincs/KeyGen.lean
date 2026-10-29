import EthLib.Cryptography.Sphincs.Verify

/-!
# `Sphincs.KeyGen`

Key generation.

The secret key is a 32-byte seed `S`, nothing more.

Every secret derives from it, so the seed alone regenerates every chain, every FORS secret and the public key.

The seed is used as it is, with no hash of the configuration before it.

So one seed must never serve two configurations: their one-time keys would coincide.

Source: `keygenFromSeed` in [FORS/Scheme.lean](https://github.com/TomWambsgans/sphincs.art/blob/1538d0a97845c3b771088f09561ddf7607b560a1/formal/sphincs/FORS/Scheme.lean).
-/

namespace EthLib.Cryptography.Sphincs

open EthLib.Cryptography.Sphincs.Constants

/-- `P = Th(0^128, A_param, S)`: the public parameter.

The all-zero parameter stands in for the one being derived. -/
def publicParamOf (seed : Seed) : PublicParam :=
  th (Vector.replicate PUBLIC_PARAM_LEN 0) addrParam (packBytes seed)

/-- A secret key: the seed `S`. -/
structure SecretKey where
  /-- The 32 uniform bytes every secret derives from. -/
  seed : Seed

/-- The secret key's public parameter `P`. -/
def SecretKey.publicParam (sk : SecretKey) : PublicParam :=
  publicParamOf sk.seed

/-- The public key: the root of the top tree, with the public parameter.

Computing it builds the whole top tree: `2^10` one-time keys. -/
def SecretKey.publicKey (sk : SecretKey) : PublicKey where
  root := treeRoot sk.publicParam sk.seed .top 0
  publicParam := sk.publicParam

/-- `Gen`: the key pair grown from a seed.

The seed must be 32 uniform bytes, kept secret. -/
def keyGen (seed : Seed) : SecretKey × PublicKey :=
  let sk : SecretKey := ⟨seed⟩
  (sk, sk.publicKey)

end EthLib.Cryptography.Sphincs
