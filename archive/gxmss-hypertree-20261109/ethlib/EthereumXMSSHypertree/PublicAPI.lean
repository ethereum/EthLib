/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import EthereumXMSSHypertree.Functional
public import EthereumXMSSHypertree.Representation

/-!
# The selected executable public API

These applications specialize deterministic source correspondence to the exact Keccak
implementation used by the selected source. They assert functional equality only.
-/

public section

namespace EthereumXMSSHypertree

open EthLib.Cryptography.Xmss

/-- The source public key generator equals its symbolic pure evaluation. -/
theorem public_keyGen_eq (rawSeed : Seed) : keyGen rawSeed = Pure.keys hash rawSeed :=
  keyGenWith_run hash rawSeed

/-- The source public signer preserves the selected returned-failure observation. -/
theorem public_sign_toOption (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    (sign sk idx msg).toOption = Pure.sign hash sk idx msg :=
  signWith_toOption hash sk idx msg

/-- The source public verifier equals its complete pure Boolean evaluation. -/
theorem public_verify_eq (pk : PublicKey) (msg : Message) (sig : Signature) :
    verify pk msg sig = Pure.verify hash pk msg sig := verifyWith_run hash pk msg sig

/-- Every signature actually returned by the public signer retains its requested source index. -/
theorem public_sign_leafIndex (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    {sig : Signature} (returned : (sign sk idx msg).toOption = some sig) :
    sig.leafIndex = idx := signWith_leafIndex hash sk idx msg returned

end EthereumXMSSHypertree
