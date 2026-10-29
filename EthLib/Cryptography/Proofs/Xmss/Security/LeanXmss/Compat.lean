module

public import EthLib.Cryptography.Proofs.Xmss.Security.Statement.LeanXmss

/-!
# The hash inputs by name

`Statement/LeanXmss.lean` states the tweakable hash once, for both schemes (`thInput`, `th`,
`thPair`, `taggedSeed`, as `tweak.rs` does). The proofs name the inputs of leanXMSS's calls:
`P || A || payload` at a hash domain's address, the seed derivations' and the randomizer's, the
scheme seed's; and the derivations themselves.
-/

@[expose] public section

namespace LeanXmss

/-- The exact 16 address bytes of a hash domain. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The hash input `P || A || payload` of every tweakable hash call. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) : HashInput :=
  bytesLE 16 parameter ++ tweakBytes domain ++ payload

/-- `"leanXMSS" || S_0`, the 40-byte input of the scheme's seed `S`. -/
def seedHashInput (keySeed : MasterSeed) : HashInput :=
  seedTag ++ bytesLE 32 keySeed

/-- `P || A || S`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  bytesLE 16 parameter ++ fieldBytes (keygenDomainFields domain) ++ bytesLE 32 seed

/-- `P || A_rnd(l, e) || S || M` (`TWEAK_RANDOMIZER = 7`): the randomizer base of a message. -/
def randomizerHashInput (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) : HashInput :=
  thInput parameter (tweakFields 7 0 (layerHi lay 0) key) (bytesLE 32 seed ++ message)

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- `S = H("leanXMSS" || S_0)` (`taggedSeed`). -/
abbrev schemeSeed (keySeed : MasterSeed) : m MasterSeed :=
  Concrete.taggedSeed seedTag keySeed

/-- One seed derivation, first 16 bytes. -/
abbrev deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m Digest :=
  Concrete.th parameter (keygenDomainFields domain) (bytesLE 32 seed)

/-- One seed derivation, all 32 bytes. -/
abbrev deriveOutput (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    m HashOutput :=
  Concrete.thPair parameter (keygenDomainFields domain) (bytesLE 32 seed)

/-- `R0`, the randomizer base of a message, first 16 bytes. -/
abbrev deriveRandomizer (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) : m Randomness :=
  Concrete.th parameter (tweakFields 7 0 (layerHi lay 0) key) (bytesLE 32 seed ++ message)

theorem thInput_hashDomainFields (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) :
    thInput parameter (hashDomainFields domain) payload =
      tweakableHashInput parameter domain payload := rfl

theorem thInput_keygenDomainFields (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    thInput parameter (keygenDomainFields domain) (bytesLE 32 seed) =
      keygenHashInput parameter domain seed := rfl

theorem thInput_randomizer (parameter : PublicParameter) (lay : Layer) (key : KeyIndex)
    (seed : MasterSeed) (message : HashInput) :
    thInput parameter (tweakFields 7 0 (layerHi lay 0) key) (bytesLE 32 seed ++ message) =
      randomizerHashInput parameter lay key seed message := rfl

/-- The signer returned the forgery: some request for its message was answered with its signature.
Any other signature of a signed message is a strong forgery. -/
abbrev SigningTranscript.Contains (log : OracleSpec.QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature

end LeanXmss
