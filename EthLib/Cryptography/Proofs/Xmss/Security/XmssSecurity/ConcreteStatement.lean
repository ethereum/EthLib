module

public import EthLib.Cryptography.Proofs.Xmss.Security.XmssSecurity.Translate
public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Xmss.Verify
public import EthLib.Cryptography.Proofs.SufCma

/-!
# Proofs: leanXMSS in the strong-unforgeability game

Source: the leanXMSS specification draft, section "Security".

The scheme runs EthLib's own key generation, signing and verification.

Their `H` is a query to the hash oracle, and key generation samples the seed `S_0` uniformly.

A request names a leaf index and a message.

The rule of use is that no leaf index is requested twice.
-/
@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability

open OracleComp OracleSpec ENNReal
open EthLib.Cryptography.Xmss

/-- `H` in the game: a query to the random oracle. -/
abbrev H : Array UInt64 → OracleComp XmssSecurity.HashSpec Lanes4 := queryH

/-- A signing request: a leaf index and a message. -/
structure SignRequest where
  leafIndex : LeafIndex
  message : Message
  deriving DecidableEq

/-- A claimed forgery: a message and a signature, which carries its leaf index. -/
abbrev Forgery := SufCma.Forgery Message Signature

/-- The signing oracle answers a request with a signature, or nothing when signing fails. -/
abbrev SigningSpec := SufCma.SigningSpec SignRequest Signature

/-- An adaptive adversary.

From the public key, it samples coins, queries `H`, requests signatures, and returns a forgery. -/
abbrev Adversary := SufCma.Adversary XmssSecurity.HashSpec SignRequest Message PublicKey Signature

/-- A query of the adversary that is a hash call, neither a coin nor a request. -/
abbrev IsAdversaryHash := SufCma.IsAdversaryHash XmssSecurity.HashSpec SignRequest Signature

/-- A query of the adversary that is a signing request. -/
abbrev IsAdversaryRequest := SufCma.IsAdversaryRequest XmssSecurity.HashSpec SignRequest Signature

/-- No leaf index was requested twice.

It counts every request, answered or not. -/
def Valid (log : QueryLog SigningSpec) : Prop :=
  (log.map fun entry => entry.1.leafIndex).Nodup

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (List.Nodup _))

/-- A uniform seed `S_0`: the lanes of a uniform 256-bit vector, converted one to one. -/
noncomputable def sampleSeed : ProbComp Seed :=
  ofSeed <$> XmssSecurity.sampleMasterSeed

/-- leanXMSS as EthLib computes it, with `H` the hash oracle.

Key generation samples `S_0` uniformly.

The signer keeps its key across requests, as a real signer does.

Its rule of use is that no leaf index is requested twice. -/
noncomputable def scheme :
    SufCma.Scheme XmssSecurity.HashSpec SignRequest Message PublicKey SecretKey Signature where
  keyGen := liftM sampleSeed >>= fun seed => liftM (keyGenWith H seed)
  sign sk request := (fun result => (result.1.toOption, result.2)) <$>
    liftM (signWith H sk request.leafIndex request.message)
  verify pk message signature := liftM (verifyWith H pk message signature)
  message := SignRequest.message
  Admissible := Valid
  decidableAdmissible := inferInstance
  admissible_singleton _ := List.nodup_singleton _
  admissible_of_append_left log log' h := by
    unfold Valid at h ⊢
    rw [List.map_append] at h
    exact h.of_append_left
  admissible_congr log log' h := by
    -- The leaf indices are read off the requests alone.
    have hidx : (log.map fun entry => entry.1.leafIndex) =
        log'.map fun entry => entry.1.leafIndex := by
      simpa [List.map_map, Function.comp_def] using congrArg (List.map SignRequest.leafIndex) h
    unfold Valid
    rw [hidx]

/-- The scheme's rule of use is that no leaf index is requested twice. -/
theorem scheme_admissible (log : QueryLog SigningSpec) : scheme.Admissible log ↔ Valid log :=
  Iff.rfl

/-- A request asks to sign its message. -/
theorem scheme_message (request : SignRequest) : scheme.message request = request.message :=
  rfl

/-- The game samples `S_0`, generates the keys, then runs the adversary and checks its forgery. -/
theorem game_eq (adversary : Adversary) :
    SufCma.game scheme adversary =
      liftM sampleSeed >>= fun seed => liftM (keyGenWith H seed) >>= fun keys =>
        SufCma.gameAfterKeys scheme adversary keys.1 keys.2 :=
  bind_assoc _ _ _

end EthLib.Cryptography.Xmss.Unforgeability
