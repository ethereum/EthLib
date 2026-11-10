module

public import EthLib.Consensus.Proofs.LightClient.Authenticate
public import EthLib.Cryptography.Proofs.Bls.Security.PopByteGame

/-!
# Proofs: a light client rarely accepts a forged signature, when every signer proves possession

The theorems on what an update authenticates assume that an accepted aggregate was signed.

No signature scheme gives that with certainty, so this module bounds a game instead.

The bound is not a proof of that assumption, which stays a hypothesis of those theorems.

One member of the committee is honest, and the game protects that one member only.

The forger knows the honest key and its proof of possession, and asks for signatures under it.

It chooses everything else: the configuration, the store, the update and the clock.

Each member whose bit is set must carry a valid proof of possession, §3.3.3 of the BLS draft.

<https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-bls-signature-04#section-3.3>

Ethereum registers keys with deposit signatures instead, so the bound does not cover its keys.

The forger wins if the light client accepts the update with the honest member's bit set.

The honest member must never have signed the signing root of the update.

Both hashes to `G2` are random oracles.

The light client checks the aggregate against the message hash.

The game checks each proof against the key hash.

The game is the byte game of aggregates with the update read as an aggregate forgery.

So it wins at most `q` times as often as a co-CDH solver built from it, plus `(q + qK - 1) / r`.

Here `r` is the order of the groups, and co-CDH is the variant that the aggregate game uses.

This needs `qK` at most `r`.

It is small when co-CDH is hard, if the solver runs in about the forger's time, which is not proved.
-/

@[expose] public section

namespace EthLib.Consensus.LightClientForgery

open OracleComp ENNReal Base
open EthLib.Cryptography.Bls EthLib.Cryptography.Bls.Security
open scoped Classical

variable {preset : Preset} {fork : Fork}

/-- The output of a forger: the inputs of the light client's check, and the proofs of possession.

The proofs are those of the members whose bit is set, in committee order. -/
structure Forgery (preset : Preset) (fork : Fork) where
  /-- The configuration of the chain. -/
  config : Config
  /-- The store of the light client. -/
  store : LightClientStore preset fork
  /-- The update that the light client checks. -/
  update : LightClientUpdate preset fork
  /-- The slot of the light client's clock. -/
  currentSlot : Slot
  /-- The root of the genesis validators. -/
  genesisValidatorsRoot : Root
  /-- A proof of possession for each signer. -/
  proofs : List ByteArray

/-- A forger against the light client.

It receives the encoded honest key and its proof, and has the oracles of the aggregate game. -/
structure Adversary (preset : Preset) (fork : Fork) where
  /-- The forger's run. -/
  main : ByteArray → ByteArray →
    OracleComp (Pop.Spec ByteArray ByteArray ByteArray) (Forgery preset fork)

/-- The keys of the members whose bit is set, as bytes. -/
def Forgery.signers (f : Forgery preset fork) : List ByteArray :=
  ((f.store.signatureCommittee f.update).participantKeys f.update.syncAggregate).toList.map
    packBytes

/-- The message that the signers sign: the signing root of the update, as bytes.

If the root cannot be computed, the light client rejects the update, and it is empty. -/
def Forgery.message (f : Forgery preset fork) : ByteArray :=
  match syncCommitteeSigningRoot f.config f.update f.genesisValidatorsRoot with
  | .ok root => packBytes root
  | .error _ => .empty

/-- The forgery read as an aggregate forgery: signers with proofs, the message, the signature. -/
def Forgery.toAggregate (f : Forgery preset fork) :
    List (ByteArray × ByteArray) × ByteArray × ByteArray :=
  (f.signers.zip f.proofs, f.message, packBytes f.update.syncAggregate.syncCommitteeSignature)

/-- The checks of the light client, with the oracle's hash `h` of the message `msg`.

The aggregate check runs fast aggregate verification against `h`, on `msg` only.

The light client never checks a single signature, so that check rejects. -/
noncomputable def oracleChecks (msg : ByteArray) (h : G2Sub) : SignatureChecks where
  verify _ _ _ := false
  fastAggregateVerify keys m sig := decide (m = msg) && byteFastAggregateVerify keys sig h

/-- With the hash to `G2` of the message, the aggregate check is the light client's. -/
theorem oracleChecks_hashPoint (msg : ByteArray) (keys : Array ByteArray) (sig : ByteArray) :
    (oracleChecks msg (hashPoint msg)).fastAggregateVerify keys msg sig =
      SignatureChecks.bls.fastAggregateVerify keys msg sig := by
  simp only [oracleChecks, decide_true, Bool.true_and, SignatureChecks.bls,
    byteFastAggregateVerify_hashPoint]

/-- With the hash to `G2` of the signing root, the game's check of an update is the real one.

The real one is the light client's check with the checks of the BLS signature scheme. -/
theorem validateLightClientUpdate_oracleChecks {config : Config}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root} {root : Root}
    (rooted : syncCommitteeSigningRoot config update genesisValidatorsRoot = .ok root) :
    validateLightClientUpdate config (oracleChecks (packBytes root) (hashPoint (packBytes root)))
        store update currentSlot genesisValidatorsRoot =
      validateLightClientUpdate config SignatureChecks.bls store update currentSlot
        genesisValidatorsRoot := by
  unfold validateLightClientUpdate
  have rooted' : syncCommitteeSigningRoot config update genesisValidatorsRoot = pure root := rooted
  simp only [rooted', pure_bind, oracleChecks_hashPoint]

/-- Whether a forgery wins against the honest key `pk`, given the hashes of verification.

The light client accepts the update, with the oracle's hash `h` of the signing root.

The honest key is among the signers, and the signing oracle never signed the signing root.

There is one proof per signer, and each passes the proof check on its key hash. -/
noncomputable def wins (pk : G1Sub) (signed : List ByteArray) (f : Forgery preset fork)
    (h : G2Sub) (hs : List G2Sub) : Bool :=
  decide (validateLightClientUpdate f.config (oracleChecks f.message h) f.store f.update
      f.currentSlot f.genesisValidatorsRoot = .ok ()) &&
    decide (G1Sub.encode pk ∈ f.signers) && decide (f.message ∉ signed) &&
    decide (f.proofs.length = f.signers.length) && decide (hs.length = f.signers.length) &&
    ((f.signers.zip f.proofs).zip hs).all fun (k, h') => byteVerify k.1 k.2 h'

/-- The game for the secret scalar `a`, as the byte game of aggregates runs it.

After the forger's run, verification hashes the signing root and each decoded signer. -/
noncomputable def experimentAt (adversary : Adversary preset fork) (a : Scalar) :
    ProbComp (Bool × Pop.State Scalar G1Sub ByteArray) :=
  (fun z => (wins (a • g1) z.2.msg.signed z.1.1 z.1.2.1 z.1.2.2, z.2)) <$>
    Pop.runAt adversary.main Forgery.toAggregate a

/-- The game draws the secret scalar uniformly.

It includes the scalar 0, which is not an EthLib secret key. -/
noncomputable def experiment (adversary : Adversary preset fork) :
    ProbComp (Bool × Pop.State Scalar G1Sub ByteArray) := do
  let a ← $ᵗ Scalar
  experimentAt adversary a

/-- The probability that the light client accepts a forged signature of the honest member. -/
noncomputable def forgeAdvantage (adversary : Adversary preset fork) : ℝ≥0∞ :=
  Pr{let z ← experiment adversary}[z.1 = true]

/-- Every run makes at most `q` message hash calls and `qK` key hash calls.

The counts are those of the byte game of aggregates.

The key count includes one hash per signer at verification. -/
def HashCallBound (adversary : Adversary preset fork) (q qK : ℕ) : Prop :=
  ∀ z ∈ support (experiment adversary), z.2.msg.calls ≤ q ∧ z.2.keyCalls ≤ qK

/-- The forger read as a forger of aggregates. -/
def Adversary.toAggregate (adversary : Adversary preset fork) : Pop.ByteAdversary where
  main pk proof := Forgery.toAggregate <$> adversary.main pk proof

/-! ## The bound -/

/-- A winning forgery is a winning aggregate forgery, on the same hashes. -/
theorem byteWins_of_wins {pk : G1Sub} {signed : List ByteArray} {f : Forgery preset fork}
    {h : G2Sub} {hs : List G2Sub} (hw : wins pk signed f h hs = true) :
    Pop.byteWins pk signed f.toAggregate h hs = true := by
  simp only [wins, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨hv, hpk⟩, hm⟩, hlen⟩, hlen'⟩, hall⟩ := hw
  obtain ⟨_, _, _, _, r, hr, hfa⟩ := validateLightClientUpdate_proves hv
  have hmsg : f.message = packBytes r := by simp only [Forgery.message, hr]
  rw [← hmsg] at hfa
  simp only [oracleChecks, decide_true, Bool.true_and] at hfa
  have hz : (f.signers.zip f.proofs).map Prod.fst = f.signers := List.map_fst_zip hlen.ge
  have hz' : (f.signers.zip f.proofs).length = f.signers.length := by
    simp only [List.length_zip, hlen, Nat.min_self]
  simp only [Pop.byteWins, Forgery.toAggregate, hz, Bool.and_eq_true, decide_eq_true_eq]
  have hsig : f.signers.toArray = Array.map packBytes
      ((f.store.signatureCommittee f.update).participantKeys f.update.syncAggregate) := by
    rw [Forgery.signers, ← Array.toList_map, Array.toArray_toList]
  rw [hsig]
  simp only [hz', decide_eq_true_eq]
  exact ⟨⟨⟨⟨hpk, decide_eq_true hm⟩, hlen'⟩, hall⟩, hfa⟩

/-- A forger wins at most as often as its reading as a forger of aggregates. -/
theorem forgeAdvantage_le_byteForgeAdvantage (adversary : Adversary preset fork) :
    forgeAdvantage adversary ≤ Pop.byteForgeAdvantage adversary.toAggregate :=
  Pop.prEvent_runAt_le adversary.main Forgery.toAggregate wins byteWins_of_wins

/-- The game ends in the same states as the byte game of the forger read as an aggregate forger. -/
theorem snd_map_experiment (adversary : Adversary preset fork) :
    Prod.snd <$> experiment adversary = Prod.snd <$> Pop.byteExperiment adversary.toAggregate :=
  Pop.snd_map_runAt adversary.main Forgery.toAggregate wins

/-- A forger has a hash-call bound exactly when its reading as an aggregate forger has it. -/
theorem hashCallBound_iff (adversary : Adversary preset fork) (q qK : ℕ) :
    HashCallBound adversary q qK ↔ Pop.ByteHashCallBound adversary.toAggregate q qK :=
  forall_mem_support_snd_iff (snd_map_experiment adversary)
    fun s => s.msg.calls ≤ q ∧ s.keyCalls ≤ qK

/-- **A light client rarely accepts a forged signature, when every signer proves possession.**

This holds in the random oracle model, when every signer carries a proof of possession.

The forger makes at most `q` message hash calls and `qK` key hash calls, with `qK` at most `r`.

Its advantage is at most `q` times that of a co-CDH solver built from it, plus `(q + qK - 1) / r`.

Ethereum keys carry deposit signatures, not these proofs, so this does not cover them. -/
theorem forgeAdvantage_le (adversary : Adversary preset fork) {q qK : ℕ} (hq0 : 0 < q)
    (hchar : qK ≤ Fr.modulus) (hq : HashCallBound adversary q qK) :
    forgeAdvantage adversary ≤
      q * coCdhAdvantage Scalar g1 g2
          (Pop.reduction (F := Scalar) g2 adversary.toAggregate.toGroup q) +
        ((q + qK - 1 : ℕ) : ℝ≥0∞) * (Fr.modulus : ℝ≥0∞)⁻¹ :=
  (forgeAdvantage_le_byteForgeAdvantage adversary).trans
    (Pop.byteForgeAdvantage_le_coCdhAdvantage adversary.toAggregate hq0 hchar
      ((hashCallBound_iff adversary q qK).mp hq))

end EthLib.Consensus.LightClientForgery
