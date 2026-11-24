module

public import EthLib.Cryptography.Xmss.Errors
public import EthLib.Cryptography.Xmss.KeyGen

/-!
# leanXMSS signing

Deterministic signing, with the bottom trees the secret key keeps.

The key tracks no spent leaf index, so preventing reuse is the caller's job.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Signing".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)

namespace Internal

/-- The top key `b`'s signature of a root: the one-time signature and the key's path.

# Errors

- No randomizer trial gives a codeword.
  In the random oracle model, from an empty cache, that has probability below `exp(-4000)`. -/
def signRootWith (prf : SeedPrf m) (sk : SecretKey) (b : Nat) (root : Digest)
    (trials : TrialSource m := hashTrials H) : m (Except XmssError LayerSignature) := do
  -- The secrets come from the given derivations, which signing takes from the key's seed `S`.
  --
  -- No codeword is an error, which every leaf index of the tree then returns.
  let some (randomizer, chainValues) ← otsSignTrials H sk.publicParam prf .top (UInt32.ofNat b)
      root.toArray trials
    | return .error (.noAdmissibleEncoding .top b)
  -- The path is read from the top tree that the key keeps, so it costs no hash call.
  return .ok { randomizer, chainValues, path := sk.top.path LAYER_HEIGHT b }

/-- Build bottom tree `b` from the given derivations, and sign its root with the top key `b`. -/
def cacheTreeWith (prf : SeedPrf m) (sk : SecretKey) (b : Nat)
    (trials : TrialSource m := hashTrials H) : m CachedTree := do
  -- Every node of the tree, from its `2^16` one-time keys.
  let tree ← build H sk.publicParam prf .bottom LAYER_HEIGHT b
  -- The top key `b` signs this one root for all `2^16` leaf indices, so it signs once here.
  --
  -- The top key `b` signs only the root of bottom tree `b`.
  --
  -- So it signs one message, however many leaf indices of that tree are used.
  --
  -- An error is kept with the tree, and every leaf index of the tree returns it.
  let top ← signRootWith H prf sk b tree.value trials
  return { index := b, tree, top }

/-- Bottom tree `b` of a secret key, and the key that keeps it as the one it signed in last. -/
def fetchTreeWith (prf : SeedPrf m) (sk : SecretKey) (b : Nat)
    (trials : TrialSource m := hashTrials H) : m (CachedTree × SecretKey) :=
  match sk.cache.find? (·.index == b) with
  -- A kept tree costs no hash call, and moves to the front.
  | some t => pure (t, { sk with cache := t :: sk.cache.filter (·.index != b) })
  | none => do
    -- Otherwise the tree is built from the given derivations.
    let t ← cacheTreeWith H prf sk b trials
    -- It goes first, and past the limit the tree used longest ago is dropped.
    return (t, { sk with cache := (t :: sk.cache).take MAX_CACHED_BOTTOM_TREES })

/-- `Sig(sk, idx, m)`, with its secrets from the given derivations, and trials from a source.

Signing passes the derivations of the key's seed `S`. -/
def signWithTrials (prf : SeedPrf m) (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (trials : TrialSource m) : m (Except XmssError Signature × SecretKey) := do
  -- Step 1: the bottom key `idx` signs the message.
  -- A failed search ends signing before any tree is built, so the key is unchanged.
  let some (randomizer, chainValues) ← otsSignTrials H sk.publicParam prf .bottom
      (UInt32.ofNat idx.toNat) msg.toArray trials
    | return (.error (.noAdmissibleEncoding .bottom idx.toNat), sk)
  -- Step 2: bottom tree `b = floor(idx / 2^16)`, from the key, or built and kept.
  let (t, sk) ← fetchTreeWith H prf sk (bottomTree idx) trials
  -- The key's path and the root the top key signed both come from the one bottom tree.
  let bottom : LayerSignature :=
    { randomizer, chainValues, path := t.tree.path LAYER_HEIGHT idx.toNat }
  -- Step 3: the top signature kept with the tree; on an error, the key still keeps the tree.
  match t.top with
  | .ok top => return (.ok { leafIndex := idx, bottom, top }, sk)
  | .error err => return (.error err, sk)

end Internal

/-- `Sig(sk, idx, m)` over a hash `H`: a message's signature at a leaf index, and the updated key.

Warning: never sign two different messages at one leaf index with one secret key.

Their two codewords would reveal every chain at the smaller of their two positions.

It fails when either layer's one-time signature finds no codeword. -/
def signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError Signature × SecretKey) :=
  -- A key that key generation and signing give signs as the note's signer does, by a theorem.
  --
  -- The derivations of the key's seed `S`, and each randomizer trial hashed with `H`.
  Internal.signWithTrials H (seedPrf H sk.schemeSeed) sk idx msg (hashTrials H)

/-- `Sig(sk, idx, m)`, with Keccak-256, and the updated key.

Its searches take their trials from Keccak-256's permutation, built once per search.

Those trials give the codewords of hashing each trial, by a theorem. -/
def sign (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    Except XmssError Signature × SecretKey :=
  (Internal.signWithTrials hashId (seedPrf hashId sk.schemeSeed) sk idx msg keccakTrials).run

end EthLib.Cryptography.Xmss
