module

public import EthLib.Cryptography.Xmss.Errors
public import EthLib.Cryptography.Xmss.KeyGen

/-!
# leanXMSS signing

Signing.

Signing is deterministic: same key, leaf index and message give the same signature.

A leaf index must never sign two different messages.

Their two codewords would reveal every chain at the smaller of their two positions.

The key tracks no spent leaf index, so preventing reuse is the caller's job.

A signature at leaf index `idx` needs bottom tree `b = floor(idx / 2^16)` and the top tree.

The top key `b` signs the same root, the root of bottom tree `b`, at all `2^16` of its indices.

So the key keeps that top signature with the tree.

A signature in a kept tree then hashes for one one-time signature only.

The key that signing returns keeps the tree, and signing with it gives the same bytes.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Signing".
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : Array UInt64 → m Lanes4)

namespace Internal

/-- The top key `b`'s signature of a root: the one-time signature and the key's path.

The path is read from the top tree, so only the search and the chains hash.

# Errors

- No randomizer trial gives a codeword.
  In the random oracle model, from an empty cache, that has probability below `exp(-4000)`. -/
def signRootWith (sk : SecretKey) (b : Nat) (root : Digest)
    (trials : TrialSource m := hashTrials H) : m (Except XmssError LayerSignature) := do
  -- No codeword is an error, which every leaf index of the tree then returns.
  let some (randomizer, chainValues) ← otsSignTrials H sk.publicParam (seedPrf H sk.schemeSeed)
      .top (UInt32.ofNat b) root.toArray trials
    | return .error (.noAdmissibleEncoding .top b)
  return .ok { randomizer, chainValues, path := sk.top.path LAYER_HEIGHT b }

/-- Build bottom tree `b` of a secret key, and sign its root with the top key `b`.

The top layer's error, if any, is kept with the tree. -/
def cacheTreeWith (sk : SecretKey) (b : Nat) (trials : TrialSource m := hashTrials H) :
    m CachedTree := do
  let tree ← build H sk.publicParam (seedPrf H sk.schemeSeed) .bottom LAYER_HEIGHT b
  let top ← signRootWith H sk b tree.value trials
  return { index := b, tree, top }

/-- Bottom tree `b` of a secret key, and the key that keeps it as the one it signed in last.

A kept tree is read without a hash call.

Otherwise the tree is built and put first.

Past the limit, the tree used longest ago is dropped. -/
def fetchTreeWith (sk : SecretKey) (b : Nat) (trials : TrialSource m := hashTrials H) :
    m (CachedTree × SecretKey) :=
  match sk.cache.find? (·.index == b) with
  | some t => pure (t, { sk with cache := t :: sk.cache.filter (·.index != b) })
  | none => do
    let t ← cacheTreeWith H sk b trials
    return (t, { sk with cache := (t :: sk.cache).take MAX_CACHED_BOTTOM_TREES })

/-- `Sig(sk, idx, m)`, with the trials of its searches taken from a source. -/
def signWithTrials (sk : SecretKey) (idx : LeafIndex) (msg : Message)
    (trials : TrialSource m) : m (Except XmssError Signature × SecretKey) := do
  -- A failed search ends signing, before any tree is built.
  let some (randomizer, chainValues) ← otsSignTrials H sk.publicParam (seedPrf H sk.schemeSeed)
      .bottom (UInt32.ofNat idx.toNat) msg.toArray trials
    | return (.error (.noAdmissibleEncoding .bottom idx.toNat), sk)
  let (t, sk) ← fetchTreeWith H sk (bottomTree idx) trials
  -- The key's path and the root the top key signed both come from the one bottom tree.
  let bottom : LayerSignature :=
    { randomizer, chainValues, path := t.tree.path LAYER_HEIGHT idx.toNat }
  match t.top with
  | .ok top => return (.ok { leafIndex := idx, bottom, top }, sk)
  | .error err => return (.error err, sk)

end Internal

/-- `Sig(sk, idx, m)` over a hash `H`: sign a message at a leaf index.

It returns the signature and the updated key.

1. The bottom key `idx` signs the message.
2. Bottom tree `b = floor(idx / 2^16)` gives the key's path, and its top signature.
   The tree comes from the key, or is built and kept.

When the bottom search succeeds, the updated key keeps tree `b`.

A failed bottom search returns the key unchanged.

A key that key generation and signing give signs as the note's stateless signer, by a theorem.

# Warning

Never sign two different messages at one leaf index with one secret key.

The top key `b` signs only the root of bottom tree `b`.

So it signs one message, however many leaf indices of that tree are used.

Each trial of a randomizer search hashes its input with `H`.

# Errors

- Either layer's one-time signature finds no codeword. -/
def signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError Signature × SecretKey) :=
  Internal.signWithTrials H sk idx msg (hashTrials H)

/-- `Sig(sk, idx, m)`, with Keccak-256, and the updated key.

Its searches take their trials from Keccak-256's permutation, built once per search.

Those trials give the codewords of hashing each trial, by a theorem. -/
def sign (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    Except XmssError Signature × SecretKey :=
  (Internal.signWithTrials hashId sk idx msg keccakTrials).run

end EthLib.Cryptography.Xmss
