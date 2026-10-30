import EthLib.Cryptography.Xmss.Errors
import EthLib.Cryptography.Xmss.KeyGen

/-!
# `Xmss.Sign`

Signing.

Signing is deterministic: same key, leaf index and message give the same signature.

A leaf index must never sign two different messages.

Their two codewords would reveal every chain at the smaller of their two positions.

Signing is stateless, so tracking spent leaf indices is the caller's job.

Source: the leanXMSS specification draft, section "The scheme", paragraph "Signing".
-/

namespace EthLib.Cryptography.Xmss

open EthLib.Cryptography.Xmss.Constants

variable {m : Type → Type} [Monad m] (H : ByteArray → m (Vector UInt8 32))

/-- One layer's signature by key `e` of a message: the one-time signature and the path.

# Errors

- No randomizer trial gives a codeword, which happens with probability below `exp(-2^11)`. -/
def signLayer (pp : PublicParam) (s : Seed) (layer : Layer) (e : Nat) (msg : ByteArray) :
    m (Except XmssError LayerSignature) := do
  -- No codeword is an error.
  let some (randomizer, chainValues) ← otsSign H pp s layer (UInt32.ofNat e) msg
    | return .error (.noAdmissibleEncoding layer e)
  -- A one-time signature is packed with the key's path.
  return .ok { randomizer, chainValues, path := ← path H pp s layer e }

/-- Sign a message at a leaf index, from the scheme seed `S` and the parameter `P`.

1. The bottom key `idx` signs the message.
2. The root `X^0_{16,b}` of bottom tree `b = floor(idx / 2^16)`, which builds that whole tree.
3. The top key `b` signs that root.

# Errors

- Either layer's one-time signature finds no codeword. -/
def signDerived (s : Seed) (pp : PublicParam) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError Signature) := do
  -- A layer's error ends signing, before any later hash call.
  let bottom ← match ← signLayer H pp s .bottom idx.toNat (packBytes msg) with
    | .ok sig => pure sig
    | .error err => return .error err
  let bottomRoot ← node H pp s .bottom LAYER_HEIGHT (Nat.le_refl _) (bottomTree idx)
  let top ← match ← signLayer H pp s .top (bottomTree idx) (packBytes bottomRoot) with
    | .ok sig => pure sig
    | .error err => return .error err
  return .ok { leafIndex := idx, bottom, top }

/-- `Sig(sk, idx, m)` over a hash `H`: sign a message at a leaf index.

1. The scheme seed `S` and the public parameter `P`, from the secret key's seed.
2. The signature from `S` and `P`.

# Warning

Never sign two different messages at one leaf index with one secret key.

The top key `b` signs only the root of bottom tree `b`.

So it signs one message, however many leaf indices of that tree are used.

# Errors

- Either layer's one-time signature finds no codeword. -/
def signWith (sk : SecretKey) (idx : LeafIndex) (msg : Message) :
    m (Except XmssError Signature) := do
  let s ← schemeSeed H sk.seed
  let pp ← publicParamOf H s
  signDerived H s pp idx msg

/-- `Sig(sk, idx, m)`, with Keccak-256. -/
def sign (sk : SecretKey) (idx : LeafIndex) (msg : Message) : Except XmssError Signature :=
  (signWith hashId sk idx msg).run

end EthLib.Cryptography.Xmss
