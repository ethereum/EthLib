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

/-- One layer's signature by key `e` of a message: the one-time signature and the path.

# Errors

- No randomizer trial gives a codeword, which happens with probability below `exp(-2^11)`. -/
def signLayer (pp : PublicParam) (s : Seed) (layer : Layer) (e : Nat) (msg : ByteArray) :
    Except XmssError LayerSignature :=
  -- No codeword is an error.
  -- A one-time signature is packed with the key's path.
  (otsSign pp s layer (UInt32.ofNat e) msg).elim (.error (.noAdmissibleEncoding layer e))
    fun ots => .ok { randomizer := ots.1, chainValues := ots.2, path := path pp s layer e }

/-- `Sig(sk, idx, m)`: sign a message at a leaf index.

1. The bottom key `idx` signs the message.
2. The top key `b = floor(idx / 2^16)` signs the root of bottom tree `b`.

# Warning

Never sign two different messages at one leaf index with one secret key.

The top key `b` signs only the root of bottom tree `b`.

So it signs one message, however many leaf indices of that tree are used.

# Errors

- Either layer's one-time signature finds no codeword. -/
def sign (sk : SecretKey) (idx : LeafIndex) (msg : Message) : Except XmssError Signature := do
  let s := sk.schemeSeed
  let pp := sk.publicParam
  -- Step 1: the bottom key signs the message, with its path in bottom tree `b`.
  let bottom ← signLayer pp s .bottom idx.toNat (packBytes msg)
  -- Step 2: the root of bottom tree `b`, from the key's leaf and its path.
  -- The path leads to that root, so this costs one leaf and 16 hashes, not a whole tree.
  let leaf := otsPublicLeaf pp s .bottom idx
  let bottomRoot := fold pp .bottom idx.toNat leaf bottom.path
  -- Step 3: the top key `b` signs that root, with its path in the top tree.
  let top ← signLayer pp s .top (bottomTree idx) (packBytes bottomRoot)
  return { leafIndex := idx, bottom, top }

end EthLib.Cryptography.Xmss
