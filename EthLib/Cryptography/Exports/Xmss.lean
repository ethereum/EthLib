import EthLib.Cryptography.Xmss.Constants
import EthLib.Cryptography.Xmss.Errors
import EthLib.Cryptography.Xmss.KeyGen
import EthLib.Cryptography.Xmss.Sign
import EthLib.Cryptography.Xmss.Serialization

/-!
# `Exports.Xmss`

C-ABI exports for leanXMSS, callable from the Python C extension.

Only key generation, signing and verification cross the boundary, with the sizes.
The scheme is a black box to callers: no hash, chain or tree is exported.
-/

namespace EthLib.Cryptography.Xmss.Exports

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- Run a fallible leanXMSS computation down to `IO`.

The C-ABI layer surfaces failures to Python as exceptions. -/
def runXmss {α : Type} (act : Except XmssError α) : IO α :=
  match act with
  -- Success passes straight through.
  | .ok a    => pure a
  -- Failure becomes the user error the Python bindings expect.
  | .error e => throw (IO.userError e.message)

/-! ## Sizes

The Python C extension reads every size through these at module-init time, so the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_xmss_const_digest_len]
def constDigestLen (_ : Unit) : UInt64 :=
  UInt64.ofNat DIGEST_LEN

@[export eth_xmss_const_public_param_len]
def constPublicParamLen (_ : Unit) : UInt64 :=
  UInt64.ofNat PUBLIC_PARAM_LEN

@[export eth_xmss_const_message_len]
def constMessageLen (_ : Unit) : UInt64 :=
  UInt64.ofNat MESSAGE_LEN

@[export eth_xmss_const_randomizer_len]
def constRandomizerLen (_ : Unit) : UInt64 :=
  UInt64.ofNat RANDOMIZER_LEN

@[export eth_xmss_const_seed_len]
def constSeedLen (_ : Unit) : UInt64 :=
  UInt64.ofNat SEED_LEN

@[export eth_xmss_const_chains]
def constChains (_ : Unit) : UInt64 :=
  UInt64.ofNat V

@[export eth_xmss_const_layer_height]
def constLayerHeight (_ : Unit) : UInt64 :=
  UInt64.ofNat LAYER_HEIGHT

@[export eth_xmss_const_pub_key_size]
def constPubKeySize (_ : Unit) : UInt64 :=
  UInt64.ofNat PUB_KEY_SIZE

@[export eth_xmss_const_sig_size]
def constSigSize (_ : Unit) : UInt64 :=
  UInt64.ofNat SIG_SIZE

/-! ## Operations -/

/-- Read a fixed-size input, rejecting any other length with the given error. -/
private def readExact (n : Nat) (bytes : ByteArray) (bad : Nat → XmssError) :
    Except XmssError (Vector UInt8 n) :=
  -- Too short or too long is refused: no padding, no truncation.
  if h : bytes.size = n then .ok ⟨bytes.data, h⟩ else .error (bad bytes.size)

/-- The public key grown from a seed.

It builds the whole top tree, `2^16` one-time keys. -/
@[export eth_xmss_key_gen]
def keyGenExport (seed : ByteArray) : IO ByteArray :=
  runXmss do
    let seed ← readExact SEED_LEN seed .badSeedSize
    -- The secret half is dropped: the seed regrows it.
    let (_, pk) := keyGen seed
    return encodePublicKey pk

/-- Sign a message at a leaf index with the key grown from a seed. -/
@[export eth_xmss_sign]
def signExport (seed : ByteArray) (leafIndex : LeafIndex) (msg : ByteArray) :
    IO ByteArray :=
  runXmss do
    let seed ← readExact SEED_LEN seed .badSeedSize
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    -- Signing needs no public key, so the top tree's root is never computed here.
    let sig ← sign ⟨seed⟩ leafIndex msg
    return encodeSignature sig

/-- Whether a signature signs a message under a public key, as 1 or 0.

The leaf index travels inside the signature. -/
@[export eth_xmss_verify]
def verifyExport (pk : ByteArray) (msg : ByteArray) (sig : ByteArray) : IO UInt8 :=
  runXmss do
    -- Only the lengths are checked: every correctly sized string decodes.
    let pk ← decodePublicKey pk
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    let sig ← decodeSignature sig
    return if verify pk msg sig then 1 else 0

end EthLib.Cryptography.Xmss.Exports
