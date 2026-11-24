module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Xmss.Constants
public import EthLib.Cryptography.Xmss.Errors
public import EthLib.Cryptography.Xmss.KeyGen
public import EthLib.Cryptography.Xmss.Sign
public import EthLib.Cryptography.Xmss.Serialization

/-!
# `Exports.Xmss`

C-ABI exports for leanXMSS, callable from the Python C extension.

Key generation, signing, verification and reading a signature's leaf index cross the boundary.

So do the sizes and the two parameters of a codeword, as constants.

The scheme is a black box to callers: no hash, chain or tree is exported.
-/

public section

namespace EthLib.Cryptography.Xmss.Exports

open EthLib.Exports (Result ExportError toResult)

open EthLib.Cryptography.Xmss
open EthLib.Cryptography.Xmss.Constants

/-- An error reaches Python with its code and its own message. -/
instance : ExportError XmssError where
  code := XmssError.code
  message := XmssError.message

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

@[export eth_xmss_const_leaf_index_size]
def constLeafIndexSize (_ : Unit) : UInt64 :=
  UInt64.ofNat LEAF_INDEX_SIZE

@[export eth_xmss_const_pub_key_size]
def constPubKeySize (_ : Unit) : UInt64 :=
  UInt64.ofNat PUB_KEY_SIZE

@[export eth_xmss_const_sig_size]
def constSigSize (_ : Unit) : UInt64 :=
  UInt64.ofNat SIG_SIZE

/-! ## Codeword parameters

A digit of a digest is below `CHAIN_LENGTH`, and a codeword's chain digits sum to `TARGET_SUM`.

No operation takes either as an argument.

The test-vector generators read them to build signatures whose digest is not a codeword. -/

@[export eth_xmss_const_chain_length]
def constChainLength (_ : Unit) : UInt64 :=
  UInt64.ofNat CHAIN_LENGTH

@[export eth_xmss_const_target_sum]
def constTargetSum (_ : Unit) : UInt64 :=
  UInt64.ofNat TARGET_SUM

/-! ## Operations -/

/-- The public key grown from a seed.

It builds the whole top tree, `2^16` one-time keys. -/
@[export eth_xmss_key_gen]
def keyGenExport (seed : ByteArray) : Result (ByteArray × SecretKey) :=
  toResult (ε := XmssError) none do
    -- The length is the only check, and the 32 bytes are read as four lanes.
    let _ ← Base.exactBytes SEED_LEN seed .badSeedSize
    -- The C side keeps the secret key per seed, so a first signature reuses its top tree.
    let (pk, sk) := keyGen (Hash.Keccak.Lanes4.read seed 0)
    -- The secret key, which holds the built top tree, crosses as an opaque object.
    return (encodePublicKey pk, sk)

/-- The updated key and the signature of a message at a leaf index, signed with a secret key.

The C side keeps the key of each seed, and passes it back here to sign.

It returns the updated key even when signing fails, so a tree that signing built is not lost.

A message of the wrong length leaves the key as it is. -/
@[export eth_xmss_sign]
def signExport (sk : SecretKey) (leafIndex : LeafIndex) (msg : ByteArray) :
    SecretKey × Result ByteArray :=
  match Base.exactBytes (ε := XmssError) MESSAGE_LEN msg .badMessageSize with
  | .error err => (sk, toResult none (.error err))
  | .ok _ =>
    let (sig, sk) := sign sk leafIndex (Hash.Keccak.Lanes4.read msg 0)
    (sk, toResult none (encodeSignature <$> sig))

/-- Whether a signature signs a message under a public key, as 1 or 0.

The leaf index travels inside the signature. -/
@[export eth_xmss_verify]
def verifyExport (pk : ByteArray) (msg : ByteArray) (sig : ByteArray) : Result UInt8 :=
  toResult none do
    -- Only the lengths are checked: every correctly sized string decodes.
    let pk ← decodePublicKey pk
    let _ ← Base.exactBytes MESSAGE_LEN msg .badMessageSize
    let sig ← decodeSignature sig
    return if verify pk (Hash.Keccak.Lanes4.read msg 0) sig then 1 else 0

/-- The leaf index a signature carries.

It is returned as a `UInt64`, so the C side reads it as any other exported integer.

A `UInt32` always fits, so the conversion drops nothing. -/
@[export eth_xmss_signature_index]
def signatureIndexExport (sig : ByteArray) : Result UInt64 :=
  toResult none ((signatureIndex sig).map UInt32.toUInt64)

end EthLib.Cryptography.Xmss.Exports
