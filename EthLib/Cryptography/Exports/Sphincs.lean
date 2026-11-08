module

public import EthLib.Base.Exports
public import EthLib.Cryptography.Sphincs.Constants
public import EthLib.Cryptography.Sphincs.Errors
public import EthLib.Cryptography.Sphincs.KeyGen
public import EthLib.Cryptography.Sphincs.Sign
public import EthLib.Cryptography.Sphincs.Serialization

/-!
# Exports: leanSPHINCS

C-ABI exports for leanSPHINCS, callable from the Python C extension.

Only key generation, signing and verification cross the boundary, with the sizes.

The scheme is a black box to callers: no hash, chain, tree or FORS instance is exported.
-/

public section

namespace EthLib.Cryptography.Sphincs.Exports

open EthLib.Exports (Result)

open EthLib.Cryptography.Sphincs
open EthLib.Cryptography.Sphincs.Constants

/-- Run a fallible leanSPHINCS computation, with its error as a code and a message. -/
def runSphincs {α : Type} (act : Except SphincsError α) : Result α :=
  act.mapError fun e => (e.code, e.message)

/-! ## Sizes

The Python C extension reads every size through these functions when it loads.

So the wrapper hardcodes no constant of its own.

Each takes a `Unit` to keep the C-ABI signature predictable. -/

@[export eth_sphincs_const_n]
def constN (_ : Unit) : UInt64 :=
  UInt64.ofNat N

@[export eth_sphincs_const_message_len]
def constMessageLen (_ : Unit) : UInt64 :=
  UInt64.ofNat MESSAGE_LEN

@[export eth_sphincs_const_randomizer_len]
def constRandomizerLen (_ : Unit) : UInt64 :=
  UInt64.ofNat RANDOMIZER_LEN

@[export eth_sphincs_const_seed_len]
def constSeedLen (_ : Unit) : UInt64 :=
  UInt64.ofNat SEED_LEN

@[export eth_sphincs_const_chains]
def constChains (_ : Unit) : UInt64 :=
  UInt64.ofNat V

@[export eth_sphincs_const_counter_len]
def constCounterLen (_ : Unit) : UInt64 :=
  UInt64.ofNat COUNTER_LEN

@[export eth_sphincs_const_top_height]
def constTopHeight (_ : Unit) : UInt64 :=
  UInt64.ofNat TOP_HEIGHT

@[export eth_sphincs_const_lower_height]
def constLowerHeight (_ : Unit) : UInt64 :=
  UInt64.ofNat LOWER_HEIGHT

@[export eth_sphincs_const_fors_trees]
def constForsTrees (_ : Unit) : UInt64 :=
  UInt64.ofNat FORS_TREES

@[export eth_sphincs_const_fors_height]
def constForsHeight (_ : Unit) : UInt64 :=
  UInt64.ofNat FORS_HEIGHT

@[export eth_sphincs_const_pub_key_size]
def constPubKeySize (_ : Unit) : UInt64 :=
  UInt64.ofNat PUB_KEY_SIZE

@[export eth_sphincs_const_sig_size]
def constSigSize (_ : Unit) : UInt64 :=
  UInt64.ofNat SIG_SIZE

/-! ## Operations -/

/-- Read a fixed-size input, rejecting any other length with the given error. -/
private def readExact (n : Nat) (bytes : ByteArray) (bad : Nat → SphincsError) :
    Except SphincsError (Vector UInt8 n) :=
  -- Too short or too long is refused: no padding, no truncation.
  if h : bytes.size = n then .ok ⟨bytes.data, h⟩ else .error (bad bytes.size)

/-- The public key `PK.seed | PK.root` of `SK.seed`.

It builds the whole top tree, `2^10` one-time keys. -/
@[export eth_sphincs_key_gen]
def keyGenExport (seed : ByteArray) : Result ByteArray :=
  runSphincs do
    let seed ← readExact SEED_LEN seed .badSeedSize
    -- The secret half is dropped: the seed regrows it.
    let (_, pk) := keyGen seed
    return encodePublicKey pk

/-- Sign a message with the key of `SK.seed`.

The message digest picks the FORS instance, so no index crosses the boundary. -/
@[export eth_sphincs_sign]
def signExport (seed : ByteArray) (msg : ByteArray) : Result ByteArray :=
  runSphincs do
    let seed ← readExact SEED_LEN seed .badSeedSize
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    -- Signing rebuilds the public key from the seed, since `H_msg` hashes `PK.root`.
    let sig ← sign ⟨seed⟩ msg
    return encodeSignature sig

/-- Whether a signature signs a message under a public key, as 1 or 0. -/
@[export eth_sphincs_verify]
def verifyExport (pk : ByteArray) (msg : ByteArray) (sig : ByteArray) : Result UInt8 :=
  runSphincs do
    -- Only the lengths are checked: every correctly sized string decodes.
    let pk ← decodePublicKey pk
    let msg ← readExact MESSAGE_LEN msg .badMessageSize
    let sig ← decodeSignature sig
    return if verify pk msg sig then 1 else 0

end EthLib.Cryptography.Sphincs.Exports
