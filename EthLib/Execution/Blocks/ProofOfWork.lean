module

public import EthLib.Cryptography.Ethash.Hashimoto
public import EthLib.Execution.Blocks.Header
public import EthLib.Execution.ErrorFormat

/-!
# `Blocks.ProofOfWork`

The proof of work of a header before Paris.

The seal hash is the Keccak-256 hash of the header without its mix digest and nonce.

Ethash of the seal hash and the nonce, over the cache of the epoch, gives a mix digest and a result.

The header is sealed when it holds that mix digest, and the result is within the target.

The target is `2^256` over the difficulty, rounded down.

Section 4.3.4 of the Yellow Paper, Berlin version, states the check: [`Paper.tex`][yp].

Section 11.5 of the same version describes the seal.

The seal hash keeps every field but the mix digest and the nonce.

So from London, whose header holds a base fee after its nonce, it keeps the base fee.

[yp]: https://github.com/ethereum/yellowpaper/blob/beacfbd29ccc04dfd790f2282d4c4b1c0afc9b5a/Paper.tex
-/

@[expose] public section

namespace EthLib.Execution.Blocks

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Cryptography.Ethash (PowOutput hashimotoLight datasetSize cache)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-- Why the proof of work of a header fails. -/
inductive PowError where
  /-- The header without its mix digest and nonce has no RLP form. -/
  | encoding (error : RlpError)
  /-- The mix digest `actual` of the header is not `expected`, the one that Ethash gives. -/
  | wrongMixDigest (expected : ByteArray) (actual : Bytes32)
  /-- The result `result` of Ethash is above `target`, `2^256` over the difficulty. -/
  | resultAboveTarget (result target : Nat)
  deriving DecidableEq

/-- The form of a proof-of-work error in Lean syntax, with its arguments.

Each value has its name, and each byte string is in hex. -/
def PowError.reprPrec : PowError → Nat → Std.Format
  | .encoding error, p =>
    constructorFormat "EthLib.Execution.Blocks.PowError.encoding" [reprArg error] p
  | .wrongMixDigest expected actual, p =>
    constructorFormat "EthLib.Execution.Blocks.PowError.wrongMixDigest"
      [namedArg "expected" expected, namedArg "actual" actual] p
  | .resultAboveTarget result target, p =>
    constructorFormat "EthLib.Execution.Blocks.PowError.resultAboveTarget"
      [namedArg "result" result, namedArg "target" target] p

instance : Repr PowError := ⟨PowError.reprPrec⟩

/-- The stable code of an error, one per constructor, for the C exports.

The codes start at 221, above the codes of the other block errors. -/
def PowError.code : PowError → UInt32
  | .encoding _ => 221
  | .wrongMixDigest .. => 222
  | .resultAboveTarget .. => 223

namespace Header

variable {fork : Fork}

/-- The item of a header without its mix digest and nonce: `H_ñ` of the Yellow Paper, 4.3.4.

It keeps every other field of a header before Paris, the base fee from London included. -/
def sealItem (h : Header fork) : Item :=
  -- `L_H(H_ñ)`: `L_H(H)` without `H_m` and `H_n`, then from London the base fee of EIP-1559.
  .list ([Codec.toItem h.parentHash, Codec.toItem h.ommersHash,
    Codec.toItem h.coinbase, Codec.toItem h.stateRoot, Codec.toItem h.transactionsRoot,
    Codec.toItem h.receiptRoot, Codec.toItem h.bloom, Codec.toItem h.difficulty,
    Codec.toItem h.number, Codec.toItem h.gasLimit, Codec.toItem h.gasUsed,
    Codec.toItem h.timestamp, Codec.toItem h.extraData] ++ Item.ofSince h.baseFeePerGas)

/-- The seal hash of a header: the Keccak-256 hash of the RLP form of its seal item. -/
def sealHash (h : Header fork) : Except RlpError Hash32 := do
  -- `KEC(RLP(L_H(H_ñ)))`, the hash that Ethash takes, Appendix J.
  return keccak256 (← encode h.sealItem)

end Header

/-- The largest result that a difficulty accepts: `2^256` over the difficulty, rounded down.

A difficulty of 0 accepts only the result 0, but the difficulty rule never gives less than `2^17`.
-/
def powTarget (difficulty : Nat) : Nat :=
  -- `n ≤ 2^256 / H_d` for an integer `n` is `n ≤ floor(2^256 / H_d)`.
  2 ^ 256 / difficulty

/-- The output of Ethash for a header: over the cache and the dataset size of its epoch. -/
def powOutput {fork : Fork} (h : Header fork) : Except PowError PowOutput := do
  let hash ← h.sealHash.mapError .encoding
  -- `(m, n) = PoW(H_ñ, H_n, d)` of Appendix J, mix digest first.
  --
  -- `d` comes from the cache and the dataset size of the epoch of `H_i`.
  return hashimotoLight (datasetSize h.number) (cache h.number) ⟨hash.toArray⟩ ⟨h.nonce.toArray⟩

/-- Whether an output of Ethash seals a header: `m = H_m` and `n ≤ 2^256 / H_d`.

The mix digest is checked first. -/
def checkPowOutput {fork : Fork} (h : Header fork) (out : PowOutput) : Except PowError Unit :=
  -- §4.3.4: `m = H_m`; from Paris, EIP-4399 gives this field to the beacon randomness.
  if out.mixDigest ≠ ⟨h.prevRandao.toArray⟩ then
    .error (.wrongMixDigest out.mixDigest h.prevRandao)
  -- And `n ≤ 2^256 / H_d`, with `n` read as a big-endian integer, which §4.3.4 leaves implicit.
  else if powTarget h.difficulty < bytesToNat out.result.toList then
    .error (.resultAboveTarget (bytesToNat out.result.toList) (powTarget h.difficulty))
  else .ok ()

/-- Check the proof of work of a header, as section 4.3.4 of the Yellow Paper asks. -/
def checkProofOfWork {fork : Fork} (h : Header fork) : Except PowError Unit :=
  powOutput h >>= checkPowOutput h

end EthLib.Execution.Blocks
