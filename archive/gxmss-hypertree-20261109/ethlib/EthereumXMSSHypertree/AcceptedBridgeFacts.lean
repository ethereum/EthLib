/- Authors: Matthias Meijers -/

module
public import EthereumXMSSHypertree.GenericEncoding

/-!
# Accepted source digest truncation

The total 58-digit word retains the source's first 58 digits. The decoder
returns that word precisely on acceptance, including its complete six-digit
zero-tail test. Injectivity is restricted to accepted digests.
-/

public section

namespace EthereumXMSSHypertree.AcceptedBridgeFacts

open EthLib.Cryptography.Xmss EthLib.Cryptography.Xmss.Constants
open GXMSS.Encoding GenericEncoding

/-- The source's first 58 digits, whether or not the digest passes its complete decoder. -/
@[expose]
def retainedDigits (digest : Digest) : Vector (Fin CHAIN_LENGTH) V :=
  Vector.ofFn fun i => (Internal.digits digest)[i.val]'(by
    have := i.isLt
    simp only [V, DIGITS] at *
    omega)

/-- The total generic word supplied by the source's first 58 base-four digits. -/
@[expose]
def truncatedWord (digest : Digest) : Codeword 58 (2 ^ 2) :=
  sourceCodewordEquiv (retainedDigits digest)

/-- Acceptance by the complete source decoder, including its six omitted zero digits. -/
@[expose]
def accepts (digest : Digest) : Bool := (codeword? digest).isSome

/-- The complete source decoder returns its first 58 digits exactly when it accepts. -/
theorem codeword_eq_if_accepts (digest : Digest) :
    codeword? digest = if accepts digest then some (retainedDigits digest) else none := by
  unfold accepts codeword?
  split <;> simp_all [retainedDigits]

/-- Mapping the actual source decoder is exactly the accepted total-word observation. -/
theorem codeword_map_eq_if_accepts (digest : Digest) :
    (codeword? digest).map sourceCodewordEquiv =
      if accepts digest then some (truncatedWord digest) else none := by
  rw [codeword_eq_if_accepts]
  split <;> rfl

/-- An accepted digest's retained digits are its actual successful decoder output. -/
theorem codeword_of_accepts (digest : Digest) (accepted : accepts digest = true) :
    codeword? digest = some (retainedDigits digest) := by
  rw [codeword_eq_if_accepts]
  simp only [accepted, ↓reduceIte]

/-- The total truncated word is injective on the accepted source-digest set. -/
theorem truncatedWord_injOn : Set.InjOn truncatedWord {digest | accepts digest = true} := by
  intro first hfirst second hsecond hword
  have hretained := sourceCodewordEquiv.injective hword
  have hsecondDecoded := codeword_of_accepts second hsecond
  rw [← hretained] at hsecondDecoded
  exact eq_of_codeword (codeword_of_accepts first hfirst) hsecondDecoded

/-- Every accepted digest retains all six source zero-tail constraints. -/
theorem accepts_tail_zero (digest : Digest) (accepted : accepts digest = true)
    (i : Nat) (hlo : 58 ≤ i) (hhi : i < 64) :
    EthLib.Base.bytesToUint digest / 4 ^ i % 4 = 0 :=
  (codeword?_eq_some (codeword_of_accepts digest accepted)).2.1 i hlo hhi

/-- The existing generic encoding observes exactly the source acceptance and retained word. -/
theorem sourceEncoding_value_eq_if_accepts {M : Type}
    (hash : ByteArray → Vector UInt8 32) (layer : Layer) (messageBytes : M → ByteArray)
    (pp : PublicParam) (message : M) (randomizer : Randomizer) (epoch : UInt32) :
    (sourceEncoding hash layer messageBytes).value pp message randomizer epoch =
      let digest := (messageDigest (pureHash hash) pp layer epoch
        (messageBytes message) randomizer).run
      if accepts digest then some (truncatedWord digest) else none := by
  rw [sourceEncoding_value, codeword_map_eq_if_accepts]

end EthereumXMSSHypertree.AcceptedBridgeFacts
