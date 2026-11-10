module

public import EthLib.Base.Proofs.Hex
public import EthLib.Cryptography.Bls.Fp12
public import EthLib.Cryptography.Hash.Keccak
public import EthLib.Execution.Proofs.Transactions.Envelope
public import EthLib.Serialization.Proofs.Rlp
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# A downstream consumer of EthLib

A package that depends on EthLib imports these modules and relies on what this file states.

Each example states one declaration that downstream proofs use, with its type written out.

An example that unfolds a definition pins its exposed body.

When an example fails, the public surface of EthLib changed: keep it, or mark the change breaking.
-/

open EthLib

-- A proof that a Keccak-256 circuit or program is right compares its output with this function.
example : (Cryptography.Hash.Keccak.keccak256 : ByteArray → Vector UInt8 32) =
    Cryptography.Hash.Keccak.keccak256 := rfl

-- A proof about a multiplication in Fp12 unfolds the product, so its body stays exposed.
example (a b : Cryptography.Bls.Fp12) :
    Cryptography.Bls.Fp12.mul a b =
      ⟨a.c0 * b.c0 + (a.c1 * b.c1).mulByV,
        (a.c0 + a.c1) * (b.c0 + b.c1) - a.c0 * b.c0 - a.c1 * b.c1⟩ := by
  unfold Cryptography.Bls.Fp12.mul
  rfl

-- A proof that its own RLP decoder is right reads back each encoding through this theorem.
example (x : Serialization.Rlp.Item) (b : ByteArray) (h : Serialization.Rlp.encode x = .ok b) :
    Serialization.Rlp.decode b = .ok x :=
  Serialization.Rlp.decode_encode x b h

-- A proof about an SSZ root of a typed value reduces it to the root of the untyped value.
example {α : Type} [Serialization.Ssz.SszType α] [Serialization.Ssz.LawfulSszType α] {a : α}
    {root : Vector UInt8 32} :
    Serialization.Ssz.SszType.hashTreeRoot a = .ok root ↔
      Serialization.Ssz.hashTreeRoot (Serialization.Ssz.SszType.desc α)
        (Serialization.Ssz.SszType.toValue a) = .ok root.toArray :=
  Serialization.Ssz.SszType.hashTreeRoot_ok_iff

-- A transaction decoder is checked against the specification through this equivalence.
example (fork : Base.Fork) (bytes : ByteArray) (t : Execution.Transactions.Transaction) :
    Execution.Transactions.decodeTransaction fork bytes = .ok t ↔
      Execution.Transactions.encodeTransaction t = .ok bytes ∧ t.fork ≤ fork :=
  Execution.Transactions.decodeTransaction_eq_ok_iff fork bytes t

-- A proof that its own hex encoder is right reads its output back through this theorem.
example (bytes : List UInt8) :
    Base.hexBytes? (bytes.flatMap Base.byteHexDigits) = some ⟨bytes.toArray⟩ :=
  Base.hexBytes?_flatMap bytes
