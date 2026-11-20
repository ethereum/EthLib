module

public import EthLib.Cryptography.Proofs.HashSig.Bytes
public import EthLib.Cryptography.Proofs.Xmss.Address
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Xmss.Ots
public import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel

/-!
# Public hash points for the leanXMSS chains

The leanXMSS draft, sections "Hashing and parameters" and "WOTS+C", gives the recurrence
`C_(i,mu+1) = Th(P, A_chain(layer,e,mu), C_(i,mu) | LE_128(i))`.

At fixed public parameter the two graph rows refer to the same 32-byte reply.
Only its low half feeds the next step.
The starting digest of each chain is a boundary cell supplied by the seed derivation.
The other address types have disjoint inputs by `input_ne_of_address_type`.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainGraph

open Constants HashSig OracleSpec

/-- The layer, epoch and chain index name a starting cell. -/
structure Chain where
  layer : Layer
  epoch : UInt32
  index : Fin V
  deriving DecidableEq

/-- The step number is its starting position. -/
abbrev Step := Chain × Fin (CHAIN_LENGTH - 1)

/-- The left row holds the low half and the right row holds the high half. -/
abbrev Row := Step ⊕ Step

/-- The graph's private and public labels both use 128-bit words. -/
abbrev Word := BitVec digestBits

/-- A public query selects one half of the word at the original byte string. -/
abbrev Public := (HashInput ⊕ HashInput) →ₒ Word

/-- The bytes passed to the hash by one chain step. -/
def input (pp : PublicParam) (s : Step) (v : Word) : HashInput :=
  (thInput pp (addrChain s.1.layer s.1.epoch s.2)
    (packBytes (ofBV 16 v) ++ packBytes (uintToBytes 16 s.1.index.val))).data.toList

/-- Equal hash inputs fix the step, the chain index in its suffix, and the predecessor value. -/
theorem input_injective {pp : PublicParam} {s t : Step} {v w : Word}
    (h : input pp s v = input pp t w) : s = t ∧ v = w := by
  obtain ⟨⟨l, e, i⟩, j⟩ := s
  obtain ⟨⟨l', e', i'⟩, j'⟩ := t
  -- The common byte string fixes its address and its complete payload.
  have raw := ByteArray.ext (Array.toList_inj.mp h)
  obtain ⟨_, address, payload⟩ := thInput_inj raw
  obtain ⟨rfl, rfl, rfl⟩ := addrChain_inj.mp address
  -- The prefix of the payload has exactly 16 bytes, so the two fields split uniquely.
  obtain ⟨values, indices⟩ := HashSig.byteArray_append_inj payload (by simp)
  have sameIndex : i = i' := Fin.ext (Base.uintToBytes_inj
    (lt_of_lt_of_le i.isLt (by decide : V ≤ 256 ^ 16))
    (lt_of_lt_of_le i'.isLt (by decide : V ≤ 256 ^ 16)) (Base.packBytes_injective indices))
  exact ⟨by cases sameIndex; rfl, ofBV_inj (by decide) (Base.packBytes_injective values)⟩

/-- An address of another type cannot give the same query bytes as a chain step. -/
theorem input_ne_of_address_type (pp other : PublicParam) (s : Step) (v : Word)
    (tag : AddressType) (different : AddressType.chain ≠ tag)
    (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) (payload : ByteArray) :
    input pp s v ≠ (thInput other (encodeAddress tag.code mu hi lo) payload).data.toList := by
  intro same
  have address := (thInput_inj (ByteArray.ext (Array.toList_inj.mp same))).2.1
  exact different (AddressType.code_injective (encodeAddress_inj.mp address).1)

/-- Executing the library step hashes these bytes and selects the first half of the response. -/
theorem chainStep_at_input {m : Type → Type} [Monad m] (H : HashInput → m (Vector UInt8 32))
    (pp : PublicParam) (s : Step) (v : Word) :
    chainStep (fun b => H b.data.toList) pp s.1.layer s.1.epoch s.1.index s.2 (ofBV 16 v) =
      (do return halfOf 0 (← H (input pp s v))) := rfl

/-- Position zero reads a derivation cell.
A later position reads the low half of the preceding step. -/
def cell (key : Chain) : (pos : Nat) → pos < CHAIN_LENGTH → Chain ⊕ Row
  | 0, _ => .inl key
  | j + 1, hj => .inr (.inl (key, ⟨j, by omega⟩))

/-- Both halves of a step have the same predecessor. -/
def predecessor (s : Step) : Chain ⊕ Row :=
  cell s.1 s.2.val (by have := s.2.isLt; omega)

/-- A public point carries the selected half and the actual query bytes.
The graph calls this function on exactly one child value. -/
def point (pp : PublicParam) (row : Row) (vs : List Word) : HashInput ⊕ HashInput :=
  row.elim (fun s => .inl (input pp s (vs.headD 0))) (fun s => .inr (input pp s (vs.headD 0)))

/-- At the graph's unary arity the public point fixes its row and its child value. -/
theorem point_injective {pp : PublicParam} {r t : Row} {v w : Word}
    (h : point pp r [v] = point pp t [w]) : r = t ∧ v = w := by
  cases r with
  | inl s =>
    cases t with
    | inl t =>
      obtain ⟨rfl, rfl⟩ := input_injective (Sum.inl.inj h)
      exact ⟨rfl, rfl⟩
    | inr t => contradiction
  | inr s =>
    cases t with
    | inl t => contradiction
    | inr t =>
      obtain ⟨rfl, rfl⟩ := input_injective (Sum.inr.inj h)
      exact ⟨rfl, rfl⟩

/-- The graph for all chain-step calls at this public parameter. -/
def graph (pp : PublicParam) : CanonicalGraph Public Chain Row Word where
  ch r := [r.elim predecessor predecessor]
  pt := point pp
  range_eq _ _ := rfl
  pt_inj := by
    intro r t vs ws hv hw h
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hv
    obtain ⟨w, rfl⟩ := List.length_eq_one_iff.mp hw
    obtain ⟨rfl, rfl⟩ := point_injective h
    exact ⟨rfl, rfl⟩

end EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainGraph
