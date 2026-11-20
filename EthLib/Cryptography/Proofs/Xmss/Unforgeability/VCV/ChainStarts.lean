module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PairedHashWord
public import EthLib.Cryptography.Proofs.HashSig.Option

/-!
# Starting cells of the leanXMSS chain graph

The leanXMSS draft, section "WOTS+C", derives starts `2j` and `2j+1` from one PRF word.
An honest layer signature leaves each of the 29 words in its full private cache.
Their halves supply the inputs for the actual 58 chain walks.
-/

public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainGraph

open Constants HashSig OracleComp OracleSpec

/-- The private cache returns the full word at its complete label. -/
abbrev PrivateWords := PublicParam × Address × ByteArray → Option HashOutput

/-- Two consecutive chains share one derivation address. -/
@[expose] def pairIndex (i : Fin V) : Fin (V / 2) :=
  ⟨i.val / 2, by have := i.isLt; simp only [V] at *; omega⟩

/-- The even chain consumes the low word and the odd chain consumes the high word. -/
def startHalf (i : Fin V) (word : HashOutput) : Word :=
  if i.val % 2 = 0 then (PairedHashWord.halves word).1 else (PairedHashWord.halves word).2

private theorem half_bytes (i : Fin V) (word : HashOutput) :
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ (ofOutput word) = ofBV 16 (startHalf i word) := by
  by_cases he : i.val % 2 = 0
  · rw [show (⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 0 from Fin.ext he]
    simpa [startHalf, he] using PairedHashWord.first_half_bytes word
  · have hodd : i.val % 2 = 1 := by omega
    rw [show (⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) = 1 from Fin.ext hodd]
    simpa [startHalf, he] using PairedHashWord.second_half_bytes word

/-- Project each populated private derivation word onto both of its graph starting cells. -/
def startTable (cache : PrivateWords) (pp : PublicParam) (key : Chain) : Option Word :=
  (cache (pp, addrPrf key.layer key.epoch (pairIndex key.index), ByteArray.empty)).map
    (startHalf key.index)

/-- The two chain indices associated with a single physical word. -/
def indexAt (j : Fin (V / 2)) (half : Fin 2) : Fin V :=
  ⟨2 * j.val + half.val, by have := j.isLt; have := half.isLt; simp only [V] at *; omega⟩

/-- Splitting a chain index into its private word and parity recovers the original position. -/
theorem indexAt_parts (i : Fin V) :
    indexAt (pairIndex i) ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ = i := by
  apply Fin.ext
  simp only [indexAt, pairIndex]
  omega

/-- Each pair reads the low and high rows of one private word, including when both are missing. -/
theorem startTable_pair (cache : PrivateWords) (pp : PublicParam) (layer : Layer) (epoch : UInt32)
    (j : Fin (V / 2)) :
    (startTable cache pp ⟨layer, epoch, indexAt j 0⟩,
      startTable cache pp ⟨layer, epoch, indexAt j 1⟩) =
    ((cache (pp, addrPrf layer epoch j, ByteArray.empty)).map (fun w => (PairedHashWord.halves w).1),
      (cache (pp, addrPrf layer epoch j, ByteArray.empty)).map (fun w => (PairedHashWord.halves w).2)) := by
  have pair (h : Fin 2) : pairIndex (indexAt j h) = j := Fin.ext (by
    change (2 * j.val + h.val) / 2 = j.val
    omega)
  have low : startHalf (indexAt j 0) = fun w => (PairedHashWord.halves w).1 := by
    funext w
    simp [startHalf, indexAt]
  have high : startHalf (indexAt j 1) = fun w => (PairedHashWord.halves w).2 := by
    funext w
    simp [startHalf, indexAt]
  simp only [startTable, pair, low, high]

/-- Storing a physical word changes exactly its pair's start lookups at this parameter. -/
theorem startTable_store (cache : PrivateWords) (pp : PublicParam) (layer : Layer)
    (epoch : UInt32) (j : Fin (V / 2)) (word : HashOutput) (key : Chain) :
    startTable (Function.update cache (pp, addrPrf layer epoch j, ByteArray.empty) (some word)) pp key =
      if key.layer = layer ∧ key.epoch = epoch ∧ pairIndex key.index = j then
        some (startHalf key.index word)
      else startTable cache pp key := by
  simp only [startTable, Function.update_apply, Prod.mk.injEq, true_and, and_true, addrPrf_inj]
  split <;> rfl

/-- Initializing the start rows leaves the public hash cache and all chain-step rows arbitrary. -/
@[expose] def stateOfStarts (cache : PrivateWords) (pp : PublicParam) (publicCache : Public.QueryCache)
    (rowCache : (Row →ₒ Word).QueryCache) : RelabelState Public Chain Row Word :=
  (publicCache, .ofFn (Sum.elim (startTable cache pp) fun r => rowCache r))

/-- The actual collector returns 58 starts from 29 full private words in the same cache. -/
theorem chainStarts_words (pp : PublicParam) (layer : Layer) (epoch : UInt32)
    (cache : PrivateWords) (starts : Vector Digest V)
    (completed : chainStarts pp (fun p a b => ofOutput <$> cache (p, a, b)) layer epoch = some starts) :
    ∃ words : Fin (V / 2) → HashOutput,
      (∀ j, cache (pp, addrPrf layer epoch j, ByteArray.empty) = some (words j)) ∧
      (∀ i : Fin V, starts[i] = ofBV 16 (startHalf i (words (pairIndex i)))) := by
  unfold chainStarts at completed
  obtain ⟨pairs, collected, returned⟩ := Option.bind_eq_some_iff.mp completed
  have selected (j : Fin (V / 2)) := ofFnInOrder_eq_some_get _ _ pairs collected j
  have cells (j : Fin (V / 2)) :
      ∃ w : HashOutput, cache (pp, addrPrf layer epoch j, ByteArray.empty) = some w ∧
        ofOutput w = pairs[j] := Option.map_eq_some_iff.mp (selected j)
  choose words atWord bytes using cells
  refine ⟨words, atWord, ?_⟩
  intro i
  -- The index and parity are exactly those used by the library collector.
  rw [← Option.some.inj returned]
  refine (Vector.getElem_ofFn (f := fun i : Fin V =>
    halfOf ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩ pairs[pairIndex i]) i.isLt).trans ?_
  simpa only [bytes] using half_bytes i (words (pairIndex i))

/-- The graph's starting tables contain the values passed by the original chain computation. -/
theorem chainStarts_table (pp : PublicParam) (layer : Layer) (epoch : UInt32)
    (cache : PrivateWords) (starts : Vector Digest V)
    (completed : chainStarts pp (fun p a b => ofOutput <$> cache (p, a, b)) layer epoch = some starts) :
    ∀ i : Fin V, (startTable cache pp ⟨layer, epoch, i⟩).map (ofBV 16) = some starts[i] := by
  obtain ⟨words, atWord, startsAt⟩ := chainStarts_words pp layer epoch cache starts completed
  intro i
  rw [startsAt]
  simp only [startTable, atWord, Option.map_some]
  rfl

end EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainGraph
