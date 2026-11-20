module

public import EthLib.Cryptography.Proofs.Wots.GraphChain
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.ChainGraph
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.PairedHashWord

/-!
# Chain walks through the two public hash rows

The leanXMSS draft, section "WOTS+C", defines a walk by repeated calls to the chain step.

Every step uses the first 16 bytes but the hash caller receives all 32 bytes.

The graph reads both halves for each step and carries the low half to the next position.
-/

@[expose] public section

namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainGraph

open Constants HashSig OracleComp OracleSpec Wots

/-- A digest represents its little-endian 128-bit integer. -/
def digestEquiv : Digest ≃ Word where
  toFun bytes := BitVec.ofNat digestBits (bytesToUint bytes)
  invFun := ofBV 16
  left_inv bytes := ofBV_ofNat_bytesToUint bytes (by decide)
  right_inv word := (congrArg (BitVec.ofNat digestBits) (bytesToUint_ofBV 16 word)).trans
    (BitVec.eq_of_toNat_eq ((BitVec.toNat_ofNat word.toNat digestBits).trans
      (Nat.mod_eq_of_lt word.isLt)))

/-- The recursive proof asks for a total position map.

It reads only positions from zero through the end of the chain. -/
def schedule (pp : PublicParam) (key : Chain) :
    GraphChain.Schedule (graph pp) (CHAIN_LENGTH - 1) where
  cell pos := cell key (min pos (CHAIN_LENGTH - 1)) (by simp [CHAIN_LENGTH])
  low j := .inl (key, j)
  high j := .inr (key, j)
  low_children j := by
    change [predecessor (key, j)] = [cell key (min j.val (CHAIN_LENGTH - 1)) _]
    simp only [Nat.min_eq_left (Nat.le_of_lt j.isLt)]
    rfl
  high_children j := by
    change [predecessor (key, j)] = [cell key (min j.val (CHAIN_LENGTH - 1)) _]
    simp only [Nat.min_eq_left (Nat.le_of_lt j.isLt)]
    rfl
  next j := by
    simp only [Nat.min_eq_left j.isLt]
    rfl

/-- Expose the private sampler and the virtual public rows within the graph oracle. -/
def liftPublic : QueryImpl (unifSpec + Public) (OracleComp (Public.withLabels Chain Row Word)) :=
  Sum.rec (fun n => query (spec := Public.withLabels Chain Row Word) (.inl (.inl (.inl n))))
    (fun row => query (spec := Public.withLabels Chain Row Word) (.inl (.inl (.inr row))))

/-- The library hash, after splitting each raw reply and lifting both queries into the graph. -/
def hash (bytes : ByteArray) : OracleComp (Public.withLabels Chain Row Word) (Vector UInt8 32) :=
  simulateQ liftPublic
    (simulateQ PairedHashWord.readHalves (queryH (m := OracleComp OracleWorld) bytes))

private theorem hash_eq (bytes : ByteArray) :
    hash bytes = (do
      let l ← query (spec := Public.withLabels Chain Row Word)
        (.inl (.inl (.inr (.inl bytes.data.toList))))
      let h ← query (spec := Public.withLabels Chain Row Word)
        (.inl (.inl (.inr (.inr bytes.data.toList))))
      pure (ofOutput (PairedHashWord.halves.symm (l, h)))) := by
  change simulateQ liftPublic (simulateQ PairedHashWord.readHalves (ofOutput <$>
    (liftM (OracleWorld.query (.inr bytes.data.toList)) : OracleComp OracleWorld HashOutput))) = _
  simp [PairedHashWord.readHalves, RandomOraclePairedValue.readHalves, liftPublic, ← bind_pure_comp]

/-- The library and graph steps read the same two public rows in order. -/
theorem chainStep_eq_publicStep (pp : PublicParam) (key : Chain)
    (j : Fin (CHAIN_LENGTH - 1)) (d : Digest) :
    chainStep hash pp key.layer key.epoch key.index j d =
      GraphChain.publicStep (schedule pp key) digestEquiv j d := by
  -- Reassembling the two halves and taking the first gives the original low row.
  simp only [chainStep, th, hash_eq, bind_assoc, pure_bind, PairedHashWord.first_half_bytes,
    Equiv.apply_symm_apply]
  -- The graph encodes the predecessor as a word and the library starts with its bytes.
  have bytes : ofBV 16 (digestEquiv d) = d := digestEquiv.symm_apply_apply d
  have inputs : input pp (key, j) (digestEquiv d) =
      (thInput pp (addrChain key.layer key.epoch j)
        (packBytes d ++ packBytes (uintToBytes 16 key.index.val))).data.toList := by
    rw [input, bytes]
    rfl
  -- Both graph rows use the same chain index and input bytes.
  unfold GraphChain.publicStep
  change _ = (do
    let l ← query (spec := Public.withLabels Chain Row Word)
      (.inl (.inl (.inr (.inl (input pp (key, j) (digestEquiv d))))))
    let _ ← query (spec := Public.withLabels Chain Row Word)
      (.inl (.inl (.inr (.inr (input pp (key, j) (digestEquiv d))))))
    pure (ofBV 16 l))
  rw [inputs]
  simp only [pure_bind]
  rfl

/-- The library chain and the graph walk return the same digest and final caches. -/
theorem chain_from_read (pp : PublicParam) (key : Chain) (start steps : Nat)
    (valid : start + steps < CHAIN_LENGTH) :
    simulateQ (graph pp).eagerImpl (do
      let v ← readCell (some ((schedule pp key).cell start))
      Xmss.chain hash pp key.layer key.epoch key.index start steps valid (digestEquiv.symm v)) =
      simulateQ (graph pp).eagerImpl (GraphChain.walkFromRead (schedule pp key) digestEquiv
        start steps (Nat.le_sub_one_of_lt valid)) :=
  GraphChain.chain_from_read (schedule pp key) digestEquiv
    (chainStep hash pp key.layer key.epoch key.index)
    (fun j d => congrArg (simulateQ (graph pp).eagerImpl) (chainStep_eq_publicStep pp key j d))
    start steps (Nat.le_sub_one_of_lt valid)

end EthLib.Cryptography.Xmss.Unforgeability.VCV.ChainGraph
