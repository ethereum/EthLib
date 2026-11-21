module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.VCV.RealGraphPrefix
public import EthLib.Cryptography.Proofs.Xmss.TweakableHash
public import EthLib.Cryptography.Proofs.Xmss.Address

/-!
# Mark full public calls that remain visible after normalizing honest work

All public calls from the adversary and verifier use the marked port.

During honest signing only the message digest trials use it.

Key generation uses the original port, as do private PRF, tick and uniform queries in every phase.
-/

public section
namespace EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix

open HashSig OracleSpec OracleComp Constants

/-- The second port has exactly the same physical byte key and full-word reply as the original. -/
abbrev Marked := Source + XmssSecurity.HashSpec

/-- Identify a message digest input at any parameter, layer and epoch. -/
def IsTrial (b : HashInput) : Prop :=
  ∃ (pp : PublicParam) (layer : Layer) (e : UInt32) (msg : ByteArray) (rho : Randomizer),
    (thInput pp (addrMsg layer e) (msg ++ packBytes rho)).data.toList = b

theorem isTrial_message (pp : PublicParam) (layer : Layer) (e : UInt32)
    (msg : ByteArray) (rho : Randomizer) :
    IsTrial (thInput pp (addrMsg layer e) (msg ++ packBytes rho)).data.toList := ⟨_,
      _, _, _, _, rfl⟩

/-- Every honest chain, leaf and internal node hash is outside the trial class, for any payload. -/
theorem not_isTrial_other (pp : PublicParam) (kind : AddressType) (other : kind ≠ .msg)
    (mu : Fin 8) (hi : Fin (2 ^ 24)) (lo : UInt32) (bytes : ByteArray) :
    ¬IsTrial (thInput pp (encodeAddress kind.code mu hi lo) bytes).data.toList := by
  rintro ⟨pp', l, e, msg, rho, eq⟩
  have same := (thInput_inj (ByteArray.ext (Array.toList_inj.mp eq))).2.1
  exact other (AddressType.code_injective (encodeAddress_inj.mp same).1.symm)

/-- Annotate a physical query without changing its answer type. -/
@[expose] noncomputable def mark (selected : HashInput → Prop) :
    QueryImpl Source (OracleComp Marked) := open Classical in
  fun t => match t with
    | .inl (.inr (.inl b)) => if selected b then liftM (Marked.query (.inr b))
        else liftM (Marked.query (.inl (.inl (.inr (.inl b)))))
    | .inl (.inl n) => liftM (Marked.query (.inl (.inl (.inl n))))
    | .inl (.inr (.inr u)) => liftM (Marked.query (.inl (.inl (.inr (.inr u)))))
    | .inr k => liftM (Marked.query (.inl (.inr k)))

/-- Read the same physical full word on the selected port. -/
@[expose] def markedFindHash (x : ByteArray) : OracleComp Marked (Vector UInt8 32) :=
  ofOutput <$> Marked.query (.inr x.data.toList)

/-- Read an honest unselected hash on the original port. -/
@[expose] def markedChainHash (x : ByteArray) : OracleComp Marked (Vector UInt8 32) :=
  ofOutput <$> Marked.query (.inl (.inl (.inr (.inl x.data.toList))))

theorem hash_chosen (selected : HashInput → Prop) (x : ByteArray)
    (chosen : selected x.data.toList) :
    simulateQ (mark selected) (hashOf sourcePass x) = markedFindHash x := by
  change simulateQ (mark selected) (ofOutput <$> (liftM
    (Source.query (.inl (.inr (.inl x.data.toList)))) : OracleComp Source HashOutput)) = _
  simp [simulateQ_map, mark, chosen, markedFindHash]

theorem hash_unchosen (selected : HashInput → Prop) (x : ByteArray)
    (skip : ¬ selected x.data.toList) :
    simulateQ (mark selected) (hashOf sourcePass x) = markedChainHash x := by
  change simulateQ (mark selected) (ofOutput <$> (liftM
    (Source.query (.inl (.inr (.inl x.data.toList)))) : OracleComp Source HashOutput)) = _
  simp [simulateQ_map, mark, skip, markedChainHash]

/-- The four byte layouts used during signing route to the finder or the uncharged tree port. -/
theorem trial_hash (pp : PublicParam) (l : Layer) (e : UInt32) (msg : ByteArray)
    (rho : Randomizer) :
    let x := thInput pp (addrMsg l e) (msg ++ packBytes rho)
    simulateQ (mark IsTrial) (hashOf sourcePass x) = markedFindHash x :=
  hash_chosen _ _ (isTrial_message pp l e msg rho)

theorem chain_hash (pp : PublicParam) (l : Layer) (e : UInt32) (mu : Fin (CHAIN_LENGTH - 1))
    (v : ByteArray) :
    let x := thInput pp (addrChain l e mu) v
    simulateQ (mark IsTrial) (hashOf sourcePass x) = markedChainHash x :=
  hash_unchosen _ _ (not_isTrial_other pp .chain (by decide) _ _ _ _)

theorem leaf_hash (pp : PublicParam) (l : Layer) (e : UInt32) (v : ByteArray) :
    let x := thInput pp (addrLeaf l e) v
    simulateQ (mark IsTrial) (hashOf sourcePass x) = markedChainHash x :=
  hash_unchosen _ _ (not_isTrial_other pp .leaf (by decide) _ _ _ _)

theorem node_hash (pp : PublicParam) (l : Layer) (level : Fin (LAYER_HEIGHT + 1))
    (j : UInt32) (v : ByteArray) :
    let x := thInput pp (addrNode l level j) v
    simulateQ (mark IsTrial) (hashOf sourcePass x) = markedChainHash x :=
  hash_unchosen _ _ (not_isTrial_other pp .node (by decide) _ _ _ _)

/-- Both representations of a byte query hit the same underlying physical hash. -/
@[expose] def eraseMark : QueryImpl Marked (OracleComp Source)
  | .inl t => liftM (Source.query t)
  | .inr b => liftM (Source.query (.inl (.inr (.inl b))))

/-- Erasing a whole adaptively marked phase gives the original program exactly. -/
theorem erase_phase {α : Type} (selected : HashInput → Prop) (body : OracleComp Source α) :
    simulateQ eraseMark (simulateQ (mark selected) body) = body := by
  rw [← QueryImpl.simulateQ_compose]
  have id : eraseMark ∘ₛ mark selected = QueryImpl.id' Source := by
    funext t
    rcases t with ((n | (b | u)) | k)
    · rfl
    · by_cases chosen : selected b <;> simp [QueryImpl.compose, mark, chosen,
          eraseMark, QueryImpl.id']
    · rfl
    · rfl
  rw [id, simulateQ_id']

/-- Mark all of the original client's raw calls and only the honest signer's digest trials. -/
@[expose] noncomputable def markedSigner :
    QueryImpl (World + SigningSpec) (WriterT RawLog (OracleComp Marked)) := fun t =>
  let selected : HashInput → Prop := match t with
    | .inl _ => fun _ => True
    | .inr _ => IsTrial
  WriterT.mk (simulateQ (mark selected)
    ((signerOf sourcePass sourceTick (fun _ => sourcePrf)) t).run)

/-- A refused signing request and a repeated query erase to the same raw reply and log entry. -/
theorem erase_client {α : Type} (body : OracleComp (World + SigningSpec) α) :
    simulateQ eraseMark (simulateQ markedSigner body).run =
      (simulateQ (signerOf sourcePass sourceTick (fun _ => sourcePrf)) body).run := by
  induction body using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', simulateQ_map, markedSigner,
      WriterT.run_mk, erase_phase, ih]

/-- The marked source starts at the sampled parameter and returns the genuine full observation. -/
@[expose] noncomputable def markedContinuation (A : Adversary)
    (pp : PublicParam) : OracleComp Marked Outcome := do
  let root ← simulateQ (mark (fun _ => False))
      (node (hashOf sourcePass) pp sourcePrf .top LAYER_HEIGHT 0)
  let pk : PublicKey := ⟨root, pp⟩
  let (candidate, log) ← (simulateQ markedSigner (A.main pk)).run
  let valid ← simulateQ (mark (fun _ => True))
      (verifyWith (hashOf sourcePass) pk candidate.message candidate.signature)
  return ⟨pk, candidate, log, valid⟩

/-- The new tags change neither the physical computation nor its native optional-reply client. -/
theorem erase_continuation (A : Adversary) (pp : PublicParam) :
    simulateQ eraseMark (markedContinuation A pp) = continuation A pp := by
  simp only [markedContinuation, continuation, simulateQ_bind, simulateQ_pure,
    erase_phase, erase_client]

end EthLib.Cryptography.Xmss.Unforgeability.VCV.RealClient.GraphPrefix
