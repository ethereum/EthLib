module

public import EthLib.Execution.Rpc.Raw
public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Proofs.Rpc.Block
public import EthLib.Execution.Proofs.Rpc.Header
public import EthLib.Execution.Proofs.Rpc.TransactionInfo
public import EthLib.Execution.Proofs.Blocks.Block
public import EthLib.Execution.Proofs.Blocks.Header
public import EthLib.Execution.Proofs.Blocks.TypedRoots
public import EthLib.Serialization.Proofs.Ssz.Codec.JsonLaws

/-!
# Proofs: the raw getters

The bytes of a transaction hash to the hash that names it in the request.

In a valid view, the raw header of a block hashes to the hash that the block objects report.

It decodes back to the header.

The raw block decodes back to the block, with each transaction as its item in a body.

This holds when each ommer is at the fork that the decoder gives its own number.

In a valid view, take a canonical block after the lowest.

Its raw receipts have the receipts root of its header.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.Rlp (Codec)
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions
open EthLib.Cryptography.Hash.Keccak (keccak256)

namespace ChainView

/-- A getter of a block gives a value exactly when the parameter names a block that gives it. -/
theorem ofBlock_eq_ok {α : Type} {v : ChainView} {p : BlockParam}
    {f : BlockRecord → Except Serialization.JsonRpc.RpcError α} {a : α} :
    v.ofBlock p f = .ok a ↔ ∃ r, v.resolve p = .ok (some r) ∧ f r = .ok a := by
  unfold ofBlock
  rcases v.resolve p with e | _ | r <;> simp [bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- The bytes of a transaction hash to the hash that names it in the request. -/
theorem keccak256_rawTransaction {v : ChainView} {hash : Hash32} {raw : ByteArray}
    (h : v.rawTransaction hash = .ok raw) : keccak256 raw = hash := by
  unfold rawTransaction at h
  rcases hf : v.findTransaction hash with _ | ⟨r, tx, index⟩
  · simp [hf] at h
  · simp only [hf] at h
    obtain ⟨-, -, hhash⟩ := findTransaction_some hf
    have he := mapError_ok_iff.mp h
    simp only [transactionHash, he, bind, Except.bind, pure, Except.pure] at hhash
    exact Except.ok.inj hhash

/-- The header object of a block reports the hash that the node keeps for it. -/
theorem getObjVal_hash_headerObject (r : BlockRecord) :
    (headerObject r).getObjVal? "hash" = .ok (hash32Json r.hash) :=
  Serialization.Ssz.getObjVal?_mkObj (names_distinct_headerFields r.hash r.block.header)
    (by simp [headerFields])

end ChainView

namespace BlockRecord

/-- When the kept hash of a block is the hash of its header, the raw header hashes to it.

The raw header also decodes back to the header. -/
theorem rawHeader_of_hash {r : BlockRecord} (h : r.block.header.hash = .ok r.hash) :
    ∃ raw, r.rawHeader = .ok raw ∧ keccak256 raw = r.hash ∧
      Codec.decode raw = .ok r.block.header := by
  obtain ⟨raw, hraw, hk⟩ := Header.hash_eq_ok_iff.mp h
  exact ⟨raw, by simp [rawHeader, hraw, Except.mapError], hk, Codec.decode_encode hraw⟩

/-- The raw block decodes back to the block, with each transaction as its item in a body.

Each ommer must be at the fork that the decoder gives its own number. -/
theorem decode_rawBlock (forkOf : Nat → Fork) {r : BlockRecord} {raw : ByteArray}
    (hOmmers : ∀ ommer ∈ r.block.ommers, ommer.1 = forkOf ommer.2.number)
    (h : r.rawBlock = .ok raw) :
    ∃ items, bodyItems r.block = .ok items ∧ Block.decode forkOf raw = .ok items := by
  unfold rawBlock at h
  obtain ⟨items, hitems, h⟩ := bind_ok_iff.mp h
  have hitems := mapError_ok_iff.mp hitems
  -- The body items keep the ommers of the block.
  have hom : items.ommers = r.block.ommers := by
    unfold bodyItems at hitems
    obtain ⟨_, -, h⟩ := bind_ok_iff.mp hitems
    cases h
    rfl
  exact ⟨items, hitems, Block.decode_encode forkOf (hom ▸ hOmmers) (mapError_ok_iff.mp h)⟩

end BlockRecord

namespace ChainView

/-- In a valid view, every block that the node holds, and its pending block, has a raw header.

It hashes to the hash that the node keeps for the block, and decodes back to the header. -/
theorem Valid.rawHeader {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {r : BlockRecord} (hr : r ∈ v.canonical ++ v.side ∨ v.pending = some r) :
    ∃ raw, r.rawHeader = .ok raw ∧ keccak256 raw = r.hash ∧
      Codec.decode raw = .ok r.block.header := by
  rcases hr with hr | hr
  · exact BlockRecord.rawHeader_of_hash (hv.hash r hr)
  · exact BlockRecord.rawHeader_of_hash (hv.pending r hr).1

/-- In a valid view, the raw header that the getter returns is that of the block it resolves to.

It hashes to the hash that the node keeps for that block, and decodes back to its header. -/
theorem Valid.rawHeader_eq_ok {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {p : BlockParam} {raw : ByteArray} (h : v.rawHeader p = .ok raw) :
    ∃ r, v.resolve p = .ok (some r) ∧ keccak256 raw = r.hash ∧
      Codec.decode raw = .ok r.block.header := by
  obtain ⟨r, hr, hraw⟩ := ofBlock_eq_ok.mp h
  obtain ⟨raw', hraw', hk, hd⟩ := hv.rawHeader (resolve_mem hr)
  obtain rfl : raw = raw' := Except.ok.inj (hraw.symm.trans hraw')
  exact ⟨r, hr, hk, hd⟩

/-- In a valid view, the raw header of a block hashes to the hash of its block object. -/
theorem Valid.hash_blockByNumber_rawHeader {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {p : BlockParam} {raw : ByteArray} {full : Bool} {j : Lean.Json}
    (h : v.rawHeader p = .ok raw) (hb : v.blockByNumber p full = .ok j) :
    j.getObjVal? "hash" = .ok (hash32Json (keccak256 raw)) := by
  obtain ⟨r, hr, hk, -⟩ := hv.rawHeader_eq_ok h
  simp only [blockByNumber, hr, bind, Except.bind] at hb
  rw [Rpc.getObjVal_blockJson hb (by simp [headerNames]), getObjVal_hash_headerObject, hk]

/-- The roots of an output hold the receipts root of its receipts. -/
private theorem outputRoots_receipts {fork : Fork} {transactions : List Transaction}
    {withdrawals : Since .shapella fork (List Withdrawal)} {output : BlockOutput fork}
    {post : State.State} {roots : OutputRoots}
    (h : outputRoots transactions withdrawals output post = .ok roots) :
    receiptsRoot output.receipts = .ok roots.receipts := by
  unfold outputRoots at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, hr, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact mapError_ok_iff.mp hr

/-- A block that passes its output checks has the receipts root of its body. -/
private theorem outputChecks_receipts {fork : Fork} {header : Header fork}
    {output : BlockOutput fork} {roots : OutputRoots}
    (h : firstFailure (outputChecks header output roots) = .ok ()) :
    roots.receipts = header.receiptRoot := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have := all (decide (roots.receipts = header.receiptRoot), .wrongReceiptRoot)
    (by simp [outputChecks])
  simpa using this

/-- In a valid view, the raw receipts of a canonical block after the lowest have its receipts root.

The root is that of the trie that keys each receipt by its index.

The receipts of the lowest block, of side blocks and of the pending block are inputs of the view.

So no root binds them. -/
theorem Valid.rawReceipts_root {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) :
    ∃ raws, v.canonical[i + 1].rawReceipts = .ok raws ∧
      indexedRoot raws = .ok v.canonical[i + 1].block.header.receiptRoot := by
  obtain ⟨hst, result, hbody, hreceipts, -⟩ := hv.follows i hi
  obtain ⟨-, -, -, hashes, output, roots, hh, hout, hroots, hchecks, -⟩ :=
    stateTransition_eq_ok hst
  obtain ⟨hashes', hh', hout', -⟩ := runBody_eq_ok.mp hbody
  obtain rfl : hashes = hashes' := Except.ok.inj (hh.symm.trans hh')
  obtain rfl : output = result.output := Except.ok.inj (hout.symm.trans hout')
  have hroot := outputRoots_receipts hroots
  rw [outputChecks_receipts hchecks, hreceipts] at hroot
  obtain ⟨raws, hraws, hindexed⟩ := receiptsRoot_eq_ok_iff.mp hroot
  refine ⟨raws, ?_, hindexed⟩
  unfold BlockRecord.rawReceipts
  -- Each receipt encodes as the root saw it, so the getter reads the same bytes.
  have key : ∀ (l : List (UInt8 × Receipt v.canonical[i + 1].fork)) (out : List ByteArray),
      l.mapM (fun (type, r) => encodeReceipt type r) = .ok out →
      l.mapM (fun (type, receipt) => (encodeReceipt type receipt).mapError
        fun _ => BlockRecord.encodingError "receipt") = .ok out := by
    intro l
    induction l with
    | nil =>
      intro out h
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h ⊢
      exact h
    | cons x l ih =>
      intro out h
      obtain ⟨b, rest, hb, hrest, rfl⟩ := mapM_cons_ok.mp h
      exact mapM_cons_ok.mpr ⟨b, rest, mapError_ok_iff.mpr hb, ih _ hrest, rfl⟩
  exact key _ _ hraws

/-- In a valid view, take a parameter that resolves to a canonical block after the lowest.

The raw receipts that the getter returns have the receipts root of that block. -/
theorem Valid.rawReceipts_eq_ok {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {p : BlockParam} {i : Nat} (hi : i + 1 < v.canonical.length)
    (hp : v.resolve p = .ok (some v.canonical[i + 1])) {raws : List ByteArray}
    (h : v.rawReceipts p = .ok raws) :
    indexedRoot raws = .ok v.canonical[i + 1].block.header.receiptRoot := by
  obtain ⟨r, hr, hraws⟩ := ofBlock_eq_ok.mp h
  obtain rfl : v.canonical[i + 1] = r := Option.some.inj (Except.ok.inj (hp.symm.trans hr))
  obtain ⟨raws', hraws', hroot⟩ := hv.rawReceipts_root hi
  obtain rfl : raws = raws' := Except.ok.inj (hraws.symm.trans hraws')
  exact hroot

end ChainView

end EthLib.Execution.Rpc
