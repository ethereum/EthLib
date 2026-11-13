module

public import EthLib.Execution.Rpc.Methods
public import EthLib.Execution.Proofs.Rpc.Raw
public import EthLib.Execution.Proofs.Blocks.Receipt
public import EthLib.Execution.Proofs.Transactions.Inclusion
public import EthLib.Execution.Proofs.Transactions.Process

/-!
# Proofs: the receipt objects

The receipt objects of a block follow its receipts, one for each transaction, in order.

Their logs are numbered from 0 across the block, and the lookup of one receipt keeps that number.

From Byzantium, the status of a receipt object is `0x1` exactly when the receipt is a success.

A receipt object has blob fields exactly for a blob transaction, with `2^17` blob gas per hash.

From Dencun, its blob gas price is the base fee per blob gas at the excess blob gas of the header.

In a valid view, take a canonical block after the lowest.

Each receipt object has the Bloom filter of its logs.

The gas of the receipt objects adds up to the last cumulative gas.

The base fee of the block is at most the maximum fee of each transaction.

So the effective gas price follows the formula of the description.

The run of the block reaches each transaction, on a state where the sender can buy the gas.

Buying it lowers the balance by the gas limit times the effective gas price of the object.

A blob transaction adds the blob gas of the object times its blob gas price.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions

namespace BlockRecord

/-- The positions of the elements of a list, from 0, are the numbers below its length. -/
private theorem map_zipIdx_snd {α : Type} (l : List α) (f : Nat → Nat) :
    l.zipIdx.map (fun x => f x.2) = (List.range l.length).map f := by
  have := congrArg (List.map f) (List.zipIdx_map_snd 0 (l := l))
  rw [List.map_map, List.range_eq_range'] at *
  exact this

/-- The object of a receipt has the index and type of the transaction, and the gas of the receipt.

It also has the Bloom filter, logs and outcome of the receipt, and the price of the transaction.

Its logs are those of the receipt, numbered from the given first log on. -/
theorem receiptInfo_eq_ok {r : BlockRecord} {config : ChainConfig}
    {index before firstLog : Nat} {tx : Transaction} {receipt : Receipt r.fork}
    {info : ReceiptInfo} (h : r.receiptInfo config index before firstLog tx receipt = .ok info) :
    info.transactionIndex = index ∧ info.type = tx.type ∧
      info.cumulativeGasUsed = receipt.cumulativeGasUsed ∧
      info.gasUsed = receipt.cumulativeGasUsed - before ∧ info.logsBloom = receipt.bloom ∧
      info.logs.map (·.log) = receipt.logs ∧
      info.logs.map (·.logIndex) = (List.range receipt.logs.length).map (firstLog + ·) ∧
      info.outcome = outcomeOf receipt.outcome ∧
      info.effectiveGasPrice = effectiveGasPrice r.baseFee tx := by
  unfold receiptInfo at h
  obtain ⟨ti, hti, h⟩ := bind_ok_iff.mp h
  obtain ⟨sender, hash, -, -, rfl⟩ := transactionInfo_eq_ok.mp hti
  rcases hto : tx.to with _ | a
  · rcases hc : (Evm.createAddress sender tx.nonce.toNat) with e | ca
    · simp [hto, hc, bind, Except.bind, Functor.map, Except.map, Except.mapError] at h
    · simp [hto, hc, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
        Except.mapError] at h
      subst h
      refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
      · simp [List.map_map, Function.comp_def]
      · clear h hti
        simpa [List.map_map, Function.comp_def] using map_zipIdx_snd receipt.logs (firstLog + ·)
  · simp [hto, bind, Except.bind, pure, Except.pure] at h
    subst h
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · simp [List.map_map, Function.comp_def]
    · clear h hti
      simpa [List.map_map, Function.comp_def] using map_zipIdx_snd receipt.logs (firstLog + ·)

/-- The objects of some receipts are one for each, built with the gas and logs of those before. -/
private theorem receiptInfosFrom_eq_ok {r : BlockRecord} {config : ChainConfig} :
    ∀ {l : List (Transaction × Receipt r.fork)} {infos : List ReceiptInfo}
      {index before firstLog : Nat},
      r.receiptInfosFrom config index before firstLog l = .ok infos →
      infos.length = l.length ∧ ∀ k (hk : k < infos.length), ∃ tx receipt,
        l[k]? = some (tx, receipt) ∧
        r.receiptInfo config (index + k)
          (((l.take k).map (·.2.cumulativeGasUsed)).getLast?.getD before)
          (firstLog + ((l.take k).map (·.2.logs.length)).sum) tx receipt = .ok infos[k] := by
  intro l
  induction l with
  | nil =>
    intro infos index before firstLog h
    simp only [receiptInfosFrom] at h
    cases h
    simp
  | cons x l ih =>
    intro infos index before firstLog h
    obtain ⟨tx, receipt⟩ := x
    simp only [receiptInfosFrom] at h
    obtain ⟨info, hinfo, h⟩ := bind_ok_iff.mp h
    obtain ⟨rest, hrest, h⟩ := bind_ok_iff.mp h
    have h : info :: rest = infos := by simpa [pure, Except.pure] using h
    subst h
    obtain ⟨hlen, hk⟩ := ih hrest
    refine ⟨by simp [hlen], ?_⟩
    intro k hk'
    cases k with
    | zero => exact ⟨tx, receipt, rfl, by simpa using hinfo⟩
    | succ k =>
      have hk'' : k < rest.length := by simpa using hk'
      obtain ⟨tx', receipt', hget, hri⟩ := hk k hk''
      refine ⟨tx', receipt', by simpa using hget, ?_⟩
      simp only [List.take_succ_cons, List.map_cons, List.getLast?_cons, Option.getD_some,
        List.sum_cons, List.getElem_cons_succ]
      rw [show index + (k + 1) = index + 1 + k by omega,
        show firstLog + (receipt.logs.length + (List.map (fun x => x.2.logs.length) (l.take k)).sum)
          = firstLog + receipt.logs.length + (List.map (fun x => x.2.logs.length) (l.take k)).sum
          by omega]
      exact hri

/-- The object of a receipt names the recipient of its transaction.

A creation has the address that the sender makes at its nonce, and a call has none. -/
theorem receiptInfo_contractAddress {r : BlockRecord} {config : ChainConfig}
    {index before firstLog : Nat} {tx : Transaction} {receipt : Receipt r.fork}
    {info : ReceiptInfo} (h : r.receiptInfo config index before firstLog tx receipt = .ok info) :
    info.to = tx.to ∧ (tx.to.isSome → info.contractAddress = none) ∧
      (tx.to = none → Evm.createAddress info.sender tx.nonce.toNat =
        .ok (info.contractAddress.getD default)) ∧
      (tx.to = none → info.contractAddress.isSome) := by
  unfold receiptInfo at h
  obtain ⟨ti, hti, h⟩ := bind_ok_iff.mp h
  obtain ⟨sender, hash, -, -, rfl⟩ := transactionInfo_eq_ok.mp hti
  rcases hto : tx.to with _ | a
  · rcases hc : (Evm.createAddress sender tx.nonce.toNat) with e | ca
    · simp [hto, hc, bind, Except.bind, Functor.map, Except.map, Except.mapError] at h
    · simp [hto, hc, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
        Except.mapError] at h
      subst h
      simp [hc]
  · simp [hto, bind, Except.bind, pure, Except.pure] at h
    subst h
    simp

/-- The object of a receipt holds the sender of the lookup of its transaction. -/
private theorem receiptInfo_transactionInfo {r : BlockRecord} {config : ChainConfig}
    {index before firstLog : Nat} {tx : Transaction} {receipt : Receipt r.fork}
    {info : ReceiptInfo} (h : r.receiptInfo config index before firstLog tx receipt = .ok info) :
    ∃ ti, r.transactionInfo index tx = .ok ti ∧ info.sender = ti.sender := by
  unfold receiptInfo at h
  obtain ⟨ti, hti, h⟩ := bind_ok_iff.mp h
  refine ⟨ti, hti, ?_⟩
  rcases hto : tx.to with _ | a
  · rcases hc : (Evm.createAddress ti.sender tx.nonce.toNat) with e | ca
    · simp [hto, hc, bind, Except.bind, Functor.map, Except.map, Except.mapError] at h
    · simp [hto, hc, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
        Except.mapError] at h
      subst h
      rfl
  · simp [hto, bind, Except.bind, pure, Except.pure] at h
    subst h
    rfl

/-- The object of a receipt has blob fields exactly for a blob transaction.

Its blob gas is `2^17` for each versioned hash of the transaction.

From Dencun, its price is the base fee per blob gas at the excess blob gas of the header.

That base fee follows the blob schedule of the chain at the number and timestamp of the block.

Before Dencun, the definition sets the price to 0. -/
theorem receiptInfo_blob {r : BlockRecord} {config : ChainConfig}
    {index before firstLog : Nat} {tx : Transaction} {receipt : Receipt r.fork}
    {info : ReceiptInfo} (h : r.receiptInfo config index before firstLog tx receipt = .ok info) :
    info.blob = match tx with
      | .blob t => some (2 ^ 17 * t.blobVersionedHashes.length,
          if hd : .dencun ≤ r.fork then
            Fees.BlobBaseFee.getBaseFeePerBlobGas
              (Fees.BlobBaseFee.chainBlobSchedule config r.fork r.block.header.number
                r.block.header.timestamp.toNat hd)
              (r.block.header.excessBlobGas hd).toNat
          else 0)
      | _ => none := by
  unfold receiptInfo at h
  obtain ⟨ti, -, h⟩ := bind_ok_iff.mp h
  rcases hto : tx.to with _ | a
  · rcases hc : (Evm.createAddress ti.sender tx.nonce.toNat) with e | ca
    · simp [hto, hc, bind, Except.bind, Functor.map, Except.map, Except.mapError] at h
    · simp [hto, hc, bind, Except.bind, pure, Except.pure, Functor.map, Except.map,
        Except.mapError] at h
      subst h
      rcases tx <;> rfl
  · simp [hto, bind, Except.bind, pure, Except.pure] at h
    subst h
    rcases tx <;> rfl

/-- The receipt objects of a block are one for each receipt, in order.

The object at index `k` is that of the transaction at `k` and its receipt. -/
theorem receiptInfos_eq_ok {r : BlockRecord} {config : ChainConfig} {infos : List ReceiptInfo}
    (h : r.receiptInfos config = .ok infos) :
    infos.length = r.receipts.length ∧ r.block.transactions.length = r.receipts.length ∧
      ∀ k (hk : k < infos.length), ∃ tx receipt, r.block.transactions[k]? = some tx ∧
        r.receipts[k]?.map Prod.snd = some receipt ∧
        r.receiptInfo config k (r.gasBefore k) (r.logsBefore k) tx receipt = .ok infos[k] := by
  unfold receiptInfos at h
  have hl : r.block.transactions.length = r.receipts.length := by
    by_cases hl : r.block.transactions.length = r.receipts.length
    · exact hl
    · simp [hl] at h
  simp only [hl, ↓reduceIte] at h
  obtain ⟨hlen, hk⟩ := receiptInfosFrom_eq_ok h
  have hzip : (r.block.transactions.zip (r.receipts.map (·.2))).length = r.receipts.length := by
    simp [hl]
  refine ⟨hlen.trans hzip, hl, fun k hk' => ?_⟩
  obtain ⟨tx, receipt, hget, hri⟩ := hk k hk'
  have htake : ∀ k, (((r.block.transactions.zip (r.receipts.map (·.2))).take k).map
      Prod.snd : List (Receipt r.fork)) = (r.receipts.take k).map (·.2) := by
    intro k
    have hz : ∀ {α β : Type} (a : List α) (b : List β), (a.zip b).take k =
        (a.take k).zip (b.take k) := fun a b => by simp [List.zip, List.take_zipWith]
    rw [hz, List.map_snd_zip, List.map_take]
    simp [hl]
  refine ⟨tx, receipt, (List.getElem?_zip_eq_some.mp hget).1, ?_, ?_⟩
  · have := (List.getElem?_zip_eq_some.mp hget).2
    simpa using this
  · have e1 : ((r.block.transactions.zip (r.receipts.map (·.2))).take k).map
        (·.2.cumulativeGasUsed) = (r.receipts.take k).map (·.2.cumulativeGasUsed) := by
      have := congrArg (List.map (·.cumulativeGasUsed)) (htake k)
      simpa [List.map_map, Function.comp_def] using this
    have e2 : ((r.block.transactions.zip (r.receipts.map (·.2))).take k).map
        (·.2.logs.length) = (r.receipts.take k).map (·.2.logs.length) := by
      have := congrArg (List.map (·.logs.length)) (htake k)
      simpa [List.map_map, Function.comp_def] using this
    rw [e1, e2] at hri
    simpa [gasBefore, logsBefore] using hri

/-- The logs of some objects are numbered in order from the first log. -/
private theorem logIndex_receiptInfosFrom {r : BlockRecord} {config : ChainConfig} :
    ∀ {l : List (Transaction × Receipt r.fork)} {infos : List ReceiptInfo}
      {index before firstLog : Nat},
      r.receiptInfosFrom config index before firstLog l = .ok infos →
      (infos.flatMap (·.logs)).map (·.logIndex) =
        (List.range (l.map (·.2.logs.length)).sum).map (firstLog + ·) := by
  intro l
  induction l with
  | nil =>
    intro infos index before firstLog h
    simp only [receiptInfosFrom] at h
    cases h
    simp
  | cons x l ih =>
    intro infos index before firstLog h
    obtain ⟨tx, receipt⟩ := x
    simp only [receiptInfosFrom] at h
    obtain ⟨info, hinfo, h⟩ := bind_ok_iff.mp h
    obtain ⟨rest, hrest, h⟩ := bind_ok_iff.mp h
    have h : info :: rest = infos := by simpa [pure, Except.pure] using h
    subst h
    obtain ⟨-, -, -, -, -, hlog, hidx, -⟩ := receiptInfo_eq_ok hinfo
    have hlen : info.logs.length = receipt.logs.length := by simpa using congrArg List.length hlog
    simp only [List.flatMap_cons, List.map_append, hidx, ih hrest, List.map_cons, List.sum_cons,
      List.range_add, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    simp
    omega

/-- The logs of the receipt objects of a block are numbered `0, 1, 2, …` in order. -/
theorem logIndex_receiptInfos {r : BlockRecord} {config : ChainConfig}
    {infos : List ReceiptInfo} (h : r.receiptInfos config = .ok infos) :
    (infos.flatMap (·.logs)).map (·.logIndex) = List.range (infos.flatMap (·.logs)).length := by
  unfold receiptInfos at h
  have hl : r.block.transactions.length = r.receipts.length := by
    by_cases hl : r.block.transactions.length = r.receipts.length
    · exact hl
    · simp [hl] at h
  simp only [hl, ↓reduceIte] at h
  have := logIndex_receiptInfosFrom h
  have hlen := congrArg List.length this
  simp only [List.length_map, List.length_range] at hlen
  rw [this, ← hlen]
  simp

/-- When the cumulative gas never decreases from `before`, the gas of some objects adds up. -/
private theorem sum_gasUsed_receiptInfosFrom {r : BlockRecord} {config : ChainConfig} :
    ∀ {l : List (Transaction × Receipt r.fork)} {infos : List ReceiptInfo}
      {index before firstLog : Nat},
      r.receiptInfosFrom config index before firstLog l = .ok infos →
      (before :: l.map (·.2.cumulativeGasUsed)).Pairwise (· ≤ ·) →
      (infos.map (·.gasUsed)).sum + before =
        ((infos.map (·.cumulativeGasUsed)).getLast?).getD before := by
  intro l
  induction l with
  | nil =>
    intro infos index before firstLog h _
    simp only [receiptInfosFrom] at h
    cases h
    simp
  | cons x l ih =>
    intro infos index before firstLog h hp
    obtain ⟨tx, receipt⟩ := x
    simp only [receiptInfosFrom] at h
    obtain ⟨info, hinfo, h⟩ := bind_ok_iff.mp h
    obtain ⟨rest, hrest, h⟩ := bind_ok_iff.mp h
    have h : info :: rest = infos := by simpa [pure, Except.pure] using h
    subst h
    obtain ⟨-, -, hcum, hgas, -⟩ := receiptInfo_eq_ok hinfo
    simp only [List.map_cons, List.pairwise_cons] at hp
    have hb : before ≤ receipt.cumulativeGasUsed := hp.1 _ (List.mem_cons_self ..)
    have := ih hrest (List.pairwise_cons.mpr hp.2)
    simp only [List.map_cons, List.sum_cons, List.getLast?_cons, Option.getD_some, hcum, hgas]
    omega

/-- When the cumulative gas of the receipts never decreases, the gas of the objects adds up.

The sum is the cumulative gas of the last object, or 0 for a block without transactions. -/
theorem sum_gasUsed_receiptInfos {r : BlockRecord} {config : ChainConfig}
    {infos : List ReceiptInfo} (h : r.receiptInfos config = .ok infos)
    (hmono : (r.receipts.map (·.2.cumulativeGasUsed)).Pairwise (· ≤ ·)) :
    (infos.map (·.gasUsed)).sum = ((infos.map (·.cumulativeGasUsed)).getLast?).getD 0 := by
  unfold receiptInfos at h
  have hl : r.block.transactions.length = r.receipts.length := by
    by_cases hl : r.block.transactions.length = r.receipts.length
    · exact hl
    · simp [hl] at h
  simp only [hl, ↓reduceIte] at h
  have e : (r.block.transactions.zip (r.receipts.map (·.2))).map (·.2.cumulativeGasUsed) =
      r.receipts.map (·.2.cumulativeGasUsed) := by
    have := congrArg (List.map fun p : Receipt r.fork => p.cumulativeGasUsed)
      (List.map_snd_zip (l₁ := r.block.transactions) (l₂ := r.receipts.map (·.2))
        (by simp [hl]))
    simpa [List.map_map, Function.comp_def] using this
  have := sum_gasUsed_receiptInfosFrom h (by
    rw [e, List.pairwise_cons]
    exact ⟨fun _ _ => Nat.zero_le _, hmono⟩)
  simpa using this

end BlockRecord

/-- From Byzantium, the outcome of a receipt is a status.

It is `true` exactly when the receipt is a success. -/
theorem outcomeOf_of_byzantium {fork : Fork} (h : .byzantium ≤ fork) (o : Outcome fork) :
    ∃ b, outcomeOf o = .inr b ∧ (b = true ↔ o = .status h true) := by
  cases o with
  | postState before root => exact absurd (Nat.lt_of_lt_of_le before h) (Nat.lt_irrefl _)
  | status since succeeded =>
    refine ⟨succeeded, rfl, ?_⟩
    cases succeeded <;> simp

/-- Before Byzantium, the outcome of a receipt is the state root after the transaction. -/
theorem outcomeOf_of_lt_byzantium {fork : Fork} (h : fork < .byzantium) (o : Outcome fork) :
    ∃ root, outcomeOf o = .inl root ∧ o = .postState h root := by
  cases o with
  | postState before root => exact ⟨root, rfl, rfl⟩
  | status since succeeded => exact absurd (Nat.lt_of_lt_of_le h since) (Nat.lt_irrefl _)

/-- The effective gas price agrees with the formula of the description, in integers.

A legacy or EIP-2930 transaction pays its gas price.

Any other transaction pays the base fee plus a priority part.

That part is the least of the maximum fee minus the base fee, and the maximum priority fee.

The formula holds when the base fee is at most the maximum fee. -/
theorem effectiveGasPrice_description {baseFee : Nat} {tx : Transaction}
    (h : baseFee ≤ tx.maxFeePerGas) :
    (effectiveGasPrice baseFee tx : Int) = match (generalizing := false) tx with
      | .legacy t | .accessList t => t.gasPrice.toNat
      | .feeMarket t | .blob t | .setCode t =>
        baseFee + min ((t.maxFeePerGas.toNat : Int) - baseFee) t.maxPriorityFeePerGas.toNat := by
  rcases tx with t | t | t | t | t <;>
    simp only [Transaction.maxFeePerGas] at h <;>
    simp only [effectiveGasPrice, effectiveGasPrice.feeMarket] <;> omega

/-- The receipts of the transactions of a body have the Bloom filters of their logs.

Their cumulative gas never decreases, and stays at most the cumulative gas of the output. -/
private theorem applyTransactions_receipts {fork : Fork} {env : Evm.BlockEnvironment fork}
    {body : BodyState} {transactions : List Transaction} {output : BodyOutput fork}
    (h : applyTransactions env body transactions = .ok output) :
    (∀ p ∈ output.receipts, p.2.bloom = logsBloom p.2.logs) ∧
      (output.receipts.map (·.2.cumulativeGasUsed)).Pairwise (· ≤ ·) ∧
      ∀ p ∈ output.receipts, p.2.cumulativeGasUsed ≤ output.cumulativeGasUsed := by
  have step : ∀ {index : Nat} {before after : BodyOutput fork} {tx : Transaction},
      applyTransaction env index before tx = .ok after →
      (((∀ p ∈ before.receipts, p.2.bloom = logsBloom p.2.logs) ∧
        (before.receipts.map (fun p : UInt8 × Receipt fork => p.2.cumulativeGasUsed)).Pairwise
          (· ≤ ·) ∧
        ∀ p ∈ before.receipts, p.2.cumulativeGasUsed ≤ before.cumulativeGasUsed) →
      ((∀ p ∈ after.receipts, p.2.bloom = logsBloom p.2.logs) ∧
        (after.receipts.map (fun p : UInt8 × Receipt fork => p.2.cumulativeGasUsed)).Pairwise
          (· ≤ ·) ∧
        ∀ p ∈ after.receipts, p.2.cumulativeGasUsed ≤ after.cumulativeGasUsed)) := by
    intro index before after tx hstep hinv
    obtain ⟨outcome, logs, hr⟩ := applyTransaction_receipts hstep
    obtain ⟨_, _, -, -, -, hcum, -⟩ := applyTransaction_eq_ok hstep
    obtain ⟨hb, hp, hl⟩ := hinv
    have hle : before.cumulativeGasUsed ≤ after.cumulativeGasUsed := by omega
    rw [hr]
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hb p hp
      · cases List.mem_singleton.mp hp
        exact bloom_makeReceipt ..
    · simp only [List.map_append, List.pairwise_append]
      refine ⟨hp, by simp, ?_⟩
      intro a ha b hb'
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
      subst hb'
      exact Nat.le_trans (hl q hq) hle
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact Nat.le_trans (hl p hp) hle
      · cases List.mem_singleton.mp hp
        exact Nat.le_refl _
  obtain ⟨hR, -⟩ := applyTransactions_steps
    (fun a b : BodyOutput fork =>
      ((∀ p ∈ a.receipts, p.2.bloom = logsBloom p.2.logs) ∧
        (a.receipts.map (fun p : UInt8 × Receipt fork => p.2.cumulativeGasUsed)).Pairwise
          (· ≤ ·) ∧
        ∀ p ∈ a.receipts, p.2.cumulativeGasUsed ≤ a.cumulativeGasUsed) →
      ((∀ p ∈ b.receipts, p.2.bloom = logsBloom p.2.logs) ∧
        (b.receipts.map (fun p : UInt8 × Receipt fork => p.2.cumulativeGasUsed)).Pairwise
          (· ≤ ·) ∧
        ∀ p ∈ b.receipts, p.2.cumulativeGasUsed ≤ b.cumulativeGasUsed))
    (fun _ => id) (fun h₁ h₂ x => h₂ (h₁ x)) step h
  exact hR (by simp)

/-- A transaction that runs has its sender buy the gas first, on the block state it runs on. -/
private theorem processTransaction_buyGas {fork : Fork} {env : Evm.BlockEnvironment fork}
    {block : State.BlockState} {included : Included} {tx : Transaction}
    {out : TransactionOutput} (h : processTransaction env block included tx = .ok out) :
    ∃ bought, buyGas env (.ofBlock block) included.sender tx = .ok bought := by
  unfold processTransaction at h
  split at h
  · cases h
  split at h
  · obtain ⟨_, bought, _, _, _, -, hb, -⟩ := runTransaction_eq_ok h
    exact ⟨bought, hb⟩
  · obtain ⟨_, bought, _, _, _, -, hb, -⟩ := runTransaction_eq_ok h
    exact ⟨bought, hb⟩

namespace ChainView

/-- In a valid view, the receipts of a canonical block after the lowest are those of its run. -/
private theorem Valid.receipts_run {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) :
    ∃ env body txs, applyTransactions env body v.canonical[i + 1].block.transactions = .ok txs ∧
      txs.receipts = v.canonical[i + 1].receipts := by
  obtain ⟨-, result, hrun, hrec, -⟩ := hv.follows i hi
  obtain ⟨hashes, -, happly, -⟩ := Blocks.runBody_eq_ok.mp hrun
  obtain ⟨-, body, txs, -, -, htxs, hr⟩ := applyBody_receipts happly
  exact ⟨_, body, txs, htxs, hr ▸ hrec⟩

/-- The receipt of a transaction is the object at its index among those of its block. -/
theorem transactionReceipt_eq_ok {v : ChainView} {hash : Hash32} {info : ReceiptInfo}
    (h : v.transactionReceipt hash = .ok (some info)) :
    ∃ r tx index infos, v.findTransaction hash = some (r, tx, index) ∧
      r.receiptInfos v.config = .ok infos ∧ infos[index]? = some info := by
  unfold transactionReceipt at h
  rcases hf : v.findTransaction hash with _ | ⟨r, tx, index⟩
  · simp [hf] at h
  · simp only [hf] at h
    obtain ⟨infos, hinfos, h⟩ := bind_ok_iff.mp h
    exact ⟨r, tx, index, infos, rfl, hinfos, by simpa [pure, Except.pure] using h⟩

/-- The receipts of a block are the receipt objects of the block that the parameter names. -/
theorem blockReceipts_of_resolve {v : ChainView} {p : BlockParam} {r : BlockRecord}
    (h : v.resolve p = .ok (some r)) :
    v.blockReceipts p = some <$> r.receiptInfos v.config := by
  unfold blockReceipts
  simp [h, bind, Except.bind]

/-- In a valid view, take a canonical block after the lowest.

Each of its receipts has the Bloom filter of its logs. -/
theorem Valid.bloom_receipts {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) {i : Nat}
    (hi : i + 1 < v.canonical.length) :
    ∀ p : UInt8 × Receipt v.canonical[i + 1].fork, p ∈ v.canonical[i + 1].receipts →
      p.2.bloom = logsBloom p.2.logs := by
  obtain ⟨env, body, txs, htxs, hr⟩ := hv.receipts_run hi
  rw [← hr]
  exact (applyTransactions_receipts htxs).1

/-- In a valid view, take a canonical block after the lowest.

The cumulative gas of its receipts never decreases. -/
theorem Valid.cumulativeGasUsed_receipts {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length) :
    (v.canonical[i + 1].receipts.map (·.2.cumulativeGasUsed)).Pairwise (· ≤ ·) := by
  obtain ⟨env, body, txs, htxs, hr⟩ := hv.receipts_run hi
  rw [← hr]
  exact (applyTransactions_receipts htxs).2.1

/-- In a valid view, take a canonical block after the lowest.

Its base fee is at most the maximum fee of each of its transactions. -/
theorem Valid.baseFee_le_maxFeePerGas {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length) :
    ∀ tx ∈ v.canonical[i + 1].block.transactions,
      v.canonical[i + 1].baseFee ≤ tx.maxFeePerGas := by
  intro tx htx
  obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem htx
  obtain ⟨hashes, -, -, before, next, -, -, -, -, hnext⟩ :=
    hv.applyTransaction_at hi (List.getElem?_eq_some_iff.mpr ⟨hindex, hget⟩)
  obtain ⟨inc, -, hinc, -⟩ := Blocks.applyTransaction_eq_ok hnext
  have h1 := checkInclusion_baseFee_le hinc
  have h2 := checkInclusion_gasPrice_le hinc
  have hbf : v.canonical[i + 1].baseFee = baseFeeOf (blockEnvironment v.config hashes
      v.canonical[i + 1].block.header) := by
    simp [baseFeeOf, BlockRecord.baseFee, blockEnvironment]
  rw [hbf]
  exact Nat.le_trans h1 h2

/-- In a valid view, take a canonical block after the lowest.

Each of its receipt objects has the Bloom filter of its logs. -/
theorem Valid.logsBloom_receiptInfos {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal)
    {i : Nat} (hi : i + 1 < v.canonical.length) {infos : List ReceiptInfo}
    (h : v.canonical[i + 1].receiptInfos v.config = .ok infos) :
    ∀ info ∈ infos, info.logsBloom = logsBloom (info.logs.map (·.log)) := by
  intro info hinfo
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hinfo
  obtain ⟨-, -, hall⟩ := BlockRecord.receiptInfos_eq_ok h
  obtain ⟨tx, receipt, -, hrec, hri⟩ := hall k hk
  obtain ⟨-, -, -, -, hbloom, hlogs, -⟩ := BlockRecord.receiptInfo_eq_ok hri
  obtain ⟨p, hp, hpr⟩ := Option.map_eq_some_iff.mp hrec
  cases hpr
  rw [hbloom, hlogs]
  exact hv.bloom_receipts hi p (List.mem_of_getElem? hp)

/-- In a valid view, take a canonical block after the lowest.

The gas of its receipt objects adds up to the cumulative gas of the last one. -/
theorem Valid.sum_gasUsed {v : ChainView} {checkSeal : Bool} (hv : v.Valid checkSeal) {i : Nat}
    (hi : i + 1 < v.canonical.length) {infos : List ReceiptInfo}
    (h : v.canonical[i + 1].receiptInfos v.config = .ok infos) :
    (infos.map (·.gasUsed)).sum = ((infos.map (·.cumulativeGasUsed)).getLast?).getD 0 :=
  BlockRecord.sum_gasUsed_receiptInfos h (hv.cumulativeGasUsed_receipts hi)

/-- In a valid view, take a canonical block after the lowest.

Each of its receipt objects has the effective gas price of the formula of the description.

The formula reads in integers at the base fee of the block, which is at most the maximum fee. -/
theorem Valid.effectiveGasPrice_receiptInfos {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length)
    {infos : List ReceiptInfo} (h : v.canonical[i + 1].receiptInfos v.config = .ok infos)
    {k : Nat} {tx : Transaction} {info : ReceiptInfo}
    (htx : v.canonical[i + 1].block.transactions[k]? = some tx) (hinfo : infos[k]? = some info) :
    (info.effectiveGasPrice : Int) = match (generalizing := false) tx with
      | .legacy t | .accessList t => t.gasPrice.toNat
      | .feeMarket t | .blob t | .setCode t => v.canonical[i + 1].baseFee +
          min ((t.maxFeePerGas.toNat : Int) - v.canonical[i + 1].baseFee)
            t.maxPriorityFeePerGas.toNat := by
  obtain ⟨hk', hinfo'⟩ := List.getElem?_eq_some_iff.mp hinfo
  obtain ⟨-, -, hall⟩ := BlockRecord.receiptInfos_eq_ok h
  obtain ⟨tx', receipt, htx', -, hri⟩ := hall k hk'
  rw [htx] at htx'
  cases htx'
  obtain ⟨-, -, -, -, -, -, -, -, hprice⟩ := BlockRecord.receiptInfo_eq_ok hri
  cases hinfo'
  rw [hprice]
  exact effectiveGasPrice_description (hv.baseFee_le_maxFeePerGas hi tx (List.mem_of_getElem? htx))

/-- In a valid view, take a canonical block after the lowest, and a receipt object of it.

The run of the block reached its transaction after those before it.

On the state that the transaction starts from, the sender can buy its gas.

Buying it lowers its balance by exactly the gas limit of the transaction times a price.

That price is the effective gas price of the object.

A blob transaction adds the blob gas of the object times its price per blob gas. -/
theorem Valid.buyGas_receiptInfos {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i + 1 < v.canonical.length)
    {infos : List ReceiptInfo} (h : v.canonical[i + 1].receiptInfos v.config = .ok infos)
    {k : Nat} {tx : Transaction} {info : ReceiptInfo}
    (htx : v.canonical[i + 1].block.transactions[k]? = some tx) (hinfo : infos[k]? = some info) :
    ∃ hashes state body, ∃ before : BodyOutput v.canonical[i + 1].fork, ∃ bought,
      recentHashes (v.chainAt i (by omega)).recent = .ok hashes ∧
      daoTransfer v.config v.canonical[i + 1].fork v.canonical[i + 1].block.header.number
        ⟨v.canonical[i].state, ∅, ∅, ∅, ∅⟩ = .ok state ∧
      startSystemCalls (blockEnvironment v.config hashes v.canonical[i + 1].block.header)
        v.canonical[i + 1].block.header.parentHash (.init state) = .ok body ∧
      applyTransactions (blockEnvironment v.config hashes v.canonical[i + 1].block.header) body
        (v.canonical[i + 1].block.transactions.take k) = .ok before ∧
      buyGas (blockEnvironment v.config hashes v.canonical[i + 1].block.header)
        (.ofBlock before.block) info.sender tx = .ok bought ∧
      (bought.getAccount info.sender).balance.toNat + tx.gas.toNat * info.effectiveGasPrice +
          (info.blob.map fun (used, price) => used * price).getD 0 =
        ((State.TransactionState.ofBlock before.block).getAccount info.sender).balance.toNat := by
  obtain ⟨hk', hinfo'⟩ := List.getElem?_eq_some_iff.mp hinfo
  obtain ⟨-, -, hall⟩ := BlockRecord.receiptInfos_eq_ok h
  obtain ⟨tx', receipt, htx', -, hri⟩ := hall k hk'
  rw [htx] at htx'
  cases htx'
  rw [hinfo'] at hri
  obtain ⟨-, -, -, -, -, -, -, -, hprice⟩ := BlockRecord.receiptInfo_eq_ok hri
  have hblob := BlockRecord.receiptInfo_blob hri
  obtain ⟨ti, hti, hsender⟩ := BlockRecord.receiptInfo_transactionInfo hri
  obtain ⟨sender, hash, hs, -, hti2⟩ := BlockRecord.transactionInfo_eq_ok.mp hti
  rw [hti2] at hsender
  dsimp only at hsender
  obtain ⟨hashes, state, body, before, next, hrec, hdao, hstart, hbefore, hnext⟩ :=
    hv.applyTransaction_at hi htx
  obtain ⟨inc, out, hinc, hout, -⟩ := Blocks.applyTransaction_eq_ok hnext
  have hincs : inc.sender = sender := Except.ok.inj ((checkInclusion_ok hinc).1.symm.trans hs)
  obtain ⟨bought, hbought⟩ := processTransaction_buyGas hout
  rw [hincs] at hbought
  rw [hsender]
  refine ⟨hashes, state, body, before, bought, hrec, hdao, hstart, hbefore, hbought, ?_⟩
  have hbase : v.canonical[i + 1].baseFee = baseFeeOf (blockEnvironment v.config hashes
      v.canonical[i + 1].block.header) := by
    simp [baseFeeOf, BlockRecord.baseFee, blockEnvironment]
  have hfee : tx.gas.toNat * info.effectiveGasPrice +
      (info.blob.map fun (used, price) => used * price).getD 0 =
      tx.gas.toNat * effectiveGasPrice (baseFeeOf (blockEnvironment v.config hashes
        v.canonical[i + 1].block.header)) tx +
      Fees.BlobBaseFee.calculateTotalBlobGas tx * blobGasPriceOf (blockEnvironment v.config hashes
        v.canonical[i + 1].block.header) := by
    rw [hprice, hbase, hblob]
    rcases tx with t | t | t | t | t <;>
      simp [Fees.BlobBaseFee.calculateTotalBlobGas, Fees.BlobBaseFee.GAS_PER_BLOB,
        blobGasPriceOf, blockEnvironment, Evm.BlockEnvironment.blobBaseFee]
  obtain ⟨hle, hbal, -⟩ := buyGas_sender hfee hbought
  omega

/-- In a valid view, take a transaction that a lookup finds in a canonical block.

Its receipt is the object at its index among the receipts of the number of that block. -/
theorem Valid.transactionReceipt_blockReceipts {v : ChainView} {checkSeal : Bool}
    (hv : v.Valid checkSeal) {i : Nat} (hi : i < v.canonical.length) {hash : Hash32}
    {tx : Transaction} {index : Nat} {info : ReceiptInfo}
    (hf : v.findTransaction hash = some (v.canonical[i], tx, index))
    (h : v.transactionReceipt hash = .ok (some info)) :
    ∃ infos, v.blockReceipts (.number v.canonical[i].block.header.number) = .ok (some infos) ∧
      infos[index]? = some info := by
  obtain ⟨r, tx', index', infos, hf', hinfos, hget⟩ := transactionReceipt_eq_ok h
  rw [hf] at hf'
  obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj hf'
  have hres : v.resolve (.number v.canonical[i].block.header.number) =
      .ok (some v.canonical[i]) := by
    cases hb : v.byNumber v.canonical[i].block.header.number with
    | none =>
      have := List.find?_eq_none.mp hb _ (List.getElem_mem hi)
      simp at this
    | some r' =>
      obtain ⟨hmem, hnum⟩ := ChainView.resolve_number
        (v := v) (n := v.canonical[i].block.header.number) (r := r') (by simp [resolve, hb])
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hmem
      rw [hv.number j hj, hv.number i hi] at hnum
      have : j = i := by omega
      subst this
      simp [resolve, hb]
  refine ⟨infos, ?_, hget⟩
  rw [blockReceipts_of_resolve hres, hinfos]
  rfl

end ChainView

end EthLib.Execution.Rpc
