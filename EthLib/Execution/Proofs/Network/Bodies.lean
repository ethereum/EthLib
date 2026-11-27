module

public import EthLib.Execution.Network.Bodies
public import EthLib.Execution.Proofs.Blocks.Roots
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Network.Blocks
public import EthLib.Execution.Proofs.Blocks.BodyGas
public import EthLib.Execution.Proofs.Blocks.Ommers
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.TypedRoots
public import EthLib.Execution.Proofs.Blocks.Validate
public import EthLib.Execution.Proofs.Transactions.Envelope
public import EthLib.Serialization.Proofs.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.Encodings
public import EthLib.Serialization.Proofs.Rlp.RoundTrip
import EthLib.Base.Proofs.CodeInjective

/-!
# Proofs: the check of a block body

The body of every block that passes the state transition passes the check against its header.

Two bodies that keep their encodings and pass for one header are equal in each part.

Otherwise a Keccak-256 collision is named.
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Serialization.Rlp
open EthLib.Execution.Blocks
open EthLib.Execution.Transactions
open EthLib.Execution.State (State)

variable {fork : Fork}

/-- Two errors with one code come from one constructor. -/
theorem BodyError.code_injective (e₁ e₂ : BodyError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  code_injective BodyError.code

/-! ## The checks with a plain hash -/

/-- The check of the transactions, with a plain hash. -/
theorem checkTransactionsM_eq (hash : ByteArray → Hash32) (header : Header fork)
    (transactions : Encoded) :
    (checkTransactionsM (m := Id) hash header transactions).run = (do
      let values ← transactionValues transactions
      let root ← ((indexedRootM (m := Id) hash values).run).mapError .trie
      ensure (root == header.transactionsRoot) (.wrongTransactionsRoot header.transactionsRoot root)
      checkGasLimits header transactions.item : Except BodyError Unit) := by
  simp only [checkTransactionsM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift,
    exceptT_id_adapt, except_bind_eq]

/-- The check of the withdrawals, with a plain hash. -/
theorem checkWithdrawalsM_eq (hash : ByteArray → Hash32) (header : Header fork)
    (h : .shapella ≤ fork) (withdrawals : Item) :
    (checkWithdrawalsM (m := Id) hash header h withdrawals).run = (do
      let ws : List Withdrawal ← (Codec.ofItem withdrawals).mapError .decoding
      let root ← ((withdrawalsRootM (m := Id) hash ws).run).mapError .trie
      ensure (root == header.withdrawalsRoot h)
        (.wrongWithdrawalsRoot (header.withdrawalsRoot h) root) : Except BodyError Unit) := by
  simp only [checkWithdrawalsM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift,
    exceptT_id_adapt, except_bind_eq]

/-- The check of the ommers, with a plain hash. -/
theorem checkOmmersM_eq (hash : ByteArray → Hash32) (header : Header fork) (ommers : Encoded) :
    (checkOmmersM (m := Id) hash header ommers).run = (do
      let items ← ommers.item.toItems.mapError .decoding
      ensure (items.length ≤ MAX_OMMERS) (.tooManyOmmers items.length)
      ensure (hash ommers.bytes == header.ommersHash)
        (.wrongOmmersHash header.ommersHash (hash ommers.bytes))
      (List.range items.length).zip items |>.forM fun (i, ommer) => do
        let n ← (headerNumber ommer).mapError .decoding
        ensure (n ≤ header.number) (.ommerAfterBlock i n) : Except BodyError Unit) := by
  simp only [checkOmmersM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift, exceptT_id_lift,
    except_bind_eq]
  cases ommers.item.toItems with
  | error => rfl
  | ok items => rfl

/-- The check of a body, with a plain hash. -/
theorem checkBodyM_eq (hash : ByteArray → Hash32) (header : Header fork) (body : Encoded) :
    (checkBodyM (m := Id) hash header body).run = (do
      let items ← body.parts.mapError .decoding
      if h : .shapella ≤ fork then
        match items with
        | [transactions, ommers, withdrawals] => do
          (checkTransactionsM (m := Id) hash header transactions).run
          (checkWithdrawalsM (m := Id) hash header h withdrawals.item).run
          (checkOmmersM (m := Id) hash header ommers).run
        | [_, _] => throw .missingWithdrawals
        | _ => throw (.decoding (.wrongFieldCount 3 items.length))
      else
        match items with
        | [transactions, ommers] => do
          (checkTransactionsM (m := Id) hash header transactions).run
          (checkOmmersM (m := Id) hash header ommers).run
        | [_, _, _] => throw .unexpectedWithdrawals
        | _ => throw (.decoding (.wrongFieldCount 2 items.length))
      : Except BodyError Unit) := by
  simp only [checkBodyM, ExceptT.run, exceptT_id_bind, exceptT_id_monadLift, except_bind_eq]
  cases body.parts with
  | error => rfl
  | ok items =>
    by_cases hf : .shapella ≤ fork
    · simp only [Except.mapError, Except.bind, hf, ↓reduceDIte]
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> rfl
    · simp only [Except.mapError, Except.bind, hf, ↓reduceDIte]
      rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> rfl

/-- The check of the ommers, with Keccak-256. -/
theorem checkOmmers_eq (header : Header fork) (ommers : Encoded) :
    checkOmmers header ommers = (do
      let items ← ommers.item.toItems.mapError .decoding
      ensure (items.length ≤ MAX_OMMERS) (.tooManyOmmers items.length)
      ensure (Cryptography.Hash.Keccak.keccak256 ommers.bytes == header.ommersHash)
        (.wrongOmmersHash header.ommersHash (Cryptography.Hash.Keccak.keccak256 ommers.bytes))
      (List.range items.length).zip items |>.forM fun (i, ommer) => do
        let n ← (headerNumber ommer).mapError .decoding
        ensure (n ≤ header.number) (.ommerAfterBlock i n) : Except BodyError Unit) :=
  checkOmmersM_eq _ header ommers

/-- The check of a body, with Keccak-256. -/
theorem checkBody_eq (header : Header fork) (body : Encoded) :
    checkBody header body = (do
      let items ← body.parts.mapError .decoding
      if h : .shapella ≤ fork then
        match items with
        | [transactions, ommers, withdrawals] => do
          checkTransactions header transactions
          checkWithdrawals header h withdrawals.item
          checkOmmers header ommers
        | [_, _] => throw .missingWithdrawals
        | _ => throw (.decoding (.wrongFieldCount 3 items.length))
      else
        match items with
        | [transactions, ommers] => do
          checkTransactions header transactions
          checkOmmers header ommers
        | [_, _, _] => throw .unexpectedWithdrawals
        | _ => throw (.decoding (.wrongFieldCount 2 items.length)) : Except BodyError Unit) :=
  checkBodyM_eq _ header body

/-- An ommers list of more than `MAX_OMMERS` items is rejected, whatever its items and bytes. -/
theorem checkOmmers_tooMany {header : Header fork} {items : List Item} {bytes : ByteArray}
    (h : MAX_OMMERS < items.length) :
    checkOmmers header ⟨.list items, bytes⟩ = .error (.tooManyOmmers items.length) := by
  have hn : ¬ items.length ≤ MAX_OMMERS := Nat.not_le.mpr h
  simp only [checkOmmers_eq, Item.toItems, Except.mapError, ensure, bind, Except.bind, hn,
    ite_false]

/-- The empty ommers list, read from its encoding, is accepted when the header commits to it. -/
theorem checkOmmers_nil {header : Header fork} (h : header.ommersHash = EMPTY_OMMER_HASH) :
    checkOmmers header ⟨.list [], ⟨#[0xc0]⟩⟩ = .ok () := by
  simp only [checkOmmers_eq, Item.toItems, Except.mapError, ensure, bind, Except.bind, h,
    EMPTY_OMMER_HASH, MAX_OMMERS, List.length_nil, Nat.zero_le, ite_true, beq_self_eq_true,
    List.range_zero, List.zip_nil_left]
  rfl

/-- Before Shapella, a body of three items, read from its encoding, is rejected for its withdrawals.
-/
theorem checkBody_unexpectedWithdrawals (hfork : ¬ .shapella ≤ fork) {header : Header fork}
    {a b c : Item} {bytes : ByteArray} (hb : encode (.list [a, b, c]) = .ok bytes) :
    checkBody header ⟨.list [a, b, c], bytes⟩ = .error .unexpectedWithdrawals := by
  obtain ⟨kept, hp, hk, -⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
  rcases kept with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, rest⟩⟩⟩⟩ <;> simp at hk
  simp only [checkBody_eq, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte]
  rfl

/-- From Shapella, a body of two items, read from its encoding, is rejected for its withdrawals. -/
theorem checkBody_missingWithdrawals (hfork : .shapella ≤ fork) {header : Header fork}
    {a b : Item} {bytes : ByteArray} (hb : encode (.list [a, b]) = .ok bytes) :
    checkBody header ⟨.list [a, b], bytes⟩ = .error .missingWithdrawals := by
  obtain ⟨kept, hp, hk, -⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
  rcases kept with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp at hk
  simp only [checkBody_eq, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte]
  rfl

/-- Before Shapella, a body with three ommers is rejected once the earlier checks pass.

The body is read from its encoding, and the transactions keep their own encoding. -/
theorem checkBody_tooManyOmmers (hfork : ¬ .shapella ≤ fork) {header : Header fork}
    {transactions : Item} {tbytes bytes : ByteArray} {ommers : List Item}
    (hlen : ommers.length = 3) (ht : encode transactions = .ok tbytes)
    (htx : checkTransactions header ⟨transactions, tbytes⟩ = .ok ())
    (hb : encode (.list [transactions, .list ommers]) = .ok bytes) :
    checkBody header ⟨.list [transactions, .list ommers], bytes⟩ = .error (.tooManyOmmers 3) := by
  obtain ⟨kept, hp, hk, he⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
  rcases kept with _ | ⟨⟨xi, xb⟩, _ | ⟨⟨yi, yb⟩, _ | ⟨_, _⟩⟩⟩ <;> simp at hk
  obtain ⟨rfl, rfl⟩ := hk
  -- The transactions are paired with their own encoding.
  obtain rfl : xb = tbytes := Except.ok.inj ((he ⟨xi, xb⟩ (by simp)).symm.trans ht)
  have hom := checkOmmers_tooMany (header := header) (items := ommers) (bytes := yb)
    (by simp [MAX_OMMERS, hlen])
  rw [hlen] at hom
  simp only [checkBody_eq, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte, htx, hom]

/-- From Shapella, a body with three ommers is rejected once the earlier checks pass.

The body is read from its encoding, and the transactions keep their own encoding. -/
theorem checkBody_tooManyOmmers_shapella (hfork : .shapella ≤ fork) {header : Header fork}
    {transactions withdrawals : Item} {tbytes bytes : ByteArray} {ommers : List Item}
    (hlen : ommers.length = 3) (ht : encode transactions = .ok tbytes)
    (htx : checkTransactions header ⟨transactions, tbytes⟩ = .ok ())
    (hw : checkWithdrawals header hfork withdrawals = .ok ())
    (hb : encode (.list [transactions, .list ommers, withdrawals]) = .ok bytes) :
    checkBody header ⟨.list [transactions, .list ommers, withdrawals], bytes⟩ =
      .error (.tooManyOmmers 3) := by
  obtain ⟨kept, hp, hk, he⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
  rcases kept with _ | ⟨⟨xi, xb⟩, _ | ⟨⟨yi, yb⟩, _ | ⟨⟨zi, zb⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hk
  obtain ⟨rfl, rfl, rfl⟩ := hk
  -- The transactions are paired with their own encoding.
  obtain rfl : xb = tbytes := Except.ok.inj ((he ⟨xi, xb⟩ (by simp)).symm.trans ht)
  have hom := checkOmmers_tooMany (header := header) (items := ommers) (bytes := yb)
    (by simp [MAX_OMMERS, hlen])
  rw [hlen] at hom
  simp only [checkBody_eq, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte, htx, hw, hom]

/-! ## What a passing check says -/

/-- The gas limits pass exactly when the transactions are a list of transactions of the fork.

The gas limit of each is at most that of the header. -/
theorem checkGasLimits_eq_ok_iff {header : Header fork} {transactions : Item} :
    checkGasLimits header transactions = .ok () ↔
      ∃ items, transactions = .list items ∧ ∀ item ∈ items, ∃ tx,
        decodeBodyTransaction fork item = .ok tx ∧ tx.gas.toNat ≤ header.gasLimit := by
  -- The check of one item: it decodes, and its gas limit fits.
  have step : ∀ (i : Nat) (item : Item),
      (do
        let tx ← (decodeBodyTransaction fork item).mapError (BodyError.invalidTransaction i)
        ensure (tx.gas.toNat ≤ header.gasLimit)
          (BodyError.gasLimitAboveBlock i tx.gas.toNat header.gasLimit)) = .ok () ↔
        ∃ tx, decodeBodyTransaction fork item = .ok tx ∧ tx.gas.toNat ≤ header.gasLimit := by
    intro i item
    cases hd : decodeBodyTransaction fork item with
    | error e => simp [Except.mapError, bind, Except.bind]
    | ok tx =>
      by_cases hg : tx.gas.toNat ≤ header.gasLimit <;>
        simp [Except.mapError, bind, Except.bind, ensure, hg]
  unfold checkGasLimits
  cases hi : transactions.toItems with
  | error e =>
    simp only [Except.mapError, bind, Except.bind, reduceCtorEq, false_iff, not_exists, not_and]
    intro items h
    simp [h, Item.toItems] at hi
  | ok items =>
    rw [Item.toItems_eq_ok.mp hi]
    simp only [Except.mapError, bind, Except.bind, Item.list.injEq, exists_eq_left']
    rw [forM_ok_iff]
    constructor
    · intro h item hmem
      obtain ⟨i, hlt, rfl⟩ := List.getElem_of_mem hmem
      have hz : (i, items[i]) ∈ (List.range items.length).zip items := by
        have hlen : i < ((List.range items.length).zip items).length := by simp [hlt]
        simpa using List.getElem_mem hlen
      exact (step i items[i]).mp (h _ hz)
    · intro h p hp
      exact (step p.1 p.2).mpr (h p.2 (List.of_mem_zip hp).2)

/-- The transactions pass exactly when their bytes have the transactions root of the header.

Each of them must also decode at the fork, with a gas limit at most that of the header.

The hash is any plain hash. -/
theorem checkTransactionsM_eq_ok_iff (hash : ByteArray → Hash32) {header : Header fork}
    {transactions : Encoded} :
    (checkTransactionsM (m := Id) hash header transactions).run = .ok () ↔
      (∃ values, transactionValues transactions = .ok values ∧
        (indexedRootM (m := Id) hash values).run = .ok header.transactionsRoot) ∧
      checkGasLimits header transactions.item = .ok () := by
  rw [checkTransactionsM_eq]
  cases hv : transactionValues transactions with
  | error e => simp [bind, Except.bind]
  | ok values =>
    cases hr : (indexedRootM (m := Id) hash values).run with
    | error e => simp [Except.mapError, bind, Except.bind, hr]
    | ok root =>
      by_cases h : root = header.transactionsRoot
      · subst h; simp [Except.mapError, bind, Except.bind, ensure, hr]
      · simp [Except.mapError, bind, Except.bind, ensure, hr, h]
        exact fun heq => absurd (Except.ok.inj heq) h

/-- The transactions pass exactly when their bytes have the transactions root of the header.

Each of them must also decode at the fork, with a gas limit at most that of the header. -/
theorem checkTransactions_eq_ok_iff {header : Header fork} {transactions : Encoded} :
    checkTransactions header transactions = .ok () ↔
      (∃ values, transactionValues transactions = .ok values ∧
        indexedRoot values = .ok header.transactionsRoot) ∧
      checkGasLimits header transactions.item = .ok () :=
  checkTransactionsM_eq_ok_iff _

/-- The withdrawals pass exactly when they decode to a list with the root of the header.

The hash is any plain hash. -/
theorem checkWithdrawalsM_eq_ok_iff (hash : ByteArray → Hash32) {header : Header fork}
    {h : .shapella ≤ fork} {withdrawals : Item} :
    (checkWithdrawalsM (m := Id) hash header h withdrawals).run = .ok () ↔
      ∃ ws : List Withdrawal, Codec.ofItem withdrawals = .ok ws ∧
        (withdrawalsRootM (m := Id) hash ws).run = .ok (header.withdrawalsRoot h) := by
  rw [checkWithdrawalsM_eq]
  cases hd : (Codec.ofItem withdrawals : Except RlpError (List Withdrawal)) with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok ws =>
    cases hr : (withdrawalsRootM (m := Id) hash ws).run with
    | error e => simp [Except.mapError, bind, Except.bind, hr]
    | ok root =>
      by_cases h' : root = header.withdrawalsRoot h
      · subst h'; simp [Except.mapError, bind, Except.bind, ensure, hr]
      · simp [Except.mapError, bind, Except.bind, ensure, hr, h']
        exact fun heq => absurd (Except.ok.inj heq) h'

/-- The withdrawals pass exactly when they decode to a list with the root of the header. -/
theorem checkWithdrawals_eq_ok_iff {header : Header fork} {h : .shapella ≤ fork}
    {withdrawals : Item} :
    checkWithdrawals header h withdrawals = .ok () ↔
      ∃ ws : List Withdrawal, Codec.ofItem withdrawals = .ok ws ∧
        withdrawalsRoot ws = .ok (header.withdrawalsRoot h) :=
  checkWithdrawalsM_eq_ok_iff _

/-- Ommers that pass were read from bytes with the ommers hash of the header.

The hash is any plain hash. -/
theorem checkOmmersM_hash (hash : ByteArray → Hash32) {header : Header fork} {ommers : Encoded}
    (h : (checkOmmersM (m := Id) hash header ommers).run = .ok ()) :
    hash ommers.bytes = header.ommersHash := by
  rw [checkOmmersM_eq] at h
  cases hi : ommers.item.toItems with
  | error e => simp [Except.mapError, bind, Except.bind, hi] at h
  | ok items =>
    by_cases hc : items.length ≤ MAX_OMMERS
    · by_cases hk : hash ommers.bytes = header.ommersHash
      · exact hk
      · have hb : (hash ommers.bytes == header.ommersHash) = false := by
          cases hh : (hash ommers.bytes == header.ommersHash)
          · rfl
          · exact absurd (eq_of_beq hh) hk
        simp [Except.mapError, bind, Except.bind, hi, ensure, hc, hb] at h
    · simp [Except.mapError, bind, Except.bind, hi, ensure, hc] at h

/-- Ommers that pass were read from bytes with the ommers hash of the header. -/
theorem checkOmmers_hash {header : Header fork} {ommers : Encoded}
    (h : checkOmmers header ommers = .ok ()) :
    Cryptography.Hash.Keccak.keccak256 ommers.bytes = header.ommersHash :=
  checkOmmersM_hash _ h

/-- A body that passes is read as its transactions, its ommers, and its withdrawals from Shapella.

Each part passes its own check, with the same plain hash. -/
theorem checkBodyM_eq_ok (hash : ByteArray → Hash32) {header : Header fork} {body : Encoded}
    (h : (checkBodyM (m := Id) hash header body).run = .ok ()) :
    ∃ transactions ommers : Encoded, ∃ rest,
      body.parts = .ok (transactions :: ommers :: rest) ∧
      (checkTransactionsM (m := Id) hash header transactions).run = .ok () ∧
      (checkOmmersM (m := Id) hash header ommers).run = .ok () ∧
      (¬ .shapella ≤ fork → rest = []) ∧
      (∀ hf : .shapella ≤ fork, ∃ withdrawals, rest = [withdrawals] ∧
        (checkWithdrawalsM (m := Id) hash header hf withdrawals.item).run = .ok ()) := by
  rw [checkBodyM_eq] at h
  cases hb : body.parts with
  | error e => simp [Except.mapError, bind, Except.bind, hb] at h
  | ok items =>
    by_cases hf : .shapella ≤ fork
    · rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        simp [Except.mapError, bind, Except.bind, hb, hf] at h
      cases ht : (checkTransactionsM (m := Id) hash header a).run with
      | error e => simp [ht] at h
      | ok u =>
        cases hw : (checkWithdrawalsM (m := Id) hash header hf c.item).run with
        | error e => simp [ht, hw] at h
        | ok u' =>
          exact ⟨a, b, [c], rfl, ht, by simpa [ht, hw] using h, fun hn => absurd hf hn,
            fun _ => ⟨c, rfl, hw⟩⟩
    · rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        simp [Except.mapError, bind, Except.bind, hb, hf] at h
      cases ht : (checkTransactionsM (m := Id) hash header a).run with
      | error e => simp [ht] at h
      | ok u =>
        exact ⟨a, b, [], rfl, ht, by simpa [ht] using h, fun _ => rfl, fun hs => absurd hs hf⟩

/-- Soundness of the gas rule: a body that passes is a list that starts with its transactions.

Each of them is a transaction of the fork, with a gas limit at most that of the header. -/
theorem checkBody_gasLimit_le {header : Header fork} {body : Encoded}
    (h : checkBody header body = .ok ()) :
    ∃ items rest, body.item = .list (.list items :: rest) ∧ ∀ item ∈ items, ∃ tx,
      decodeBodyTransaction fork item = .ok tx ∧ tx.gas.toNat ≤ header.gasLimit := by
  obtain ⟨transactions, ommers, rest, hp, ht, -⟩ := checkBodyM_eq_ok _ h
  obtain ⟨items, hitems, hgas⟩ :=
    checkGasLimits_eq_ok_iff.mp ((checkTransactionsM_eq_ok_iff _).mp ht).2
  exact ⟨items, (ommers :: rest).map (·.item), by
    rw [Encoded.item_of_parts hp, List.map_cons, hitems], hgas⟩

/-! ## Binding -/

/-- A typed transaction item stands for itself, with a type as its first byte. -/
theorem transactionBytes_bytes {b bytes v : ByteArray}
    (h : transactionBytes ⟨.bytes b, bytes⟩ = .ok v) : b = v ∧ ∃ h0 : 0 < b.size, b[0] < 0x80 := by
  unfold transactionBytes at h
  by_cases h0 : 0 < b.size
  · by_cases ht : b[0] < 0x80
    · simp only [h0, ht, ↓reduceDIte, ↓reduceIte, Except.ok.injEq] at h
      exact ⟨h, h0, ht⟩
    · simp [h0, ht] at h
  · simp [h0] at h

/-- A legacy transaction item stands for the bytes it was read from. -/
theorem transactionBytes_list {items : List Item} {bytes v : ByteArray}
    (h : transactionBytes ⟨.list items, bytes⟩ = .ok v) : bytes = v := by
  simpa [transactionBytes] using h

/-- Two transactions that keep their own encodings and stand for the same bytes are equal.

A list starts with a byte of at least `0xc0`, and a typed transaction with a byte below `0x80`. -/
theorem transactionBytes_injective {a b : Encoded} {v : ByteArray}
    (hea : encode a.item = .ok a.bytes) (heb : encode b.item = .ok b.bytes)
    (ha : transactionBytes a = .ok v) (hb : transactionBytes b = .ok v) : a = b := by
  -- A list item and a byte string item never stand for the same bytes.
  have mixed : ∀ {x bx bl : ByteArray} {l : List Item}, transactionBytes ⟨.bytes x, bx⟩ = .ok v →
      encode (.list l) = .ok bl → transactionBytes ⟨.list l, bl⟩ = .ok v → False := by
    intro x bx bl l hx he hl
    obtain ⟨hxv, h0, hlow⟩ := transactionBytes_bytes hx
    rw [transactionBytes_list hl, ← hxv] at he
    obtain ⟨first, rest, hlist, hhigh⟩ := encode_list_head l x he
    obtain ⟨h0', hfirst⟩ := getElem_zero_of_toList hlist
    have hlow' : first < 0x80 := hfirst ▸ hlow
    exact absurd (UInt8.lt_of_le_of_lt hhigh hlow') (by decide)
  obtain ⟨ai, ab⟩ := a
  obtain ⟨bi, bb⟩ := b
  cases ai with
  | bytes x =>
    cases bi with
    | bytes y =>
      obtain rfl : x = y := (transactionBytes_bytes ha).1.trans (transactionBytes_bytes hb).1.symm
      -- One item has one encoding.
      obtain rfl : ab = bb := Except.ok.inj (hea.symm.trans heb)
      rfl
    | list l => exact (mixed ha heb hb).elim
  | list l =>
    cases bi with
    | bytes y => exact (mixed hb hea ha).elim
    | list m =>
      obtain rfl : ab = bb := (transactionBytes_list ha).trans (transactionBytes_list hb).symm
      obtain rfl : l = m := by simpa using encode_injective (.list l) (.list m) ab hea heb
      rfl

/-- Transactions lists that keep their encodings and stand for the same bytes have equal items. -/
theorem transactionValues_injective {t₁ t₂ : Encoded} {values : List ByteArray}
    (he₁ : encode t₁.item = .ok t₁.bytes) (he₂ : encode t₂.item = .ok t₂.bytes)
    (h₁ : transactionValues t₁ = .ok values) (h₂ : transactionValues t₂ = .ok values) :
    t₁.item = t₂.item := by
  obtain ⟨kept₁, hp₁, hm₁⟩ := bind_ok_iff.mp h₁
  obtain ⟨kept₂, hp₂, hm₂⟩ := bind_ok_iff.mp h₂
  obtain ⟨hi₁, hk₁⟩ := (Encoded.parts_eq_ok_iff he₁).mp (mapError_ok_iff.mp hp₁)
  obtain ⟨hi₂, hk₂⟩ := (Encoded.parts_eq_ok_iff he₂).mp (mapError_ok_iff.mp hp₂)
  rw [hi₁, hi₂, mapM_ok_injective (fun x hx y hy _ h h' =>
    transactionBytes_injective (hk₁ x hx) (hk₂ y hy) h h') hm₁ hm₂]

/-- Two transactions lists have equal items, or their bytes give a collision of the hash. -/
def TransactionsBound (hash : ByteArray → Hash32) (t₁ t₂ : Encoded) : Prop :=
  t₁.item = t₂.item ∨
    ∃ values₁ values₂ pair, transactionValues t₁ = .ok values₁ ∧
      transactionValues t₂ = .ok values₂ ∧
      findIndexedCollision hash values₁ values₂ = some pair ∧ Trie.IsCollision hash pair

/-- Two withdrawals items are equal, or their withdrawals give a collision of the hash. -/
def WithdrawalsBound (hash : ByteArray → Hash32) (w₁ w₂ : Item) : Prop :=
  w₁ = w₂ ∨
    ∃ ws₁ ws₂ : List Withdrawal, ∃ values₁ values₂ pair, Codec.ofItem w₁ = .ok ws₁ ∧
      Codec.ofItem w₂ = .ok ws₂ ∧ ws₁.mapM Codec.encode = .ok values₁ ∧
      ws₂.mapM Codec.encode = .ok values₂ ∧
      findIndexedCollision hash values₁ values₂ = some pair ∧ Trie.IsCollision hash pair

/-- Two ommers lists have equal items, or the bytes they keep are a collision of the hash. -/
def OmmersBound (hash : ByteArray → Hash32) (o₁ o₂ : Encoded) : Prop :=
  o₁.item = o₂.item ∨ Trie.IsCollision hash (o₁.bytes, o₂.bytes)

/-- Two transactions lists that keep their own encodings and pass for one header are equal.

Otherwise the search over their bytes finds a collision of the hash. -/
theorem checkTransactions_binding (hash : ByteArray → Hash32) {header : Header fork}
    {t₁ t₂ : Encoded}
    (he₁ : encode t₁.item = .ok t₁.bytes) (he₂ : encode t₂.item = .ok t₂.bytes)
    (h₁ : (checkTransactionsM (m := Id) hash header t₁).run = .ok ())
    (h₂ : (checkTransactionsM (m := Id) hash header t₂).run = .ok ()) :
    TransactionsBound hash t₁ t₂ := by
  unfold TransactionsBound
  obtain ⟨⟨v₁, hv₁, hr₁⟩, -⟩ := (checkTransactionsM_eq_ok_iff hash).mp h₁
  obtain ⟨⟨v₂, hv₂, hr₂⟩, -⟩ := (checkTransactionsM_eq_ok_iff hash).mp h₂
  rcases indexedRootM_binding hash hr₁ hr₂ with rfl | ⟨pair, hfound, hvalid⟩
  · exact .inl (transactionValues_injective he₁ he₂ hv₁ hv₂)
  · exact .inr ⟨v₁, v₂, pair, hv₁, hv₂, hfound, hvalid⟩

/-- Two withdrawals items that pass for one header are equal.

Otherwise the search over the bytes of their withdrawals finds a collision of the hash. -/
theorem checkWithdrawals_binding (hash : ByteArray → Hash32) {header : Header fork}
    {h : .shapella ≤ fork} {w₁ w₂ : Item}
    (h₁ : (checkWithdrawalsM (m := Id) hash header h w₁).run = .ok ())
    (h₂ : (checkWithdrawalsM (m := Id) hash header h w₂).run = .ok ()) :
    WithdrawalsBound hash w₁ w₂ := by
  unfold WithdrawalsBound
  obtain ⟨ws₁, hd₁, hr₁⟩ := (checkWithdrawalsM_eq_ok_iff hash).mp h₁
  obtain ⟨ws₂, hd₂, hr₂⟩ := (checkWithdrawalsM_eq_ok_iff hash).mp h₂
  rcases withdrawalsRootM_binding hash hr₁ hr₂ with
    rfl | ⟨values₁, values₂, pair, hv₁, hv₂, hfound, hvalid⟩
  · exact .inl ((LawfulCodec.toItem_of_ofItem hd₁).symm.trans (LawfulCodec.toItem_of_ofItem hd₂))
  · exact .inr ⟨ws₁, ws₂, values₁, values₂, pair, hd₁, hd₂, hv₁, hv₂, hfound, hvalid⟩

/-- Two ommers lists that keep their own encodings and pass for one header are equal.

Otherwise their encodings are a collision of the hash. -/
theorem checkOmmers_binding (hash : ByteArray → Hash32) {header : Header fork} {o₁ o₂ : Encoded}
    (he₁ : encode o₁.item = .ok o₁.bytes) (he₂ : encode o₂.item = .ok o₂.bytes)
    (h₁ : (checkOmmersM (m := Id) hash header o₁).run = .ok ())
    (h₂ : (checkOmmersM (m := Id) hash header o₂).run = .ok ()) :
    OmmersBound hash o₁ o₂ := by
  unfold OmmersBound
  by_cases heq : o₁.bytes = o₂.bytes
  · exact .inl (encode_injective _ _ o₁.bytes he₁ (heq ▸ he₂))
  · exact .inr ⟨heq, (checkOmmersM_hash hash h₁).trans (checkOmmersM_hash hash h₂).symm⟩

/-- Binding of a body to its header, up to a collision of the hash.

Two bodies that keep their own encodings and pass for one header have the same parts.

With Keccak-256, the hypotheses are that both bodies pass the check. -/
theorem checkBody_binding (hash : ByteArray → Hash32) {header : Header fork} {x₁ x₂ : Encoded}
    (he₁ : encode x₁.item = .ok x₁.bytes) (he₂ : encode x₂.item = .ok x₂.bytes)
    (h₁ : (checkBodyM (m := Id) hash header x₁).run = .ok ())
    (h₂ : (checkBodyM (m := Id) hash header x₂).run = .ok ()) :
    -- Each body is read as its transactions, its ommers, and the rest.
    ∃ t₁ o₁ t₂ o₂ : Encoded, ∃ rest₁ rest₂,
      x₁.parts = .ok (t₁ :: o₁ :: rest₁) ∧ x₂.parts = .ok (t₂ :: o₂ :: rest₂) ∧
      -- Their transactions are equal, or the bytes of the transactions give a collision.
      --
      -- Their ommers lists are equal, or their encodings are a collision.
      TransactionsBound hash t₁ t₂ ∧ OmmersBound hash o₁ o₂ ∧
      (¬ .shapella ≤ fork → rest₁ = [] ∧ rest₂ = []) ∧
      -- From Shapella, their withdrawals are equal, or the withdrawal bytes give a collision.
      (.shapella ≤ fork → ∃ w₁ w₂ : Encoded, rest₁ = [w₁] ∧ rest₂ = [w₂] ∧
        WithdrawalsBound hash w₁.item w₂.item) := by
  obtain ⟨t₁, o₁, rest₁, hp₁, ht₁, ho₁, hn₁, hs₁⟩ := checkBodyM_eq_ok hash h₁
  obtain ⟨t₂, o₂, rest₂, hp₂, ht₂, ho₂, hn₂, hs₂⟩ := checkBodyM_eq_ok hash h₂
  -- Each part keeps its own encoding, since the body does.
  have hk₁ := ((Encoded.parts_eq_ok_iff he₁).mp hp₁).2
  have hk₂ := ((Encoded.parts_eq_ok_iff he₂).mp hp₂).2
  refine ⟨t₁, o₁, t₂, o₂, rest₁, rest₂, hp₁, hp₂,
    checkTransactions_binding hash (hk₁ t₁ (by simp)) (hk₂ t₂ (by simp)) ht₁ ht₂,
    checkOmmers_binding hash (hk₁ o₁ (by simp)) (hk₂ o₂ (by simp)) ho₁ ho₂,
    fun hf => ⟨hn₁ hf, hn₂ hf⟩, fun hf => ?_⟩
  obtain ⟨w₁, rfl, hw₁⟩ := hs₁ hf
  obtain ⟨w₂, rfl, hw₂⟩ := hs₂ hf
  exact ⟨w₁, w₂, rfl, rfl, checkWithdrawals_binding hash hw₁ hw₂⟩

/-! ## Completeness -/

/-- The item of a transaction, with its own encoding, stands for the bytes of the transaction. -/
theorem transactionBytes_bodyItem {tx : Transaction} {item : Item} {bytes b : ByteArray}
    (h : bodyItem tx = .ok item) (hk : encode item = .ok bytes)
    (he : encodeTransaction tx = .ok b) : transactionBytes ⟨item, bytes⟩ = .ok b := by
  by_cases hl : ∃ t, tx = .legacy t
  · obtain ⟨t, rfl⟩ := hl
    simp only [bodyItem, Except.ok.injEq] at h
    subst h
    -- A legacy transaction is the encoding of its item, which the item keeps.
    have he' : encode (Codec.toItem t) = .ok b := he
    obtain rfl : bytes = b := Except.ok.inj (hk.symm.trans he')
    rfl
  · have hb : bodyItem tx = .bytes <$> encodeTransaction tx := by
      cases tx <;> first | rfl | exact absurd ⟨_, rfl⟩ hl
    rw [hb, he] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    -- The first byte is the type, at most 4.
    obtain ⟨h0, -, htype⟩ := encodeTransaction_head he
    have hne : tx.type ≠ 0 := fun h0' => hl (by cases tx <;> simp_all [Transaction.type])
    have hlow : b[0] < 0x80 := by
      rw [htype hne]
      exact UInt8.lt_of_le_of_lt (Transaction.type_le tx) (by decide)
    simp [transactionBytes, h0, hlow]

/-- The transactions of a body, each with its own encoding, stand for their bytes. -/
theorem mapM_transactionBytes {txs : List Transaction} {kept : List Encoded}
    {values : List ByteArray} (h : txs.mapM bodyItem = .ok (kept.map (·.item)))
    (hk : ∀ k ∈ kept, encode k.item = .ok k.bytes)
    (hv : txs.mapM encodeTransaction = .ok values) : kept.mapM transactionBytes = .ok values := by
  induction txs generalizing kept values with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h hv
    subst hv
    cases kept with
    | nil => rfl
    | cons _ _ => simp at h
  | cons tx txs ih =>
    obtain ⟨item, rest, hi, hr, hcons⟩ := mapM_cons_ok.mp h
    obtain ⟨b, bs, hb, hbs, rfl⟩ := mapM_cons_ok.mp hv
    cases kept with
    | nil => simp at hcons
    | cons k ks =>
      simp only [List.map_cons, List.cons.injEq] at hcons
      obtain ⟨rfl, rfl⟩ := hcons
      simp only [List.mem_cons, forall_eq_or_imp] at hk
      rw [List.mapM_cons, transactionBytes_bodyItem hi hk.1 hb, ih hr hk.2 hbs]
      rfl

/-- Ommers pass when the bytes they keep have the ommers hash of the header.

There must be at most two of them, and none may have a number above that of the block. -/
theorem checkOmmers_of_valid {header : Header fork}
    {ommers : List ((f : Fork) × Header f)} {encoded : ByteArray}
    (hhash : Cryptography.Hash.Keccak.keccak256 encoded = header.ommersHash)
    (hcount : ommers.length ≤ MAX_OMMERS)
    (hnumber : ∀ ommer ∈ ommers, ommer.2.number ≤ header.number) :
    checkOmmers header ⟨ommersItem ommers, encoded⟩ = .ok () := by
  have hb : (Cryptography.Hash.Keccak.keccak256 encoded == header.ommersHash) = true := by
    rw [hhash]; exact beq_self_eq_true _
  have hit : (ommersItem ommers).toItems = .ok (ommers.map fun o => Codec.toItem o.2) := rfl
  rw [checkOmmers_eq]
  simp only [hit, Except.mapError, bind, Except.bind, ensure, List.length_map, hcount,
    ↓reduceIte, hb]
  refine forM_ok_iff.mpr fun (i, item) hm => ?_
  obtain ⟨ommer, hmem, rfl⟩ := List.mem_map.mp (List.of_mem_zip hm).2
  simp only [headerNumber_toItem, hnumber ommer hmem, ↓reduceIte]

/-- Completeness: the body of a block that passes the transition passes the check.

The check is against the header of that block, and reads the body from its encoding.

Only a body that encodes is covered, which every body under `2^64` bytes does. -/
theorem checkBody_complete {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ body, bodyOf block = .ok body ∧
      ∀ bytes, encode body = .ok bytes → checkBody block.header ⟨body, bytes⟩ = .ok () := by
  obtain ⟨-, -, hcheck, hashes, output, roots, -, -, hroots, hchecks, -⟩ := stateTransition_eq_ok h
  obtain ⟨items, hitems⟩ := checkBlock_transactions hcheck
  have htx : ∀ tbytes, encode (.list items) = .ok tbytes →
      checkTransactions block.header ⟨.list items, tbytes⟩ = .ok () := by
    intro tbytes htb
    refine checkTransactions_eq_ok_iff.mpr ⟨?_, ?_⟩
    · have hroot := outputRoots_transactions hroots
      rw [outputChecks_transactions hchecks] at hroot
      obtain ⟨values, hvalues, hindexed⟩ := transactionsRoot_eq_ok_iff.mp hroot
      refine ⟨values, ?_, hindexed⟩
      -- Each transaction is read with its own encoding.
      obtain ⟨kept, hp, hk, he⟩ := Encoded.parts_of_encode (e := ⟨_, tbytes⟩) htb rfl
      simp [transactionValues, hp, Except.mapError, bind, Except.bind,
        mapM_transactionBytes (hk ▸ hitems) he hvalues]
    · -- Each transaction has a type of the fork and a gas limit at most the block's.
      refine checkGasLimits_eq_ok_iff.mpr ⟨items, rfl, fun item hmem => ?_⟩
      obtain ⟨tx, htxmem, hitem⟩ := mapM_ok_mem hitems item hmem
      exact ⟨tx, decodeBodyTransaction_bodyItem hitem (stateTransition_fork_le h tx htxmem),
        stateTransition_txGas_le h tx htxmem⟩
  have hom : ∀ obytes, encode (ommersItem block.ommers) = .ok obytes →
      checkOmmers block.header ⟨ommersItem block.ommers, obytes⟩ = .ok () := by
    intro obytes hob
    by_cases hp : fork < .paris
    · obtain ⟨⟨e, he, hk⟩, hc, -, hn⟩ := validateOmmers_spec (checkBlock_validateOmmers hp hcheck)
      obtain rfl : obytes = e := Except.ok.inj (hob.symm.trans he)
      exact checkOmmers_of_valid hk hc fun o hmem => Nat.le_of_lt (hn o hmem).2.1
    · obtain ⟨hempty, hhash⟩ := checkBlock_paris hp hcheck
      rw [hempty] at hob ⊢
      obtain rfl : obytes = ⟨#[0xc0]⟩ := Except.ok.inj (hob.symm.trans rfl)
      exact checkOmmers_nil hhash
  by_cases hs : .shapella ≤ fork
  · have hw : checkWithdrawals block.header hs (Codec.toItem (block.withdrawals hs)) = .ok () := by
      obtain ⟨r, hr, hsome⟩ := outputRoots_withdrawals hs hroots
      have := hsome.symm.trans (outputChecks_withdrawals hs hchecks)
      cases this
      exact checkWithdrawals_eq_ok_iff.mpr ⟨_, LawfulCodec.ofItem_toItem _, hr⟩
    refine ⟨.list [.list items, ommersItem block.ommers, Codec.toItem (block.withdrawals hs)],
      by simp [bodyOf, hitems, Item.ofSince, hs]; rfl, fun bytes hb => ?_⟩
    -- Each part of the body is read with its own encoding.
    obtain ⟨kept, hp, hk, he⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
    rcases kept with _ | ⟨⟨ti, tb⟩, _ | ⟨⟨oi, ob⟩, _ | ⟨⟨wi, wb⟩, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at hk
    obtain ⟨rfl, rfl, rfl⟩ := hk
    simp only [List.mem_cons, forall_eq_or_imp] at he
    simp only [checkBody_eq, hp, Except.mapError, bind, Except.bind, hs, ↓reduceDIte,
      htx tb he.1, hw, hom ob he.2.1]
  · refine ⟨.list [.list items, ommersItem block.ommers],
      by simp [bodyOf, hitems, Item.ofSince, hs]; rfl, fun bytes hb => ?_⟩
    obtain ⟨kept, hp, hk, he⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
    rcases kept with _ | ⟨⟨ti, tb⟩, _ | ⟨⟨oi, ob⟩, _ | ⟨_, _⟩⟩⟩ <;> simp at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [List.mem_cons, forall_eq_or_imp] at he
    simp only [checkBody_eq, hp, Except.mapError, bind, Except.bind, hs, ↓reduceDIte,
      htx tb he.1, hom ob he.2.1]

end EthLib.Execution.Network
