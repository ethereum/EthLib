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

/-!
# Proofs: the check of a block body

The body of every block that passes the state transition passes the check against its header.

Each transaction of a body that passes decodes at the fork, with a gas limit at most the block's.

Two bodies that keep their encodings and pass for one header are equal in each part.

Otherwise a Keccak-256 collision is named.

A body with three ommers is rejected once the checks before the ommers pass.

A body without withdrawals from Shapella, or with them before, is rejected for that reason.

Two errors with one code come from one constructor.
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
  cases e₁ <;> cases e₂ <;>
    first | rfl | (simp only [BodyError.code] at h; exact absurd h (by decide))

/-- An ommers list of more than `MAX_OMMERS` items is rejected, whatever its items and bytes. -/
theorem checkOmmers_tooMany {header : Header fork} {items : List Item} {bytes : ByteArray}
    (h : MAX_OMMERS < items.length) :
    checkOmmers header ⟨.list items, bytes⟩ = .error (.tooManyOmmers items.length) := by
  have hn : ¬ items.length ≤ MAX_OMMERS := Nat.not_le.mpr h
  simp only [checkOmmers, Item.toItems, Except.mapError, ensure, bind, Except.bind, hn, ite_false]

/-- The empty ommers list, read from its encoding, is accepted when the header commits to it. -/
theorem checkOmmers_nil {header : Header fork} (h : header.ommersHash = EMPTY_OMMER_HASH) :
    checkOmmers header ⟨.list [], ⟨#[0xc0]⟩⟩ = .ok () := by
  simp only [checkOmmers, Item.toItems, Except.mapError, ensure, bind, Except.bind, h,
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
  simp only [checkBody, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte]
  rfl

/-- From Shapella, a body of two items, read from its encoding, is rejected for its withdrawals. -/
theorem checkBody_missingWithdrawals (hfork : .shapella ≤ fork) {header : Header fork}
    {a b : Item} {bytes : ByteArray} (hb : encode (.list [a, b]) = .ok bytes) :
    checkBody header ⟨.list [a, b], bytes⟩ = .error .missingWithdrawals := by
  obtain ⟨kept, hp, hk, -⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
  rcases kept with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩ <;> simp at hk
  simp only [checkBody, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte]
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
  simp only [checkBody, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte, htx, hom]

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
  simp only [checkBody, hp, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte, htx, hw, hom]

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

Each of them must also decode at the fork, with a gas limit at most that of the header. -/
theorem checkTransactions_eq_ok_iff {header : Header fork} {transactions : Encoded} :
    checkTransactions header transactions = .ok () ↔
      (∃ values, transactionValues transactions = .ok values ∧
        indexedRoot values = .ok header.transactionsRoot) ∧
      checkGasLimits header transactions.item = .ok () := by
  unfold checkTransactions
  cases hv : transactionValues transactions with
  | error e => simp [bind, Except.bind]
  | ok values =>
    cases hr : indexedRoot values with
    | error e => simp [Except.mapError, bind, Except.bind, hr]
    | ok root =>
      by_cases h : root = header.transactionsRoot
      · subst h; simp [Except.mapError, bind, Except.bind, ensure, hr]
      · simp [Except.mapError, bind, Except.bind, ensure, hr, h]

/-- The withdrawals pass exactly when they decode to a list with the root of the header. -/
theorem checkWithdrawals_eq_ok_iff {header : Header fork} {h : .shapella ≤ fork}
    {withdrawals : Item} :
    checkWithdrawals header h withdrawals = .ok () ↔
      ∃ ws : List Withdrawal, Codec.ofItem withdrawals = .ok ws ∧
        withdrawalsRoot ws = .ok (header.withdrawalsRoot h) := by
  unfold checkWithdrawals
  cases hd : (Codec.ofItem withdrawals : Except RlpError (List Withdrawal)) with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok ws =>
    cases hr : withdrawalsRoot ws with
    | error e => simp [Except.mapError, bind, Except.bind, hr]
    | ok root =>
      by_cases h' : root = header.withdrawalsRoot h
      · subst h'; simp [Except.mapError, bind, Except.bind, ensure, hr]
      · simp [Except.mapError, bind, Except.bind, ensure, hr, h']

/-- Ommers that pass were read from bytes with the ommers hash of the header. -/
theorem checkOmmers_hash {header : Header fork} {ommers : Encoded}
    (h : checkOmmers header ommers = .ok ()) :
    Cryptography.Hash.Keccak.keccak256 ommers.bytes = header.ommersHash := by
  unfold checkOmmers at h
  cases hi : ommers.item.toItems with
  | error e => simp [Except.mapError, bind, Except.bind, hi] at h
  | ok items =>
    by_cases hc : items.length ≤ MAX_OMMERS
    · by_cases hk : Cryptography.Hash.Keccak.keccak256 ommers.bytes = header.ommersHash
      · exact hk
      · have hb : (Cryptography.Hash.Keccak.keccak256 ommers.bytes == header.ommersHash) =
            false := by
          cases hh : (Cryptography.Hash.Keccak.keccak256 ommers.bytes == header.ommersHash)
          · rfl
          · exact absurd (eq_of_beq hh) hk
        simp [Except.mapError, bind, Except.bind, hi, ensure, hc, hb] at h
    · simp [Except.mapError, bind, Except.bind, hi, ensure, hc] at h

/-- A body that passes is the list of its parts, with the withdrawals exactly from Shapella.

When the body keeps its own encoding, so do its transactions and its ommers. -/
theorem checkBody_eq_ok {header : Header fork} {body : Encoded}
    (h : checkBody header body = .ok ()) :
    ∃ transactions ommers : Encoded, checkTransactions header transactions = .ok () ∧
      checkOmmers header ommers = .ok () ∧
      (encode body.item = .ok body.bytes → encode transactions.item = .ok transactions.bytes ∧
        encode ommers.item = .ok ommers.bytes) ∧
      (¬ .shapella ≤ fork → body.item = .list [transactions.item, ommers.item]) ∧
      (∀ hf : .shapella ≤ fork, ∃ withdrawals, checkWithdrawals header hf withdrawals = .ok () ∧
        body.item = .list [transactions.item, ommers.item, withdrawals]) := by
  unfold checkBody at h
  cases hb : body.parts with
  | error e => simp [Except.mapError, bind, Except.bind, hb] at h
  | ok items =>
    have hbody := Encoded.item_of_parts hb
    -- Each part keeps its own encoding when the body does.
    have henc : encode body.item = .ok body.bytes → ∀ k ∈ items, encode k.item = .ok k.bytes :=
      fun he => ((Encoded.parts_eq_ok_iff he).mp hb).2
    by_cases hf : .shapella ≤ fork
    · rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        simp [Except.mapError, bind, Except.bind, hb, hf] at h
      cases ht : checkTransactions header a with
      | error e => simp [ht] at h
      | ok u =>
        cases hw : checkWithdrawals header hf c.item with
        | error e => simp [ht, hw] at h
        | ok u' =>
          refine ⟨a, b, ht, by simpa [ht, hw] using h,
            fun he => ⟨henc he a (by simp), henc he b (by simp)⟩, fun hn => absurd hf hn,
            fun _ => ⟨c.item, hw, by simpa using hbody⟩⟩
    · rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        simp [Except.mapError, bind, Except.bind, hb, hf] at h
      cases ht : checkTransactions header a with
      | error e => simp [ht] at h
      | ok u =>
        refine ⟨a, b, ht, by simpa [ht] using h,
          fun he => ⟨henc he a (by simp), henc he b (by simp)⟩, fun _ => by simpa using hbody,
          fun hs => absurd hs hf⟩

/-- Soundness of the gas rule: a body that passes is a list that starts with its transactions.

Each of them is a transaction of the fork, with a gas limit at most that of the header. -/
theorem checkBody_gasLimit_le {header : Header fork} {body : Encoded}
    (h : checkBody header body = .ok ()) :
    ∃ items rest, body.item = .list (.list items :: rest) ∧ ∀ item ∈ items, ∃ tx,
      decodeBodyTransaction fork item = .ok tx ∧ tx.gas.toNat ≤ header.gasLimit := by
  obtain ⟨transactions, ommers, ht, -, -, hn, hs⟩ := checkBody_eq_ok h
  obtain ⟨items, hitems, hgas⟩ :=
    checkGasLimits_eq_ok_iff.mp (checkTransactions_eq_ok_iff.mp ht).2
  by_cases hf : .shapella ≤ fork
  · obtain ⟨withdrawals, -, hbody⟩ := hs hf
    exact ⟨items, [ommers.item, withdrawals], by rw [hbody, hitems], hgas⟩
  · exact ⟨items, [ommers.item], by rw [hn hf, hitems], hgas⟩

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

/-- Two transactions lists have equal items, or their bytes give a Keccak-256 collision. -/
def TransactionsBound (t₁ t₂ : Encoded) : Prop :=
  t₁.item = t₂.item ∨
    ∃ values₁ values₂ pair, transactionValues t₁ = .ok values₁ ∧
      transactionValues t₂ = .ok values₂ ∧ findIndexedCollision values₁ values₂ = some pair ∧
      Trie.IsCollision Cryptography.Hash.Keccak.keccak256 pair

/-- Two withdrawals items are equal, or their withdrawals give a Keccak-256 collision. -/
def WithdrawalsBound (w₁ w₂ : Item) : Prop :=
  w₁ = w₂ ∨
    ∃ ws₁ ws₂ : List Withdrawal, ∃ values₁ values₂ pair, Codec.ofItem w₁ = .ok ws₁ ∧
      Codec.ofItem w₂ = .ok ws₂ ∧ ws₁.mapM Codec.encode = .ok values₁ ∧
      ws₂.mapM Codec.encode = .ok values₂ ∧ findIndexedCollision values₁ values₂ = some pair ∧
      Trie.IsCollision Cryptography.Hash.Keccak.keccak256 pair

/-- Two ommers lists have equal items, or the bytes they keep are a Keccak-256 collision. -/
def OmmersBound (o₁ o₂ : Encoded) : Prop :=
  o₁.item = o₂.item ∨ Trie.IsCollision Cryptography.Hash.Keccak.keccak256 (o₁.bytes, o₂.bytes)

/-- Two transactions lists that keep their own encodings and pass for one header are equal.

Otherwise the search over their bytes finds a Keccak-256 collision. -/
theorem checkTransactions_binding {header : Header fork} {t₁ t₂ : Encoded}
    (he₁ : encode t₁.item = .ok t₁.bytes) (he₂ : encode t₂.item = .ok t₂.bytes)
    (h₁ : checkTransactions header t₁ = .ok ()) (h₂ : checkTransactions header t₂ = .ok ()) :
    TransactionsBound t₁ t₂ := by
  unfold TransactionsBound
  obtain ⟨⟨v₁, hv₁, hr₁⟩, -⟩ := checkTransactions_eq_ok_iff.mp h₁
  obtain ⟨⟨v₂, hv₂, hr₂⟩, -⟩ := checkTransactions_eq_ok_iff.mp h₂
  rcases indexedRoot_binding hr₁ hr₂ with rfl | ⟨pair, hfound, hvalid⟩
  · exact .inl (transactionValues_injective he₁ he₂ hv₁ hv₂)
  · exact .inr ⟨v₁, v₂, pair, hv₁, hv₂, hfound, hvalid⟩

/-- Two withdrawals items that pass for one header are equal.

Otherwise the search over the bytes of their withdrawals finds a Keccak-256 collision. -/
theorem checkWithdrawals_binding {header : Header fork} {h : .shapella ≤ fork} {w₁ w₂ : Item}
    (h₁ : checkWithdrawals header h w₁ = .ok ()) (h₂ : checkWithdrawals header h w₂ = .ok ()) :
    WithdrawalsBound w₁ w₂ := by
  unfold WithdrawalsBound
  obtain ⟨ws₁, hd₁, hr₁⟩ := checkWithdrawals_eq_ok_iff.mp h₁
  obtain ⟨ws₂, hd₂, hr₂⟩ := checkWithdrawals_eq_ok_iff.mp h₂
  rcases withdrawalsRoot_binding hr₁ hr₂ with
    rfl | ⟨values₁, values₂, pair, hv₁, hv₂, hfound, hvalid⟩
  · exact .inl ((LawfulCodec.toItem_of_ofItem hd₁).symm.trans (LawfulCodec.toItem_of_ofItem hd₂))
  · exact .inr ⟨ws₁, ws₂, values₁, values₂, pair, hd₁, hd₂, hv₁, hv₂, hfound, hvalid⟩

/-- Two ommers lists that keep their own encodings and pass for one header are equal.

Otherwise their encodings are a Keccak-256 collision. -/
theorem checkOmmers_binding {header : Header fork} {o₁ o₂ : Encoded}
    (he₁ : encode o₁.item = .ok o₁.bytes) (he₂ : encode o₂.item = .ok o₂.bytes)
    (h₁ : checkOmmers header o₁ = .ok ()) (h₂ : checkOmmers header o₂ = .ok ()) :
    OmmersBound o₁ o₂ := by
  unfold OmmersBound
  by_cases heq : o₁.bytes = o₂.bytes
  · exact .inl (encode_injective _ _ o₁.bytes he₁ (heq ▸ he₂))
  · exact .inr ⟨heq, (checkOmmers_hash h₁).trans (checkOmmers_hash h₂).symm⟩

/-- Binding of a body to its header.

Two bodies that keep their own encodings and pass for one header have the same parts.

That holds up to a Keccak-256 collision.

- Their transactions are equal, or the bytes of the transactions give a collision.
- From Shapella, their withdrawals are equal, or the bytes of the withdrawals give a collision.
- Their ommers lists are equal, or their encodings are a collision. -/
theorem checkBody_binding {header : Header fork} {x₁ x₂ : Encoded}
    (he₁ : encode x₁.item = .ok x₁.bytes) (he₂ : encode x₂.item = .ok x₂.bytes)
    (h₁ : checkBody header x₁ = .ok ()) (h₂ : checkBody header x₂ = .ok ()) :
    ∃ t₁ o₁ t₂ o₂ : Encoded, TransactionsBound t₁ t₂ ∧ OmmersBound o₁ o₂ ∧
      (¬ .shapella ≤ fork →
        x₁.item = .list [t₁.item, o₁.item] ∧ x₂.item = .list [t₂.item, o₂.item]) ∧
      (.shapella ≤ fork → ∃ w₁ w₂, WithdrawalsBound w₁ w₂ ∧
        x₁.item = .list [t₁.item, o₁.item, w₁] ∧ x₂.item = .list [t₂.item, o₂.item, w₂]) := by
  obtain ⟨t₁, o₁, ht₁, ho₁, hk₁, hn₁, hs₁⟩ := checkBody_eq_ok h₁
  obtain ⟨t₂, o₂, ht₂, ho₂, hk₂, hn₂, hs₂⟩ := checkBody_eq_ok h₂
  obtain ⟨hte₁, hoe₁⟩ := hk₁ he₁
  obtain ⟨hte₂, hoe₂⟩ := hk₂ he₂
  refine ⟨t₁, o₁, t₂, o₂, checkTransactions_binding hte₁ hte₂ ht₁ ht₂,
    checkOmmers_binding hoe₁ hoe₂ ho₁ ho₂, fun hf => ⟨hn₁ hf, hn₂ hf⟩, fun hf => ?_⟩
  obtain ⟨w₁, hw₁, hx₁⟩ := hs₁ hf
  obtain ⟨w₂, hw₂, hx₂⟩ := hs₂ hf
  exact ⟨w₁, w₂, checkWithdrawals_binding hw₁ hw₂, hx₁, hx₂⟩

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
  unfold checkOmmers
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
    simp only [checkBody, hp, Except.mapError, bind, Except.bind, hs, ↓reduceDIte,
      htx tb he.1, hw, hom ob he.2.1]
  · refine ⟨.list [.list items, ommersItem block.ommers],
      by simp [bodyOf, hitems, Item.ofSince, hs]; rfl, fun bytes hb => ?_⟩
    obtain ⟨kept, hp, hk, he⟩ := Encoded.parts_of_encode (e := ⟨_, bytes⟩) hb rfl
    rcases kept with _ | ⟨⟨ti, tb⟩, _ | ⟨⟨oi, ob⟩, _ | ⟨_, _⟩⟩⟩ <;> simp at hk
    obtain ⟨rfl, rfl⟩ := hk
    simp only [List.mem_cons, forall_eq_or_imp] at he
    simp only [checkBody, hp, Except.mapError, bind, Except.bind, hs, ↓reduceDIte,
      htx tb he.1, hom ob he.2.1]

end EthLib.Execution.Network
