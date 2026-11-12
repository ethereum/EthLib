module

public import EthLib.Execution.Network.Bodies
public import EthLib.Execution.Proofs.Blocks.Roots
public import EthLib.Base.Proofs.MapM
public import EthLib.Execution.Proofs.Blocks.Header
public import EthLib.Execution.Proofs.Blocks.Ommers
public import EthLib.Execution.Proofs.Blocks.Transition
public import EthLib.Execution.Proofs.Blocks.TypedRoots
public import EthLib.Execution.Proofs.Blocks.Validate
public import EthLib.Serialization.Proofs.Rlp.Codec
public import EthLib.Serialization.Proofs.Rlp.RoundTrip

/-!
# Proofs: the check of a block body

Two errors with one code come from one constructor.

A body whose ommers list holds three items is rejected, once its shape and its transactions pass.

A body without withdrawals from Shapella, or with them before, is rejected for that reason.
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

/-- An ommers list of more than `MAX_OMMERS` items is rejected, whatever its items. -/
theorem checkOmmers_tooMany {header : Header fork} {items : List Item}
    (h : MAX_OMMERS < items.length) :
    checkOmmers header (.list items) = .error (.tooManyOmmers items.length) := by
  have hn : ¬ items.length ≤ MAX_OMMERS := Nat.not_le.mpr h
  simp only [checkOmmers, Item.toItems, Except.mapError, ensure, bind, Except.bind, hn, ite_false]

/-- The empty ommers list is accepted when the header commits to it. -/
theorem checkOmmers_nil {header : Header fork} (h : header.ommersHash = EMPTY_OMMER_HASH) :
    checkOmmers header (.list []) = .ok () := by
  have he : encode (.list []) = .ok ⟨#[0xc0]⟩ := by rfl
  simp only [checkOmmers, Item.toItems, Except.mapError, ensure, bind, Except.bind, he, h,
    EMPTY_OMMER_HASH, MAX_OMMERS, List.length_nil, Nat.zero_le, ite_true, beq_self_eq_true,
    List.range_zero, List.zip_nil_left]
  rfl

/-- Before Shapella, a body with three items is rejected for its withdrawals. -/
theorem checkBody_unexpectedWithdrawals (hfork : ¬ .shapella ≤ fork) {header : Header fork}
    {a b c : Item} : checkBody header (.list [a, b, c]) = .error .unexpectedWithdrawals := by
  simp only [checkBody, hfork, ↓reduceDIte]
  rfl

/-- From Shapella, a body with two items is rejected for its withdrawals. -/
theorem checkBody_missingWithdrawals (hfork : .shapella ≤ fork) {header : Header fork}
    {a b : Item} : checkBody header (.list [a, b]) = .error .missingWithdrawals := by
  simp only [checkBody, hfork, ↓reduceDIte]
  rfl

/-- Before Shapella, a body that passes the shape and transactions checks, with three ommers, is
rejected for them. -/
theorem checkBody_tooManyOmmers (hfork : ¬ .shapella ≤ fork) {header : Header fork}
    {transactions : Item} {ommers : List Item} (hlen : ommers.length = 3)
    (htx : checkTransactions header transactions = .ok ()) :
    checkBody header (.list [transactions, .list ommers]) = .error (.tooManyOmmers 3) := by
  have := checkOmmers_tooMany (header := header) (items := ommers) (by simp [MAX_OMMERS, hlen])
  rw [hlen] at this
  simp only [checkBody, Item.toItems, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte,
    htx, this]

/-- From Shapella, a body that passes the shape, transactions and withdrawals checks, with three
ommers, is rejected for them. -/
theorem checkBody_tooManyOmmers_shapella (hfork : .shapella ≤ fork) {header : Header fork}
    {transactions withdrawals : Item} {ommers : List Item} (hlen : ommers.length = 3)
    (htx : checkTransactions header transactions = .ok ())
    (hw : checkWithdrawals header hfork withdrawals = .ok ()) :
    checkBody header (.list [transactions, .list ommers, withdrawals]) =
      .error (.tooManyOmmers 3) := by
  have := checkOmmers_tooMany (header := header) (items := ommers) (by simp [MAX_OMMERS, hlen])
  rw [hlen] at this
  simp only [checkBody, Item.toItems, Except.mapError, bind, Except.bind, hfork, ↓reduceDIte,
    htx, hw, this]

/-! ## What a passing check says -/

/-- The transactions pass exactly when their bytes have the transactions root of the header. -/
theorem checkTransactions_eq_ok_iff {header : Header fork} {transactions : Item} :
    checkTransactions header transactions = .ok () ↔
      ∃ values, transactionValues transactions = .ok values ∧
        indexedRoot values = .ok header.transactionsRoot := by
  unfold checkTransactions
  cases hv : transactionValues transactions with
  | error e => simp [Except.mapError, bind, Except.bind]
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

/-- Ommers that pass have an encoding with the ommers hash of the header. -/
theorem checkOmmers_hash {header : Header fork} {ommers : Item}
    (h : checkOmmers header ommers = .ok ()) :
    ∃ encoded, encode ommers = .ok encoded ∧
      Cryptography.Hash.Keccak.keccak256 encoded = header.ommersHash := by
  unfold checkOmmers at h
  cases hi : ommers.toItems with
  | error e => simp [Except.mapError, bind, Except.bind, hi] at h
  | ok items =>
    by_cases hc : items.length ≤ MAX_OMMERS
    · cases he : encode ommers with
      | error e => simp [Except.mapError, bind, Except.bind, hi, he, ensure, hc] at h
      | ok encoded =>
        refine ⟨encoded, rfl, ?_⟩
        by_cases hk : Cryptography.Hash.Keccak.keccak256 encoded = header.ommersHash
        · exact hk
        · have hb : (Cryptography.Hash.Keccak.keccak256 encoded == header.ommersHash) = false := by
            cases hh : (Cryptography.Hash.Keccak.keccak256 encoded == header.ommersHash)
            · rfl
            · exact absurd (eq_of_beq hh) hk
          simp [Except.mapError, bind, Except.bind, hi, he, ensure, hc, hb] at h
    · simp [Except.mapError, bind, Except.bind, hi, ensure, hc] at h

/-- A body that passes is the list of its parts, with the withdrawals exactly from Shapella. -/
theorem checkBody_eq_ok {header : Header fork} {body : Item}
    (h : checkBody header body = .ok ()) :
    ∃ transactions ommers, checkTransactions header transactions = .ok () ∧
      checkOmmers header ommers = .ok () ∧
      (¬ .shapella ≤ fork → body = .list [transactions, ommers]) ∧
      (∀ hf : .shapella ≤ fork, ∃ withdrawals, checkWithdrawals header hf withdrawals = .ok () ∧
        body = .list [transactions, ommers, withdrawals]) := by
  unfold checkBody at h
  cases hb : body.toItems with
  | error e => simp [Except.mapError, bind, Except.bind, hb] at h
  | ok items =>
    have hbody : body = .list items := Item.toItems_eq_ok.mp hb
    by_cases hf : .shapella ≤ fork
    · rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        simp [Except.mapError, bind, Except.bind, hb, hf] at h
      cases ht : checkTransactions header a with
      | error e => simp [ht] at h
      | ok u =>
        cases hw : checkWithdrawals header hf c with
        | error e => simp [ht, hw] at h
        | ok u' =>
          refine ⟨a, b, ht, by simpa [ht, hw] using h, fun hn => absurd hf hn,
            fun _ => ⟨c, hw, hbody⟩⟩
    · rcases items with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
        simp [Except.mapError, bind, Except.bind, hb, hf] at h
      cases ht : checkTransactions header a with
      | error e => simp [ht] at h
      | ok u =>
        refine ⟨a, b, ht, by simpa [ht] using h, fun _ => hbody, fun hs => absurd hs hf⟩

/-! ## Binding -/

/-- Two transaction items have the same bytes, or their bytes give a Keccak-256 collision. -/
def TransactionsBound (t₁ t₂ : Item) : Prop :=
  transactionValues t₁ = transactionValues t₂ ∨
    ∃ values₁ values₂ pair, transactionValues t₁ = .ok values₁ ∧
      transactionValues t₂ = .ok values₂ ∧ findIndexedCollision values₁ values₂ = some pair ∧
      Trie.IsCollision Cryptography.Hash.Keccak.keccak256 pair

/-- Two withdrawals items are equal, or the bytes of their withdrawals give a Keccak-256 collision. -/
def WithdrawalsBound (w₁ w₂ : Item) : Prop :=
  w₁ = w₂ ∨
    ∃ ws₁ ws₂ : List Withdrawal, ∃ values₁ values₂ pair, Codec.ofItem w₁ = .ok ws₁ ∧
      Codec.ofItem w₂ = .ok ws₂ ∧ ws₁.mapM Codec.encode = .ok values₁ ∧
      ws₂.mapM Codec.encode = .ok values₂ ∧ findIndexedCollision values₁ values₂ = some pair ∧
      Trie.IsCollision Cryptography.Hash.Keccak.keccak256 pair

/-- Two ommers items are equal, or their encodings are a Keccak-256 collision. -/
def OmmersBound (o₁ o₂ : Item) : Prop :=
  o₁ = o₂ ∨ ∃ e₁ e₂, encode o₁ = .ok e₁ ∧ encode o₂ = .ok e₂ ∧
    Trie.IsCollision Cryptography.Hash.Keccak.keccak256 (e₁, e₂)

/-- Two transaction lists that pass for one header have the same bytes.

Otherwise the search over their bytes finds a Keccak-256 collision. -/
theorem checkTransactions_binding {header : Header fork} {t₁ t₂ : Item}
    (h₁ : checkTransactions header t₁ = .ok ()) (h₂ : checkTransactions header t₂ = .ok ()) :
    TransactionsBound t₁ t₂ := by
  unfold TransactionsBound
  obtain ⟨v₁, hv₁, hr₁⟩ := checkTransactions_eq_ok_iff.mp h₁
  obtain ⟨v₂, hv₂, hr₂⟩ := checkTransactions_eq_ok_iff.mp h₂
  rcases indexedRoot_binding hr₁ hr₂ with rfl | ⟨pair, hfound, hvalid⟩
  · exact .inl (hv₁.trans hv₂.symm)
  · exact .inr ⟨v₁, v₂, pair, hv₁, hv₂, hfound, hvalid⟩

/-- Two withdrawals items that pass for one header are equal.

Otherwise the search over the bytes of their withdrawals finds a Keccak-256 collision. -/
theorem checkWithdrawals_binding {header : Header fork} {h : .shapella ≤ fork} {w₁ w₂ : Item}
    (h₁ : checkWithdrawals header h w₁ = .ok ()) (h₂ : checkWithdrawals header h w₂ = .ok ()) :
    WithdrawalsBound w₁ w₂ := by
  unfold WithdrawalsBound
  obtain ⟨ws₁, hd₁, hr₁⟩ := checkWithdrawals_eq_ok_iff.mp h₁
  obtain ⟨ws₂, hd₂, hr₂⟩ := checkWithdrawals_eq_ok_iff.mp h₂
  rcases withdrawalsRoot_binding hr₁ hr₂ with rfl | ⟨values₁, values₂, pair, hv₁, hv₂, hfound, hvalid⟩
  · exact .inl ((LawfulCodec.toItem_of_ofItem hd₁).symm.trans (LawfulCodec.toItem_of_ofItem hd₂))
  · exact .inr ⟨ws₁, ws₂, values₁, values₂, pair, hd₁, hd₂, hv₁, hv₂, hfound, hvalid⟩

/-- Two ommers items that pass for one header are equal.

Otherwise their encodings are a Keccak-256 collision. -/
theorem checkOmmers_binding {header : Header fork} {o₁ o₂ : Item}
    (h₁ : checkOmmers header o₁ = .ok ()) (h₂ : checkOmmers header o₂ = .ok ()) :
    OmmersBound o₁ o₂ := by
  unfold OmmersBound
  obtain ⟨e₁, he₁, hk₁⟩ := checkOmmers_hash h₁
  obtain ⟨e₂, he₂, hk₂⟩ := checkOmmers_hash h₂
  by_cases heq : e₁ = e₂
  · subst heq
    exact .inl (encode_injective o₁ o₂ e₁ he₁ he₂)
  · exact .inr ⟨e₁, e₂, he₁, he₂, heq, hk₁.trans hk₂.symm⟩

/-- Binding of a body to its header.

Two bodies that pass for one header have the same parts, up to a Keccak-256 collision.

- Their transactions have the same bytes, or the bytes give a collision.
- From Shapella, their withdrawals are equal, or the bytes of the withdrawals give a collision.
- Their ommers lists are equal, or their encodings are a collision. -/
theorem checkBody_binding {header : Header fork} {x₁ x₂ : Item}
    (h₁ : checkBody header x₁ = .ok ()) (h₂ : checkBody header x₂ = .ok ()) :
    ∃ t₁ o₁ t₂ o₂, TransactionsBound t₁ t₂ ∧ OmmersBound o₁ o₂ ∧
      (¬ .shapella ≤ fork → x₁ = .list [t₁, o₁] ∧ x₂ = .list [t₂, o₂]) ∧
      (.shapella ≤ fork → ∃ w₁ w₂, WithdrawalsBound w₁ w₂ ∧
        x₁ = .list [t₁, o₁, w₁] ∧ x₂ = .list [t₂, o₂, w₂]) := by
  obtain ⟨t₁, o₁, ht₁, ho₁, hn₁, hs₁⟩ := checkBody_eq_ok h₁
  obtain ⟨t₂, o₂, ht₂, ho₂, hn₂, hs₂⟩ := checkBody_eq_ok h₂
  refine ⟨t₁, o₁, t₂, o₂, checkTransactions_binding ht₁ ht₂, checkOmmers_binding ho₁ ho₂,
    fun hf => ⟨hn₁ hf, hn₂ hf⟩, fun hf => ?_⟩
  obtain ⟨w₁, hw₁, hx₁⟩ := hs₁ hf
  obtain ⟨w₂, hw₂, hx₂⟩ := hs₂ hf
  exact ⟨w₁, w₂, checkWithdrawals_binding hw₁ hw₂, hx₁, hx₂⟩

/-! ## Completeness -/

/-- A block that passes its checks has transactions that all encode as items of a body. -/
theorem checkBlock_transactions {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {block : Block fork Transaction}
    (h : checkBlock config checkSeal recent block = .ok ()) :
    ∃ items, block.transactions.mapM bodyItem = .ok items := by
  unfold checkBlock at h
  obtain ⟨_, hitems, -⟩ := bind_ok_iff.mp h
  unfold bodyItems at hitems
  cases hm : block.transactions.mapM bodyItem with
  | error e => simp [hm, Except.mapError, bind, Except.bind] at hitems
  | ok items => exact ⟨items, rfl⟩

/-- From Paris, a block that passes its checks has no ommers, and its header commits to none. -/
theorem checkBlock_paris {config : ChainConfig} {checkSeal : Bool}
    {recent : List RecentBlock} {block : Block fork Transaction} (hp : ¬ fork < .paris)
    (h : checkBlock config checkSeal recent block = .ok ()) :
    block.ommers = [] ∧ block.header.ommersHash = EMPTY_OMMER_HASH := by
  unfold checkBlock at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  split at h
  · rename_i parent hparent
    by_cases hF : parent.fork ≤ fork
    · simp only [hF, ↓reduceDIte] at h
      have hhead : checkHeader hF parent.header block.header
          (Fees.BlobBaseFee.chainBlobSchedule config fork block.header.number
            block.header.timestamp.toNat) = .ok () := by
        cases hs : checkSeal
        · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
          cases hc : checkHeader hF parent.header block.header
              (Fees.BlobBaseFee.chainBlobSchedule config fork block.header.number
                block.header.timestamp.toNat) with
          | ok u => rfl
          | error e => simp [hc, bind, Except.bind] at h
        · simp only [hs, ↓reduceIte] at h
          cases hc : validateHeader hF parent.header block.header
              (Fees.BlobBaseFee.chainBlobSchedule config fork block.header.number
                block.header.timestamp.toNat) with
          | ok u => exact checkHeader_of_validateHeader hc
          | error e => simp [hc, bind, Except.bind] at h
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hpar, -⟩ := checkHeader_eq_ok_iff.mp hhead
      refine ⟨?_, (hpar hp).2.2⟩
      refine Classical.byContradiction fun hne => ?_
      have hne' : ¬ block.ommers.isEmpty = true := fun he => hne (List.isEmpty_iff.mp he)
      cases hs : checkSeal
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
        simp [hhead, bind, Except.bind, hp, hne', throw, throwThe, MonadExceptOf.throw] at h
        split at h <;> cases h
      · simp only [hs, ↓reduceIte] at h
        cases hc : validateHeader hF parent.header block.header
            (Fees.BlobBaseFee.chainBlobSchedule config fork block.header.number
              block.header.timestamp.toNat) with
        | ok u =>
          simp [hc, bind, Except.bind, hp, hne', throw, throwThe, MonadExceptOf.throw] at h
          split at h <;> cases h
        | error e => simp [hc, bind, Except.bind] at h
    · simp [hF, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The bytes that a transaction item stands for are the bytes of the transaction. -/
theorem transactionBytes_bodyItem {tx : Transaction} {item : Item}
    (h : bodyItem tx = .ok item) : transactionBytes item = encodeTransaction tx := by
  by_cases hl : ∃ t, tx = .legacy t
  · obtain ⟨t, rfl⟩ := hl
    simp only [bodyItem, Except.ok.injEq] at h
    subst h
    rfl
  · have hb : bodyItem tx = .bytes <$> encodeTransaction tx := by
      cases tx <;> first | rfl | exact absurd ⟨_, rfl⟩ hl
    rw [hb] at h
    cases he : encodeTransaction tx with
    | error e => simp only [he, Functor.map, Except.map] at h; cases h
    | ok b =>
      simp only [he, Functor.map, Except.map, Except.ok.injEq] at h
      subst h
      simp [transactionBytes]

/-- The items of the transactions of a body have the bytes of the transactions. -/
theorem mapM_transactionBytes {txs : List Transaction} {items : List Item}
    (h : txs.mapM bodyItem = .ok items) :
    items.mapM transactionBytes = txs.mapM encodeTransaction := by
  induction txs generalizing items with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; rfl
  | cons tx txs ih =>
    obtain ⟨item, rest, hi, hr, rfl⟩ := mapM_cons_ok.mp h
    rw [List.mapM_cons, List.mapM_cons, transactionBytes_bodyItem hi, ih hr]

/-- The number of the header of an encoded header is its number. -/
theorem headerNumber_toItem (h : Header fork) : headerNumber (Codec.toItem h) = .ok h.number := by
  rw [Header.toItem_eq]
  simp [headerNumber, HEADER_NUMBER_INDEX, Item.toItems, bind, Except.bind]
  exact LawfulCodec.ofItem_toItem _

/-- The roots of an output hold the transactions root of the transactions. -/
theorem outputRoots_transactions {transactions : List Transaction}
    {withdrawals : Since .shapella fork (List Withdrawal)} {output : BlockOutput fork}
    {post : State} {roots : OutputRoots}
    (h : outputRoots transactions withdrawals output post = .ok roots) :
    transactionsRoot transactions = .ok roots.transactions := by
  unfold outputRoots at h
  obtain ⟨_, htx, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  cases h
  exact mapError_ok_iff.mp htx

/-- From Shapella, the roots of an output hold the withdrawals root of the withdrawals. -/
theorem outputRoots_withdrawals {transactions : List Transaction}
    {withdrawals : Since .shapella fork (List Withdrawal)} {output : BlockOutput fork}
    {post : State} {roots : OutputRoots} (hs : .shapella ≤ fork)
    (h : outputRoots transactions withdrawals output post = .ok roots) :
    ∃ r, withdrawalsRoot (withdrawals hs) = .ok r ∧ roots.withdrawals = some r := by
  unfold outputRoots at h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_ok_iff.mp h
  cases h
  simp only [withdrawalsRootOf, hs, ↓reduceDIte] at hw
  cases hr : withdrawalsRoot (withdrawals hs) with
  | error e => simp only [hr, Functor.map, Except.map, Except.mapError] at hw; cases hw
  | ok r =>
    simp only [hr, Functor.map, Except.map, Except.mapError, Except.ok.injEq] at hw
    exact ⟨r, rfl, hw.symm⟩

/-- A block that passes the checks against its output has the transactions root of its body. -/
theorem outputChecks_transactions {header : Header fork} {output : BlockOutput fork}
    {roots : OutputRoots} (h : firstFailure (outputChecks header output roots) = .ok ()) :
    roots.transactions = header.transactionsRoot := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have := all (decide (roots.transactions = header.transactionsRoot), .wrongTransactionsRoot)
    (by simp [outputChecks])
  simpa using this

/-- From Shapella, a block that passes the checks against its output has the withdrawals root of
its body. -/
theorem outputChecks_withdrawals {header : Header fork} {output : BlockOutput fork}
    {roots : OutputRoots} (hs : .shapella ≤ fork)
    (h : firstFailure (outputChecks header output roots) = .ok ()) :
    roots.withdrawals = some (header.withdrawalsRoot hs) := by
  have all := (firstFailure_eq_ok_iff _).mp h
  have := all (decide (roots.withdrawals = some (header.withdrawalsRoot hs)),
    .wrongWithdrawalsRoot) (by simp [outputChecks, hs])
  simpa using this

/-- Ommers whose encoding has the ommers hash of the header, in number and in count, pass. -/
theorem checkOmmers_of_valid {header : Header fork}
    {ommers : List ((f : Fork) × Header f)} {encoded : ByteArray}
    (henc : encode (ommersItem ommers) = .ok encoded)
    (hhash : Cryptography.Hash.Keccak.keccak256 encoded = header.ommersHash)
    (hcount : ommers.length ≤ MAX_OMMERS)
    (hnumber : ∀ ommer ∈ ommers, ommer.2.number ≤ header.number) :
    checkOmmers header (ommersItem ommers) = .ok () := by
  have hb : (Cryptography.Hash.Keccak.keccak256 encoded == header.ommersHash) = true := by
    rw [hhash]; exact beq_self_eq_true _
  have hit : (ommersItem ommers).toItems = .ok (ommers.map fun o => Codec.toItem o.2) := rfl
  unfold checkOmmers
  rw [hit]
  simp only [Except.mapError, bind, Except.bind, ensure, List.length_map, hcount, ↓reduceIte, henc,
    hb]
  refine forM_ok_iff.mpr fun (i, item) hm => ?_
  obtain ⟨ommer, hmem, rfl⟩ := List.mem_map.mp (List.of_mem_zip hm).2
  simp only [headerNumber_toItem, hnumber ommer hmem, ↓reduceIte]

/-- Completeness: the body of a block that passes the transition passes the check against its
header. -/
theorem checkBody_complete {chain : BlockChain} {block : Block fork Transaction}
    {checkSeal : Bool} {post : State} (h : stateTransition chain block checkSeal = .ok post) :
    ∃ body, bodyOf block = .ok body ∧ checkBody block.header body = .ok () := by
  obtain ⟨-, -, hcheck, hashes, output, roots, -, -, hroots, hchecks, -⟩ := stateTransition_eq_ok h
  obtain ⟨items, hitems⟩ := checkBlock_transactions hcheck
  have htx : checkTransactions block.header (.list items) = .ok () := by
    refine checkTransactions_eq_ok_iff.mpr ?_
    have hroot := outputRoots_transactions hroots
    rw [outputChecks_transactions hchecks] at hroot
    obtain ⟨values, hvalues, hindexed⟩ := transactionsRoot_eq_ok_iff.mp hroot
    refine ⟨values, ?_, hindexed⟩
    simp [transactionValues, Item.toItems, bind, Except.bind, mapM_transactionBytes hitems,
      hvalues]
  have hom : checkOmmers block.header (ommersItem block.ommers) = .ok () := by
    by_cases hp : fork < .paris
    · obtain ⟨⟨e, he, hk⟩, hc, -, hn⟩ := validateOmmers_spec (checkBlock_validateOmmers hp hcheck)
      exact checkOmmers_of_valid he hk hc fun o hmem => Nat.le_of_lt (hn o hmem).2.1
    · obtain ⟨hempty, hhash⟩ := checkBlock_paris hp hcheck
      rw [hempty]
      exact checkOmmers_nil hhash
  by_cases hs : .shapella ≤ fork
  · have hw : checkWithdrawals block.header hs (Codec.toItem (block.withdrawals hs)) = .ok () := by
      obtain ⟨r, hr, hsome⟩ := outputRoots_withdrawals hs hroots
      have := hsome.symm.trans (outputChecks_withdrawals hs hchecks)
      cases this
      exact checkWithdrawals_eq_ok_iff.mpr ⟨_, LawfulCodec.ofItem_toItem _, hr⟩
    refine ⟨.list [.list items, ommersItem block.ommers, Codec.toItem (block.withdrawals hs)],
      by simp [bodyOf, hitems, Item.ofSince, hs]; rfl, ?_⟩
    simp only [checkBody, Item.toItems, Except.mapError, bind, Except.bind, hs, ↓reduceDIte, htx,
      hw, hom]
  · refine ⟨.list [.list items, ommersItem block.ommers],
      by simp [bodyOf, hitems, Item.ofSince, hs]; rfl, ?_⟩
    simp only [checkBody, Item.toItems, Except.mapError, bind, Except.bind, hs, ↓reduceDIte, htx,
      hom]

end EthLib.Execution.Network
