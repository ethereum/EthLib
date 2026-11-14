module

public import EthLib.Execution.Rpc.Simulate

/-!
# Proofs: the request of `eth_simulateV1`

The reader rejects a key outside the schema of block or account overrides.

It rejects an account override that gives both `state` and `stateDiff`.

A rejected block or account override rejects the whole request.

Each block keeps the number and the time that the request gives it.

With a positive block time and no number or time override, the numbers and the times increase.

The order check passes exactly when all numbers and times, gap blocks included, strictly increase.

An override sets each field that it gives, and keeps the others and the other accounts.

`stateDiff` keeps the slots that it does not name, and `state` clears them.

Filling the defaults of a call keeps every field that the call gives.
-/

public section

namespace EthLib.Execution.Rpc

open Lean (Json)
open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.State (State Account EMPTY_ACCOUNT StorageMap)
open EthLib.Cryptography.Hash.Keccak (keccak256)

/-! ## The reader -/

private theorem onlyKeys_rejects {kvs : Std.TreeMap.Raw String Json compare} {name : String}
    {value : Json} {keys : List String} (what : String) (hmem : (name, value) ∈ kvs.toList)
    (hk : name ∉ keys) : ∃ e, onlyKeys what keys (.obj kvs) = .error e := by
  unfold onlyKeys
  cases h : kvs.toList.find? fun (name, _) => !keys.contains name with
  | none =>
    have := List.find?_eq_none.1 h _ hmem
    simp_all
  | some p =>
    obtain ⟨n, v⟩ := p
    exact ⟨_, by simp only [h]; rfl⟩

/-- Block overrides with a key outside their schema are rejected. -/
theorem blockOverrides_unknown_key {kvs : Std.TreeMap.Raw String Json compare} {name : String}
    {value : Json} (hmem : (name, value) ∈ kvs.toList) (hk : name ∉ blockOverrideKeys)
    (b : BlockOverrides) : blockOverrides (.obj kvs) ≠ .ok b := by
  obtain ⟨e, he⟩ := onlyKeys_rejects "blockOverrides" hmem hk
  intro hb
  simp [blockOverrides, he, bind, Except.bind] at hb

/-- An account override with a key outside its schema is rejected. -/
theorem accountOverride_unknown_key {kvs : Std.TreeMap.Raw String Json compare} {name : String}
    {value : Json} (hmem : (name, value) ∈ kvs.toList) (hk : name ∉ accountOverrideKeys)
    (o : AccountOverride) : accountOverride (.obj kvs) ≠ .ok o := by
  obtain ⟨e, he⟩ := onlyKeys_rejects "account override" hmem hk
  intro hb
  simp [accountOverride, he, bind, Except.bind] at hb

/-- An account override that gives both `state` and `stateDiff` is rejected, even as `null`. -/
theorem accountOverride_state_and_stateDiff {kvs : Std.TreeMap.Raw String Json compare}
    {v1 v2 : Json} (hstate : ("state", v1) ∈ kvs.toList) (hdiff : ("stateDiff", v2) ∈ kvs.toList)
    (o : AccountOverride) : accountOverride (.obj kvs) ≠ .ok o := by
  intro ho
  have h1 : hasKey (.obj kvs) "state" = true := List.any_eq_true.2 ⟨_, hstate, by simp⟩
  have h2 : hasKey (.obj kvs) "stateDiff" = true := List.any_eq_true.2 ⟨_, hdiff, by simp⟩
  unfold accountOverride at ho
  cases hk : onlyKeys "account override" accountOverrideKeys (.obj kvs) with
  | error e => simp [hk, bind, Except.bind] at ho
  | ok u =>
    simp [hk, h1, h2, bind, Except.bind, reject, throw, throwThe, MonadExceptOf.throw] at ho

private theorem mapM_ne_ok {α β : Type} {f : α → Except String β} {x : α} :
    ∀ {l : List α}, x ∈ l → (∀ b, f x ≠ .ok b) → ∀ r, l.mapM f ≠ .ok r
  | [], h, _, _ => by simp at h
  | y :: l, h, hx, r => by
    intro hr
    rw [List.mapM_cons] at hr
    cases hy : f y with
    | error e =>
      simp [hy, bind, Except.bind] at hr
    | ok b =>
      simp only [hy, bind, Except.bind] at hr
      cases hl : l.mapM f with
      | error e => simp [hl] at hr
      | ok r' =>
        rcases List.mem_cons.1 h with rfl | hm
        · exact hx b hy
        · exact mapM_ne_ok hm hx r' hl

/-- A rejected account override rejects the overrides of its block. -/
theorem stateOverrides_rejects {kvs : Std.TreeMap.Raw String Json compare} {name : String}
    {value : Json} (hmem : (name, value) ∈ kvs.toList)
    (hbad : ∀ o, accountOverride value ≠ .ok o) (overrides : List (Address × AccountOverride)) :
    stateOverrides (.obj kvs) ≠ .ok overrides := by
  intro ho
  have hm := mapM_ne_ok (f := fun (x : String × Json) => match x with | (name, value) => do
    return (← address "address" (.str name), ← accountOverride value)) hmem
    (fun b hb => hbad b.2 (by
      cases ha : address "address" (.str name) with
      | error e => simp [ha, bind, Except.bind] at hb
      | ok a =>
        cases hc : accountOverride value with
        | error e => simp [ha, hc, bind, Except.bind] at hb
        | ok c =>
          simp [ha, hc, bind, Except.bind] at hb
          have hb' : (a, c) = b := Except.ok.inj hb
          subst hb'
          rfl))
  unfold stateOverrides at ho
  dsimp only at ho
  cases hl : kvs.toList.mapM (fun (name, value) => do
      return (← address "address" (.str name), ← accountOverride value)) with
  | error e => rw [hl] at ho; simp [bind, Except.bind] at ho
  | ok r => exact hm r hl

/-- Rejected block overrides reject their block. -/
theorem blockStateCall_rejects_blockOverrides {j : Json} {fs : List (String × Json)}
    (hfs : fields "block state call" j = .ok fs) {o : Json}
    (ho : fs.lookup "blockOverrides" = some o) (hbad : ∀ b, blockOverrides o ≠ .ok b)
    (c : BlockStateCall) : blockStateCall j ≠ .ok c := by
  intro hc
  unfold blockStateCall at hc
  rw [hfs] at hc
  simp only [ho, bind, Except.bind, Option.mapM, Functor.map, Except.map] at hc
  cases hb : blockOverrides o with
  | error e => simp [hb] at hc
  | ok b => exact hbad b hb

/-- Rejected state overrides reject their block. -/
theorem blockStateCall_rejects_stateOverrides {j : Json} {fs : List (String × Json)}
    (hfs : fields "block state call" j = .ok fs) {o : Json}
    (ho : fs.lookup "stateOverrides" = some o) (hbad : ∀ s, stateOverrides o ≠ .ok s)
    (c : BlockStateCall) : blockStateCall j ≠ .ok c := by
  intro hc
  unfold blockStateCall at hc
  rw [hfs] at hc
  simp only [ho, bind, Except.bind, Option.mapM, Functor.map, Except.map] at hc
  cases hb : stateOverrides o with
  | error e =>
    cases hq : (fs.lookup "blockOverrides") with
    | none => simp [hb, hq, pure, Except.pure] at hc
    | some v =>
      simp only [hb, hq] at hc
      cases hv : blockOverrides v <;> simp [hv] at hc
  | ok b => exact hbad b hb

/-- A rejected block rejects the request. -/
theorem simulatePayload_rejects {j : Json} {fs : List (String × Json)}
    (hfs : fields "payload" j = .ok fs) {items : Array Json}
    (hcalls : fs.lookup "blockStateCalls" = some (.arr items)) {c : Json} (hc : c ∈ items.toList)
    (hbad : ∀ b, blockStateCall c ≠ .ok b) (p : SimulatePayload) :
    simulatePayload j ≠ .ok p := by
  intro hp
  have hm := mapM_ne_ok hc hbad
  unfold simulatePayload at hp
  rw [hfs] at hp
  simp only [bind, Except.bind, field, hcalls, array] at hp
  cases hl : items.toList.mapM blockStateCall with
  | error e => simp [hl, pure, Except.pure] at hp
  | ok r => exact hm r hl

/-! ## The defaults of a call -/

/-- A call keeps its type, or takes the type of a simulation. -/
theorem GenericTransaction.withDefaults_type (tx : GenericTransaction) (nonce gas : Nat) :
    (tx.withDefaults nonce gas).type = some (tx.type.getD tx.simulateType) := by
  cases h : tx.type <;> simp [GenericTransaction.withDefaults, GenericTransaction.simulateType, h]

/-- A call keeps its nonce, or takes the given one. -/
theorem GenericTransaction.withDefaults_nonce (tx : GenericTransaction) (nonce gas : Nat) :
    (tx.withDefaults nonce gas).nonce = some (tx.nonce.getD nonce) := rfl

/-- A call keeps its gas, or takes the given one. -/
theorem GenericTransaction.withDefaults_gas (tx : GenericTransaction) (nonce gas : Nat) :
    (tx.withDefaults nonce gas).gas = some (tx.gas.getD gas) := rfl

/-- A call keeps its sender, or takes the zero address. -/
theorem GenericTransaction.withDefaults_sender (tx : GenericTransaction) (nonce gas : Nat) :
    (tx.withDefaults nonce gas).sender = some (tx.sender.getD (Vector.replicate 20 0)) := rfl

/-- Filling the defaults of a call changes no field but the type, the nonce, the gas and the sender.
-/
theorem GenericTransaction.withDefaults_rest (tx : GenericTransaction) (nonce gas : Nat) :
    { tx.withDefaults nonce gas with
      type := tx.type, nonce := tx.nonce, gas := tx.gas, sender := tx.sender } = tx := rfl

/-! ## The sequence of blocks -/

private theorem checkOrder_cons_iff {blockTime number time : Nat} {b : PlannedBlock}
    {bs : List PlannedBlock} :
    checkOrder blockTime number time (b :: bs) = .ok () ↔
      number < b.number ∧ time + blockTime * b.gap < b.time ∧
        checkOrder blockTime b.number b.time bs = .ok () := by
  rw [checkOrder]
  by_cases h1 : number < b.number <;> by_cases h2 : time + blockTime * b.gap < b.time <;>
    simp only [ensure, h1, h2, ite_true, ite_false, bind, Except.bind, true_and, false_and,
      reduceCtorEq] <;> simp

private theorem pairwise_step {bt : Nat} (hbt : 0 < bt) {a τ gap n t : Nat}
    {rest : List (Nat × Nat)} (hgap : 0 < gap → n = a + 1 + gap) :
    List.Pairwise (fun x y : Nat × Nat => x.1 < y.1 ∧ x.2 < y.2)
        ((a, τ) :: ((List.range gap).map (fun i => (a + 1 + i, τ + bt * (i + 1))) ++
          (n, t) :: rest)) ↔
      (a < n ∧ τ + bt * gap < t) ∧
        List.Pairwise (fun x y : Nat × Nat => x.1 < y.1 ∧ x.2 < y.2) ((n, t) :: rest) := by
  have trans : ∀ x y z : Nat × Nat, (x.1 < y.1 ∧ x.2 < y.2) → (y.1 < z.1 ∧ y.2 < z.2) →
      (x.1 < z.1 ∧ x.2 < z.2) := fun x y z h1 h2 => ⟨by omega, by omega⟩
  have mono : ∀ i j : Nat, i < j → bt * (i + 1) < bt * (j + 1) := fun i j h =>
    Nat.mul_lt_mul_of_pos_left (by omega) hbt
  have monole : ∀ i : Nat, i < gap → bt * (i + 1) ≤ bt * gap := fun i h =>
    Nat.mul_le_mul_left _ (by omega)
  constructor
  · intro h
    rw [List.pairwise_cons] at h
    obtain ⟨h1, h2⟩ := h
    have hq := h1 (n, t) (by simp)
    have hrest := (List.pairwise_append.1 h2).2.1
    refine ⟨⟨hq.1, ?_⟩, hrest⟩
    rcases Nat.eq_zero_or_pos gap with rfl | hg
    · simpa using hq.2
    · have := (List.pairwise_append.1 h2).2.2 (a + 1 + (gap - 1), τ + bt * (gap - 1 + 1))
        (by simp; exact ⟨gap - 1, by omega, rfl, rfl⟩) (n, t) (by simp)
      have e : gap - 1 + 1 = gap := by omega
      simpa [e] using this.2
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hrest := List.pairwise_cons.1 h3
    rw [List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro y hy
      rw [List.mem_append] at hy
      rcases hy with hy | hy
      · simp only [List.mem_map, List.mem_range] at hy
        obtain ⟨i, hi, rfl⟩ := hy
        have := monole i hi
        have : 0 < bt * (i + 1) := Nat.mul_pos hbt (by omega)
        exact ⟨by omega, by omega⟩
      · rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨h1, by omega⟩
        · exact trans _ (n, t) _ ⟨h1, by omega⟩ (hrest.1 _ hy)
    · rw [List.pairwise_append]
      refine ⟨?_, h3, ?_⟩
      · rw [List.pairwise_map]
        refine List.Pairwise.imp_of_mem ?_ (List.pairwise_lt_range (n := gap))
        intro i j hi hj hij
        have := mono i j hij
        exact ⟨by simp; omega, by simp; omega⟩
      · intro x hx y hy
        simp only [List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hn := hgap (by omega)
        have hlt : (a + 1 + i < n ∧ τ + bt * (i + 1) < t) :=
          ⟨by omega, by have := monole i hi; omega⟩
        rcases List.mem_cons.1 hy with rfl | hy
        · exact hlt
        · exact trans _ (n, t) _ hlt (hrest.1 _ hy)

/-- Each planned block comes from the block of the request at its place. -/
theorem planBlocks_request (blockTime number time : Nat) (cs : List BlockStateCall) :
    (planBlocks blockTime number time cs).map (·.request) = cs := by
  induction cs generalizing number time with
  | nil => simp [planBlocks]
  | cons c cs ih => simp [planBlocks, ih]

/-- A block keeps the number that the request gives it. -/
theorem planBlocks_number {blockTime number time : Nat} {cs : List BlockStateCall}
    {b : PlannedBlock} (hb : b ∈ planBlocks blockTime number time cs) {n : Nat}
    (hn : b.request.blockOverrides.number = some n) : b.number = n := by
  induction cs generalizing number time with
  | nil => simp [planBlocks] at hb
  | cons c cs ih =>
    simp only [planBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp_all
    · exact ih hb

/-- A block keeps the time that the request gives it. -/
theorem planBlocks_time {blockTime number time : Nat} {cs : List BlockStateCall}
    {b : PlannedBlock} (hb : b ∈ planBlocks blockTime number time cs) {t : Nat}
    (ht : b.request.blockOverrides.time = some t) : b.time = t := by
  induction cs generalizing number time with
  | nil => simp [planBlocks] at hb
  | cons c cs ih =>
    simp only [planBlocks, List.mem_cons] at hb
    rcases hb with rfl | hb
    · simp_all
    · exact ih hb

/-- Without number and time overrides, the blocks pass the order check. -/
theorem checkOrder_planBlocks_of_none {blockTime : Nat} (hbt : 0 < blockTime)
    (number time : Nat) {cs : List BlockStateCall}
    (hcs : ∀ c ∈ cs, c.blockOverrides.number = none ∧ c.blockOverrides.time = none) :
    checkOrder blockTime number time (planBlocks blockTime number time cs) = .ok () := by
  induction cs generalizing number time with
  | nil => simp [planBlocks, checkOrder]
  | cons c cs ih =>
    obtain ⟨h1, h2⟩ := hcs c (by simp)
    have hlt : time + blockTime * (0 + 1) > time + blockTime * 0 := by
      have := Nat.mul_pos hbt (Nat.succ_pos 0)
      omega
    simp only [planBlocks, h1, h2, Option.getD_none,
      Nat.sub_self, Nat.zero_add] at ih ⊢
    rw [checkOrder_cons_iff]
    refine ⟨Nat.lt_succ_self _, by simpa using hbt, ?_⟩
    exact ih _ _ (fun c hc => hcs c (List.mem_cons_of_mem _ hc))

/-- The order check passes exactly when the numbers and the times strictly increase.

The sequence starts at the base block and holds every block, gap blocks included. -/
theorem checkOrder_planBlocks_iff {blockTime : Nat} (hbt : 0 < blockTime)
    (number time : Nat) (cs : List BlockStateCall) :
    checkOrder blockTime number time (planBlocks blockTime number time cs) = .ok () ↔
      List.Pairwise (fun x y => x.1 < y.1 ∧ x.2 < y.2)
        ((number, time) :: expandBlocks blockTime number time
          (planBlocks blockTime number time cs)) := by
  induction cs generalizing number time with
  | nil => simp [planBlocks, checkOrder, expandBlocks]
  | cons c cs ih =>
    simp only [planBlocks, expandBlocks]
    rw [checkOrder_cons_iff, ih, pairwise_step hbt]
    · simp only [and_assoc]
    · intro h
      omega

/-! ## The overrides of the state -/

private theorem foldl_insert_get (slots : List (Bytes32 × U256))
    (hslots : (slots.map (·.1)).Nodup) (m0 : Std.ExtTreeMap Bytes32 U256) (k : Bytes32) :
    (slots.foldl (fun m (p : Bytes32 × U256) => m.insert p.1 p.2) m0)[k]? =
      (slots.lookup k).or m0[k]? := by
  induction slots generalizing m0 with
  | nil => simp
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hslots
    simp only [List.foldl_cons]
    rw [ih hslots.2]
    by_cases hk : k' = k
    · subst hk
      have : rest.lookup k' = none := by
        rw [List.lookup_eq_none_iff]
        intro q hq
        simp only [bne_iff_ne, ne_eq]
        intro h
        exact hslots.1 ⟨q, hq, h.symm⟩
      simp [this]
    · have hk' : (k == k') = false := by simpa using Ne.symm hk
      simp [List.lookup_cons, Std.ExtTreeMap.getElem?_insert, hk, hk']

/-- The account at an address, the empty account when there is none. -/
abbrev accountAt (s : State) (a : Address) : Account :=
  (s.getAccountOptional a).getD EMPTY_ACCOUNT

/-- An override that sets the nonce gives the account that nonce. -/
theorem applyAccountOverride_nonce (s : State) (a : Address) {o : AccountOverride} {n : Nat}
    (h : o.nonce = some n) : (accountAt (applyAccountOverride s a o) a).nonce = n := by
  have hc : o.changesState = true := by simp [AccountOverride.changesState, h]
  simp [accountAt, applyAccountOverride, hc, State.getAccountOptional, h]

/-- An override that sets the balance gives the account that balance. -/
theorem applyAccountOverride_balance (s : State) (a : Address) {o : AccountOverride} {x : U256}
    (h : o.balance = some x) : (accountAt (applyAccountOverride s a o) a).balance = x := by
  have hc : o.changesState = true := by simp [AccountOverride.changesState, h]
  simp [accountAt, applyAccountOverride, hc, State.getAccountOptional, h]

/-- An override that sets the code gives the account its hash, and stores the code with it. -/
theorem applyAccountOverride_code (s : State) (a : Address) {o : AccountOverride}
    {c : ByteArray} (h : o.code = some c) :
    (accountAt (applyAccountOverride s a o) a).codeHash = keccak256 c ∧
      (applyAccountOverride s a o).code.get? (keccak256 c) = some c := by
  have hc : o.changesState = true := by simp [AccountOverride.changesState, h]
  refine ⟨?_, ?_⟩
  · simp [accountAt, applyAccountOverride, hc, State.getAccountOptional, h]
    rfl
  · simp only [applyAccountOverride, hc, h, ite_true]
    have key : ∀ (k : Hash32) (v : ByteArray), (s.code.insert k v).get? k = some v :=
      fun k v => by simp [Std.ExtTreeMap.get?_eq_getElem?]
    exact key _ _

/-- An override keeps the nonce that it does not set. -/
theorem applyAccountOverride_nonce_of_none (s : State) (a : Address) {o : AccountOverride}
    (h : o.nonce = none) :
    (accountAt (applyAccountOverride s a o) a).nonce = (accountAt s a).nonce := by
  unfold applyAccountOverride
  split <;> simp [accountAt, State.getAccountOptional, h]

/-- An override keeps the balance that it does not set. -/
theorem applyAccountOverride_balance_of_none (s : State) (a : Address) {o : AccountOverride}
    (h : o.balance = none) :
    (accountAt (applyAccountOverride s a o) a).balance = (accountAt s a).balance := by
  unfold applyAccountOverride
  split <;> simp [accountAt, State.getAccountOptional, h]

/-- An override keeps the code that it does not set. -/
theorem applyAccountOverride_codeHash_of_none (s : State) (a : Address) {o : AccountOverride}
    (h : o.code = none) :
    (accountAt (applyAccountOverride s a o) a).codeHash = (accountAt s a).codeHash := by
  unfold applyAccountOverride
  split <;> simp [accountAt, State.getAccountOptional, h] <;> rfl

/-- An override keeps the storage that it does not set. -/
theorem applyAccountOverride_storage_of_none (s : State) (a : Address) {o : AccountOverride}
    (h : o.storage = none) (k : Bytes32) :
    (applyAccountOverride s a o).getStorage a k = s.getStorage a k := by
  unfold applyAccountOverride
  split <;> simp [State.getStorage, StorageMap.slot, h]

/-- An override keeps every other account and its storage. -/
theorem applyAccountOverride_ne (s : State) {a b : Address} (o : AccountOverride) (h : b ≠ a)
    (k : Bytes32) :
    (applyAccountOverride s a o).getAccountOptional b = s.getAccountOptional b ∧
      (applyAccountOverride s a o).getStorage b k = s.getStorage b k := by
  unfold applyAccountOverride
  split
  · simp [State.getAccountOptional, State.getStorage, StorageMap.slot]
    rcases o.storage with _ | st <;> simp [Std.ExtTreeMap.getElem?_insert, Ne.symm h]
  · exact ⟨rfl, rfl⟩

/-- `stateDiff` sets the slots that it names and keeps the others. -/
theorem applyAccountOverride_stateDiff (s : State) (a : Address) {o : AccountOverride}
    {slots : List (Bytes32 × U256)} (h : o.storage = some (.diff slots))
    (hslots : (slots.map (·.1)).Nodup) (k : Bytes32) :
    (applyAccountOverride s a o).getStorage a k = (slots.lookup k).getD (s.getStorage a k) := by
  have hc : o.changesState = true := by simp [AccountOverride.changesState, h]
  simp only [State.getStorage, StorageMap.slot, applyAccountOverride, hc, ite_true, h,
    StorageOverride.apply, Std.ExtTreeMap.getElem?_insert_self, Option.bind_some]
  rw [foldl_insert_get _ hslots]
  cases hl : slots.lookup k <;> cases hs : s.storage[a]? <;>
    simp [Std.ExtTreeMap.getD_eq_getD_getElem?, hs]

/-- `state` sets the slots that it names and clears the others. -/
theorem applyAccountOverride_state (s : State) (a : Address) {o : AccountOverride}
    {slots : List (Bytes32 × U256)} (h : o.storage = some (.full slots))
    (hslots : (slots.map (·.1)).Nodup) (k : Bytes32) :
    (applyAccountOverride s a o).getStorage a k = (slots.lookup k).getD 0 := by
  have hc : o.changesState = true := by simp [AccountOverride.changesState, h]
  simp only [State.getStorage, StorageMap.slot, applyAccountOverride, hc, ite_true, h,
    StorageOverride.apply, Std.ExtTreeMap.getElem?_insert_self, Option.bind_some]
  rw [foldl_insert_get _ hslots]
  cases hl : slots.lookup k <;> simp

private theorem apply_ne (s : State) {a b : Address} (o : AccountOverride) (h : b ≠ a) :
    (applyAccountOverride s a o).accounts[b]? = s.accounts[b]? ∧
      (applyAccountOverride s a o).storage[b]? = s.storage[b]? := by
  unfold applyAccountOverride
  split
  · rcases o.storage with _ | st <;> simp [Std.ExtTreeMap.getElem?_insert, Ne.symm h]
  · exact ⟨rfl, rfl⟩

private theorem apply_agree {s1 s2 : State} (a : Address) (o : AccountOverride)
    (h1 : s1.accounts[a]? = s2.accounts[a]?) (h2 : s1.storage[a]? = s2.storage[a]?) :
    (applyAccountOverride s1 a o).accounts[a]? = (applyAccountOverride s2 a o).accounts[a]? ∧
      (applyAccountOverride s1 a o).storage[a]? = (applyAccountOverride s2 a o).storage[a]? := by
  unfold applyAccountOverride
  split
  · rcases o.storage with _ | st <;>
      simp [Std.ExtTreeMap.getD_eq_getD_getElem?, State.getAccountOptional, h1, h2]
  · exact ⟨h1, h2⟩

private theorem applyOverrides_not_mem_maps (s : State)
    {overrides : List (Address × AccountOverride)} {b : Address}
    (hb : b ∉ overrides.map (·.1)) :
    (applyOverrides s overrides).accounts[b]? = s.accounts[b]? ∧
      (applyOverrides s overrides).storage[b]? = s.storage[b]? := by
  induction overrides generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨a, o⟩ := p
    simp only [List.map_cons, List.mem_cons, not_or] at hb
    have := ih (applyAccountOverride s a o) hb.2
    have h2 := apply_ne s o hb.1
    exact ⟨this.1.trans h2.1, this.2.trans h2.2⟩

private theorem applyOverrides_mem_maps (s : State)
    {overrides : List (Address × AccountOverride)}
    (hnodup : (overrides.map (·.1)).Nodup) {a : Address} {o : AccountOverride}
    (hmem : (a, o) ∈ overrides) :
    (applyOverrides s overrides).accounts[a]? = (applyAccountOverride s a o).accounts[a]? ∧
      (applyOverrides s overrides).storage[a]? = (applyAccountOverride s a o).storage[a]? := by
  induction overrides generalizing s with
  | nil => simp at hmem
  | cons p rest ih =>
    obtain ⟨a0, o0⟩ := p
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnodup
    rcases List.mem_cons.1 hmem with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact applyOverrides_not_mem_maps _ (fun hm => hnodup.1 (by simpa using hm))
    · have hne : a ≠ a0 := fun e => hnodup.1 ⟨(a, o), h, e⟩
      have h1 := ih (applyAccountOverride s a0 o0) hnodup.2 h
      have h2 := apply_ne s o0 hne
      have h3 := apply_agree (s1 := applyAccountOverride s a0 o0) (s2 := s) a o h2.1 h2.2
      exact ⟨h1.1.trans h3.1, h1.2.trans h3.2⟩

/-- The overrides of a block keep every account that they do not name, and its storage. -/
theorem applyOverrides_not_mem (s : State) {overrides : List (Address × AccountOverride)}
    {b : Address} (hb : b ∉ overrides.map (·.1)) (k : Bytes32) :
    (applyOverrides s overrides).getAccountOptional b = s.getAccountOptional b ∧
      (applyOverrides s overrides).getStorage b k = s.getStorage b k := by
  have := applyOverrides_not_mem_maps s hb
  exact ⟨this.1, by simp [State.getStorage, StorageMap.slot, this.2]⟩

/-- The overrides of a block act on each account they name as its own override alone. -/
theorem applyOverrides_mem (s : State) {overrides : List (Address × AccountOverride)}
    (hnodup : (overrides.map (·.1)).Nodup) {a : Address} {o : AccountOverride}
    (hmem : (a, o) ∈ overrides) (k : Bytes32) :
    (applyOverrides s overrides).getAccountOptional a =
        (applyAccountOverride s a o).getAccountOptional a ∧
      (applyOverrides s overrides).getStorage a k =
        (applyAccountOverride s a o).getStorage a k := by
  have := applyOverrides_mem_maps s hnodup hmem
  exact ⟨this.1, by simp [State.getStorage, StorageMap.slot, this.2]⟩

end EthLib.Execution.Rpc
