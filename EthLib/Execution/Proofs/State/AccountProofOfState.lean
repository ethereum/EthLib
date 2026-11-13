module

public import EthLib.Execution.Proofs.State.AccountProof
import EthLib.Execution.Proofs.State.Account
import EthLib.Serialization.Proofs.Rlp.Codec

/-!
# Proofs: the answer of `eth_getProof` that a state gives passes the check

Take a state with a state root, and the answer that the state gives for an address and some slots.

The answer passes the check against that root.

It reports the account present exactly when the state has it.

Each slot of a present account is set exactly when the state holds a word other than zero there.

The proof assumes that an address with no account has the word zero at each slot asked for.

When the answer does not pass the check, a search finds two keys with one hash.

It looks among the address, the state's addresses, the slots asked for and the address's storage.
-/

@[expose] public section

namespace EthLib.Execution.State

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Serialization.Rlp

namespace AccountProof

/-- Two different keys with one hash among those that the tries of an answer read.

The first search looks at the address and the addresses of the state.

The second looks at the slots asked for and the keys of the storage of the address. -/
def findAnswerCollision (hash : ByteArray → Hash32) (state : State) (address : Address)
    (keys : List Bytes32) : Option (ByteArray × ByteArray) :=
  (findKeyCollision hash (⟨address.toArray⟩ :: state.accounts.keys.map fun a => ⟨a.toArray⟩)).or
    (findKeyCollision hash (keys.map (fun key => ⟨key.toArray⟩) ++
      (state.storage.getD address ∅).keys.map fun key => ⟨key.toArray⟩))

/-- Every pair that the search returns is a collision. -/
theorem findAnswerCollision_valid (hash : ByteArray → Hash32) {state : State} {address : Address}
    {keys : List Bytes32} {pair : ByteArray × ByteArray}
    (h : findAnswerCollision hash state address keys = some pair) : IsCollision hash pair := by
  unfold findAnswerCollision at h
  cases hfirst : findKeyCollision hash
      (⟨address.toArray⟩ :: state.accounts.keys.map fun a => ⟨a.toArray⟩) with
  | some found =>
    rw [hfirst] at h
    cases h
    exact findKeyCollision_valid hash _ hfirst
  | none =>
    rw [hfirst] at h
    exact findKeyCollision_valid hash _ h

/-- The search finds nothing in a state with no account and no storage, for no slot. -/
theorem findAnswerCollision_empty (hash : ByteArray → Hash32) (address : Address) :
    findAnswerCollision hash ⟨∅, ∅, ∅⟩ address [] = none := by
  have hstate : (∅ : Std.ExtTreeMap Address Account).keys = [] :=
    Std.ExtTreeMap.keys_eq_nil_iff.mpr rfl
  have hstorage : (∅ : Std.ExtTreeMap Bytes32 U256).keys = [] :=
    Std.ExtTreeMap.keys_eq_nil_iff.mpr rfl
  simp [findAnswerCollision, findKeyCollision, hstate, hstorage]

/-- Distinct keys among those of a list where the search finds nothing have no collision. -/
private theorem findKeyCollision_of_subset {hash : ByteArray → Hash32} {keys big : List ByteArray}
    (hnodup : keys.Nodup) (hsub : ∀ x ∈ keys, x ∈ big) (hnone : findKeyCollision hash big = none) :
    findKeyCollision hash keys = none :=
  findKeyCollision_of_nodup hash keys (List.pairwise_map.mpr (hnodup.imp_of_mem
    fun hx hy hne => hash_ne_of_findKeyCollision hash big hnone _ (hsub _ hx) _ (hsub _ hy) hne))

/-- A search by bytes finds the entry that a search by equality finds. -/
private theorem find_sameBytes (data : List (ByteArray × ByteArray)) (key : ByteArray) :
    (data.find? fun entry => sameBytes entry.1 key) = data.find? fun entry => entry.1 = key :=
  find?_congr data fun entry _ => by rw [Bool.eq_iff_iff, sameBytes_iff, decide_eq_true_iff]

/-- The keys of the state entries are the addresses of the state, as bytes. -/
private theorem stateEntries_keys {hash : ByteArray → Hash32} {state : State}
    {entries : List (ByteArray × ByteArray)} (h : stateEntries hash state = .ok entries) :
    entries.map Prod.fst = state.accounts.keys.map fun a => (⟨a.toArray⟩ : ByteArray) := by
  unfold stateEntries at h
  rw [map_of_mapM_ok (q := fun entry => (⟨entry.1.toArray⟩ : ByteArray)) ?_ h,
    ← Std.ExtTreeMap.map_fst_toList_eq_keys, List.map_map]
  · rfl
  · -- Each entry keeps the bytes of its address.
    intro entry result hentry
    cases hroot : storageRoot hash (state.storage.getD entry.1 ∅) with
    | error e => simp [hroot, bind, Except.bind] at hentry
    | ok storageHash =>
      cases hencode : encodeAccount entry.2 storageHash with
      | error e => simp [hroot, hencode, bind, Except.bind, Except.mapError] at hentry
      | ok encoded =>
        simp only [hroot, hencode, bind, Except.bind, pure, Except.pure, Except.mapError,
          Except.ok.injEq] at hentry
        rw [← hentry]

/-- Each key of the storage entries is a key of the storage, as bytes. -/
private theorem mem_storageEntries_keys {storage : Std.ExtTreeMap Bytes32 U256}
    {entries : List (ByteArray × ByteArray)} (h : storageEntries storage = .ok entries) :
    ∀ x ∈ entries.map Prod.fst, ∃ key ∈ storage.keys, x = ⟨key.toArray⟩ := by
  intro x hx
  obtain ⟨entry, hmem, rfl⟩ := List.mem_map.mp hx
  unfold storageEntries at h
  obtain ⟨⟨key, word⟩, hkw, hstep⟩ := mapM_ok_mem h entry hmem
  cases henc : (Codec.encode word : Except RlpError ByteArray) with
  | error e => simp [henc, bind, Except.bind] at hstep
  | ok bytes =>
    simp only [henc, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hstep
    subst hstep
    refine ⟨key, ?_, rfl⟩
    have hin : key ∈ storage.filter fun _ value => value != 0 :=
      Std.ExtTreeMap.isSome_getElem?_iff_mem.mp
        (by rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some.mp hkw]; rfl)
    exact Std.ExtTreeMap.mem_keys.mpr (Std.ExtTreeMap.mem_of_mem_filter hin)

/-- The slot checks pass on proofs that each pass on their own, with the outcome of their key. -/
private theorem verifySlots_of_mapM {hash : ByteArray → Hash32} {storageRoot : Hash32}
    {f : Bytes32 → Except TrieError StorageProof} {g : Bytes32 → SlotOutcome} :
    ∀ {keys : List Bytes32} {slots : List StorageProof} {index : Nat},
      keys.mapM f = .ok slots →
      (∀ key ∈ keys, ∀ s, f key = .ok s → ∀ i, verifySlot hash storageRoot i s = .ok (g key)) →
      verifySlots hash storageRoot index slots = .ok (keys.map g)
  | [], slots, index, hmap, _ => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at hmap
    subst hmap
    rfl
  | key :: rest, slots, index, hmap, hslot => by
    obtain ⟨s, others, hfirst, hrest, rfl⟩ := mapM_cons_ok.mp hmap
    have ih := verifySlots_of_mapM (index := index + 1) hrest
      fun k hk => hslot k (List.mem_cons_of_mem key hk)
    simp [verifySlots, hslot key List.mem_cons_self s hfirst index, ih, bind, Except.bind,
      pure, Except.pure]

/-- What the check of the answer that a state gives reports.

A present account comes with each slot, set when the state holds a word other than zero there. -/
def outcomeOfState (state : State) (address : Address) (keys : List Bytes32) : AccountOutcome :=
  match state.accounts[address]? with
  | some _ => .present (keys.map fun key =>
      if (state.storage.getD address ∅).getD key 0 = 0 then .absent else .set)
  | none => .absent

/-- Completeness: the answer that a state gives passes the check against the state root.

It reports the account present exactly when the state has it.

Each slot of a present account is set exactly when its word is not zero.

The proof assumes that an address with no account has the word zero at each slot asked for.

When the answer does not pass the check, the search finds two keys with one hash. -/
theorem verify_ofState {hash : ByteArray → Hash32} {state : State} {address : Address}
    {keys : List Bytes32} {stateRoot' : Hash32} {p : AccountProof}
    (hroot : stateRoot hash state = .ok stateRoot')
    (hp : ofState hash state address keys = .ok p)
    (hstorage : state.accounts[address]? = none →
      ∀ key ∈ keys, (state.storage.getD address ∅).getD key 0 = 0) :
    p.verify hash stateRoot' = .ok (outcomeOfState state address keys) ∨
      ∃ pair, findAnswerCollision hash state address keys = some pair ∧ IsCollision hash pair := by
  obtain ⟨entries, hentries, htrie⟩ := stateRoot_eq_ok_iff.mp hroot
  cases hsentries : storageEntries (state.storage.getD address ∅) with
  | error e =>
    cases hg : getProof hash ⟨true, entries⟩ ⟨address.toArray⟩ <;>
      simp [ofState, hentries, hsentries, hg, bind, Except.bind, Except.mapError] at hp
  | ok sentries =>
  cases haccProof : getProof hash ⟨true, entries⟩ ⟨address.toArray⟩ with
  | error e =>
    simp [ofState, hentries, haccProof, bind, Except.bind] at hp
  | ok accountProof =>
  simp only [ofState, hentries, hsentries, haccProof, bind, Except.bind, Except.mapError,
    pure, Except.pure] at hp
  cases hsearch : findAnswerCollision hash state address keys with
  | some pair => exact .inr ⟨pair, rfl, findAnswerCollision_valid hash hsearch⟩
  | none =>
  refine .inl ?_
  unfold findAnswerCollision at hsearch
  obtain ⟨hfirst, hsecond⟩ := Option.or_eq_none_iff.mp hsearch
  -- The address has the value of its own entry, since no address shares its hash.
  have hkeys := stateEntries_keys hentries
  have hvalue : valueAt hash ⟨true, entries⟩ ⟨address.toArray⟩ =
      (entries.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd := by
    rw [valueAt_secured hash ?_, find_sameBytes]
    intro other hother hne
    rw [hkeys] at hother
    exact hash_ne_of_findKeyCollision hash _ hfirst other (List.mem_cons_of_mem _ hother) _
      List.mem_cons_self hne
  have hpaths : (entries.map fun entry => keyPath hash true entry.1).Nodup :=
    keyPath_nodup hash (trie := ⟨true, entries⟩) (stateEntries_nodup hentries) (by
      simp only [findPathCollision, ↓reduceIte]
      refine findKeyCollision_of_subset (stateEntries_nodup hentries) (fun x hx => ?_) hfirst
      rw [hkeys] at hx
      exact List.mem_cons_of_mem _ hx)
  have hfind := find_stateEntries hentries address
  cases hacc : state.accounts[address]? with
  | none =>
    simp only [hacc] at hp
    split at hp
    · cases hp
    rename_i slots hmap
    simp only [Except.ok.injEq] at hp
    have hnone : (entries.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd = none := by
      cases hf : (entries.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd with
      | none => rfl
      | some bytes =>
        rw [hf] at hfind
        obtain ⟨_, _, hsome, -⟩ := hfind
        rw [hacc] at hsome
        cases hsome
    have haccount := verifyAccount_getProof (stateRoot := stateRoot') (p := p) htrie rfl
      (by rw [← hp]; exact haccProof) hpaths
    rw [← hp] at haccount ⊢
    rw [hvalue, hnone] at haccount
    simp only [outcomeOfState, hacc]
    refine verify_eq_ok_absent_iff.mpr ⟨haccount ?_, fun s hs => ?_⟩
    · simp [absentFields, EMPTY_ACCOUNT]
    · obtain ⟨key, hk, hstep⟩ := mapM_ok_mem hmap s hs
      split at hstep
      · cases hstep
      simp only [Except.ok.injEq] at hstep
      subst hstep
      exact hstorage hacc key hk
  | some account =>
    simp only [hacc] at hp
    split at hp
    · cases hp
    rename_i storageHash hsroot
    split at hp
    · cases hp
    rename_i slots hmap
    simp only [Except.ok.injEq] at hp
    -- The entry of the address holds the account and the root of its storage.
    cases hf : (entries.find? fun entry => entry.1 = ⟨address.toArray⟩).map Prod.snd with
    | none =>
      rw [hf, hacc] at hfind
      cases hfind
    | some bytes =>
    rw [hf] at hfind
    obtain ⟨account', storageHash', hacc', hsr, henc⟩ := hfind
    rw [hacc] at hacc'
    cases hacc'
    obtain ⟨sentries', hsentries', hsroot'⟩ := storageRoot_eq_ok_iff.mp hsr
    rw [hsentries] at hsentries'
    cases hsentries'
    rw [hsroot] at hsroot'
    cases hsroot'
    have haccount := verifyAccount_getProof (stateRoot := stateRoot') (p := p) htrie rfl
      (by rw [← hp]; exact haccProof) hpaths
    simp only [outcomeOfState, hacc]
    rw [← hp] at haccount ⊢
    rw [hvalue, hf] at haccount
    -- No two slots or storage keys share a hash, so the storage trie has distinct paths.
    have hpathsS : (sentries.map fun entry => keyPath hash true entry.1).Nodup :=
      keyPath_nodup hash (trie := ⟨true, sentries⟩) (storageEntries_nodup hsentries) (by
        simp only [findPathCollision, ↓reduceIte]
        refine findKeyCollision_of_subset (storageEntries_nodup hsentries) (fun x hx => ?_)
          hsecond
        obtain ⟨k, hk, rfl⟩ := mem_storageEntries_keys hsentries x hx
        exact List.mem_append_right _ (List.mem_map_of_mem hk))
    refine verify_eq_ok_present_iff.mpr ⟨haccount ?_, verifySlots_of_mapM hmap ?_⟩
    · simpa [AccountProof.account] using decodeAccount_encodeAccount henc
    intro key hk s hs i
    split at hs
    · cases hs
    rename_i proof hproof
    simp only [Except.ok.injEq] at hs
    subst hs
    have hvalueS : valueAt hash ⟨true, sentries⟩ ⟨key.toArray⟩ =
        (sentries.find? fun entry => entry.1 = ⟨key.toArray⟩).map Prod.snd := by
      rw [valueAt_secured hash ?_, find_sameBytes]
      intro other hother hne
      obtain ⟨k, hk', rfl⟩ := mem_storageEntries_keys hsentries other hother
      exact hash_ne_of_findKeyCollision hash _ hsecond _
        (List.mem_append_right _ (List.mem_map_of_mem hk')) _
        (List.mem_append_left _ (List.mem_map_of_mem hk)) hne
    have hslot := verifySlot_getProof (index := i)
      (s := ⟨key, (state.storage.getD address ∅).getD key 0, proof⟩) hsroot rfl hproof hpathsS
    rw [hvalueS] at hslot
    have hfs := find_storageEntries hsentries key
    cases hfs' : (sentries.find? fun entry => entry.1 = ⟨key.toArray⟩).map Prod.snd with
    | none =>
      rw [hfs'] at hslot hfs
      simp only [hfs, ↓reduceIte]
      rw [hfs] at hslot
      exact hslot rfl
    | some b =>
      rw [hfs'] at hslot hfs
      obtain ⟨word, hw, hne, hencw⟩ := hfs
      simp only [hw, hne, ↓reduceIte]
      rw [hw] at hslot
      exact hslot (Codec.decode_encode hencw)

end AccountProof

end EthLib.Execution.State
