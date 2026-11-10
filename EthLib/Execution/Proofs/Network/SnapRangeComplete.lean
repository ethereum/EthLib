module

public import EthLib.Execution.Proofs.Network.Snap
public import EthLib.Execution.Proofs.Network.SnapRange
public import EthLib.Execution.Proofs.Trie.RangeComplete

/-!
# Proofs: honest snap ranges pass the checks

An honest AccountRange answer sends the slim encodings of accounts of a secured state trie.

The check converts them to their full encodings before checking the range.

An honest StorageRanges answer sends whole tries before its last, possibly partial, range.

The keys are listed by increasing hash, the order of a secured trie.

So the keys of each trie have distinct hashes.

As for the range check of a trie, acceptance fails only when the node search returns a collision.

Whole tries need no proof and pass without that qualification.

The requests are [GetAccountRange (0x00)][get-account] and [GetStorageRanges (0x02)][get-storage].

The answers are in [AccountRange (0x01)][account] and [StorageRanges (0x03)][storage].

The slim form of an account is in [Data format][format].

[get-account]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#getaccountrange-0x00
[account]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#accountrange-0x01
[get-storage]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#getstorageranges-0x02
[storage]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#storageranges-0x03
[format]: https://github.com/ethereum/devp2p/blob/88f1c80800d622cc3a542a2125bbe33cc18c9f9c/caps/snap.md#data-format
-/

@[expose] public section

namespace EthLib.Execution.Network

open EthLib.Base
open EthLib.Execution.Trie
open EthLib.Cryptography.Hash.Keccak
open EthLib.Serialization.Rlp

/-- An account, its key, and its successful slim and full encodings.

Encoding success is explicit because an account nonce is an unbounded natural number. -/
structure AccountRangeWitness where
  /-- The address whose hash is the account's path. -/
  key : ByteArray
  /-- The account held at the address. -/
  account : State.Account
  /-- The root of the account's storage trie. -/
  storageRoot : Hash32
  /-- The slim encoding sent by the peer. -/
  slim : ByteArray
  /-- The full encoding held in the state trie. -/
  full : ByteArray
  /-- The sent bytes encode the account in slim form. -/
  encode_slim : encode (slimAccount account storageRoot) = .ok slim
  /-- The stored bytes encode the same account in full form. -/
  encode_full : State.encodeAccount account storageRoot = .ok full

/-- The key and full encoding of an account in the secured trie. -/
def AccountRangeWitness.trieEntry (a : AccountRangeWitness) : ByteArray × ByteArray :=
  (a.key, a.full)

/-- The hashed key and full encoding used by the range check. -/
def AccountRangeWitness.hashedEntry (a : AccountRangeWitness) : Hash32 × ByteArray :=
  (keccak256 a.key, a.full)

/-- The hashed key and slim encoding sent in an AccountRange answer. -/
def AccountRangeWitness.rangeEntry (a : AccountRangeWitness) : RangeEntry :=
  ⟨keccak256 a.key, a.slim⟩

/-- The account check accepts a range whose conversion and trie check succeed. -/
private theorem verifyAccountRange_of_checks {root' start : Hash32}
    {accounts : List RangeEntry} {entries : List (Hash32 × ByteArray)}
    {proof : List ByteArray} {more : Bool}
    (hstate : accounts ≠ [] ∨ proof ≠ [])
    (hconvert : accounts.mapM (fun entry => do
      let some value := fullAccount entry.data | Except.error SnapRangeError.slimAccount
      Except.ok (entry.hash, value)) = .ok entries)
    (hcheck : verifyRange keccak256 root' start entries proof = .ok more) :
    verifyAccountRange root' start accounts proof = .ok (.ofMore more) := by
  have hempty : (accounts.isEmpty && proof.isEmpty) = false := by
    rcases hstate with h | h <;> simp [h]
  simp only [verifyAccountRange, hempty, Bool.false_eq_true, ↓reduceIte]
  erw [hconvert]
  simp [hcheck, Except.mapError, bind, Except.bind]
  rfl

/-- The account conversion gives the full encodings, in order. -/
private theorem mapM_accountRangeWitness (data : List AccountRangeWitness) :
    (data.map AccountRangeWitness.rangeEntry).mapM (fun entry => do
      let some value := fullAccount entry.data | Except.error SnapRangeError.slimAccount
      Except.ok (entry.hash, value)) = .ok (data.map AccountRangeWitness.hashedEntry) := by
  rw [List.mapM_map]
  apply mapM_eq_ok_map
  intro a _
  simp [AccountRangeWitness.rangeEntry, AccountRangeWitness.hashedEntry,
    fullAccount_encode_slimAccount a.encode_slim a.encode_full]

/-- The honest nonempty AccountRange from a secured trie passes, or a node collision is found.

The sent accounts are the first `count` accounts from `start`, listed by increasing hash.

The proof contains the proof of the start and of the last account.

Those proofs are taken in the plain trie of hashed keys, whose root is the secured trie's root. -/
theorem verifyAccountRange_complete {data sent : List AccountRangeWitness} {root' : Hash32}
    (start : Hash32) (count : Nat) {last : AccountRangeWitness}
    {first second proof : List ByteArray}
    (hroot : root keccak256 ⟨true, data.map AccountRangeWitness.trieEntry⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun a =>
      bytesToNibbleList ⟨(keccak256 a.key).toArray⟩) = true)
    (hsent : sent = (data.filter fun a => bytesToNibbleList ⟨start.toArray⟩ ≤
      bytesToNibbleList ⟨(keccak256 a.key).toArray⟩).take count)
    (hlast : sent.getLast? = some last)
    (hfirst : getProof keccak256
      ⟨false, data.map fun a => (⟨(keccak256 a.key).toArray⟩, a.full)⟩
      ⟨start.toArray⟩ = .ok first)
    (hsecond : getProof keccak256
      ⟨false, data.map fun a => (⟨(keccak256 a.key).toArray⟩, a.full)⟩
      ⟨(keccak256 last.key).toArray⟩ = .ok second)
    (hproof : ∀ x ∈ first ++ second, x ∈ proof) :
    verifyAccountRange root' start (sent.map AccountRangeWitness.rangeEntry) proof =
        .ok (.ofMore (data.any fun a => bytesToNibbleList ⟨(keccak256 last.key).toArray⟩ <
          bytesToNibbleList ⟨(keccak256 a.key).toArray⟩)) ∨
      ∃ pair, findCrossCollision keccak256 (first ++ second) proof = some pair ∧
        IsCollision keccak256 pair := by
  rw [root_secured_eq_plain keccak256] at hroot
  have hroot' : root keccak256
      ⟨false, (data.map AccountRangeWitness.hashedEntry).map fun e => (⟨e.1.toArray⟩, e.2)⟩ =
      .ok root' := by
    simpa [List.map_map, Function.comp_def, AccountRangeWitness.trieEntry,
      AccountRangeWitness.hashedEntry] using hroot
  have hentries : ((data.map AccountRangeWitness.hashedEntry).filter fun entry =>
      bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨entry.1.toArray⟩).take count =
      sent.map AccountRangeWitness.hashedEntry := by
    simp [hsent, List.filter_map, List.map_take, Function.comp_def,
      AccountRangeWitness.hashedEntry]
    rfl
  have h := verifyRange_complete keccak256 start count
    (data := data.map AccountRangeWitness.hashedEntry)
    (last := last.hashedEntry) hroot'
    (by simpa [List.map_map, Function.comp_def, AccountRangeWitness.hashedEntry] using hsorted)
    (by rw [hentries, List.getLast?_map, hlast]; rfl)
    (by simpa [List.map_map, Function.comp_def, AccountRangeWitness.hashedEntry] using hfirst)
    (by simpa [List.map_map, Function.comp_def, AccountRangeWitness.hashedEntry] using hsecond)
    hproof
  rcases h with hcheck | hcollision
  · refine .inl (verifyAccountRange_of_checks (.inl ?_) (mapM_accountRangeWitness sent) ?_)
    · intro hempty
      have := congrArg List.isEmpty hempty
      have hne : sent ≠ [] := by intro h; simp [h] at hlast
      simp [hne] at this
    · rw [hentries] at hcheck
      simp only [List.any_map, AccountRangeWitness.hashedEntry] at hcheck
      exact hcheck
  · exact .inr hcollision

/-- An empty honest AccountRange passes, or the node search returns a collision.

The trie holds no account at or after the start.

The proof contains the proof of the start, possibly with other nodes. -/
theorem verifyAccountRange_complete_nil {data : List AccountRangeWitness} {root' : Hash32}
    (start : Hash32) {first proof : List ByteArray}
    (hroot : root keccak256 ⟨true, data.map AccountRangeWitness.trieEntry⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun a =>
      bytesToNibbleList ⟨(keccak256 a.key).toArray⟩) = true)
    (hnone : ∀ a ∈ data,
      bytesToNibbleList ⟨(keccak256 a.key).toArray⟩ < bytesToNibbleList ⟨start.toArray⟩)
    (hfirst : getProof keccak256
      ⟨false, data.map fun a => (⟨(keccak256 a.key).toArray⟩, a.full)⟩
      ⟨start.toArray⟩ = .ok first) (hproof : ∀ x ∈ first, x ∈ proof) :
    verifyAccountRange root' start [] proof = .ok .toEnd ∨
      ∃ pair, findCrossCollision keccak256 first proof = some pair ∧
        IsCollision keccak256 pair := by
  rw [root_secured_eq_plain keccak256] at hroot
  have hroot' : root keccak256
      ⟨false, (data.map AccountRangeWitness.hashedEntry).map fun e => (⟨e.1.toArray⟩, e.2)⟩ =
      .ok root' := by
    simpa [List.map_map, Function.comp_def, AccountRangeWitness.trieEntry,
      AccountRangeWitness.hashedEntry] using hroot
  have h := verifyRange_complete_nil keccak256 start
    (data := data.map AccountRangeWitness.hashedEntry) hroot'
    (by simpa [List.map_map, Function.comp_def, AccountRangeWitness.hashedEntry] using hsorted)
    (by
      intro entry hentry
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hentry
      exact hnone a ha)
    (by simpa [List.map_map, Function.comp_def, AccountRangeWitness.hashedEntry] using hfirst)
    hproof
  rcases h with hcheck | hcollision
  · have hne : proof ≠ [] := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (getProof_ne_nil hfirst)
      exact List.ne_nil_of_mem (hproof x hx)
    exact .inl (verifyAccountRange_of_checks (.inr hne) rfl hcheck)
  · exact .inr hcollision

/-- An honest whole state trie passes without a proof.

Every account must be at or after the start.

An empty trie sent with no proof is the empty reply, read as a peer without the root's state. -/
theorem verifyAccountRange_whole {data : List AccountRangeWitness} {root' : Hash32}
    (start : Hash32)
    (hroot : root keccak256 ⟨true, data.map AccountRangeWitness.trieEntry⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun a =>
      bytesToNibbleList ⟨(keccak256 a.key).toArray⟩) = true)
    (hstart : ∀ a ∈ data,
      bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨(keccak256 a.key).toArray⟩) :
    verifyAccountRange root' start (data.map AccountRangeWitness.rangeEntry) [] =
      .ok (if data.isEmpty then .noState else .toEnd) := by
  by_cases hnil : data = []
  · subst hnil
    rfl
  have hne : data.map AccountRangeWitness.rangeEntry ≠ [] := by simpa using hnil
  simp only [List.isEmpty_eq_false_iff.mpr hnil, Bool.false_eq_true, ↓reduceIte]
  rw [root_secured_eq_plain keccak256] at hroot
  change verifyAccountRange root' start (data.map AccountRangeWitness.rangeEntry) [] =
    .ok (.ofMore false)
  apply verifyAccountRange_of_checks (.inl hne) (mapM_accountRangeWitness data)
  apply verifyRange_whole keccak256 start
  · simpa [List.map_map, Function.comp_def, AccountRangeWitness.trieEntry,
      AccountRangeWitness.hashedEntry] using hroot
  · simpa [List.map_map, Function.comp_def, AccountRangeWitness.hashedEntry] using hsorted
  · intro entry hentry
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hentry
    exact hstart a ha

/-! ## Storage ranges -/

/-- The slots of a storage trie with hashed keys, as a StorageRanges answer sends them. -/
def storageRangeEntries (data : List (ByteArray × ByteArray)) : List RangeEntry :=
  data.map fun entry => ⟨keccak256 entry.1, entry.2⟩

/-- The whole secured storage trie passes the range check without a proof. -/
private theorem verifyRange_storage_whole {data : List (ByteArray × ByteArray)}
    {root' start : Hash32}
    (hroot : root keccak256 ⟨true, data⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun entry =>
      bytesToNibbleList ⟨(keccak256 entry.1).toArray⟩) = true)
    (hstart : ∀ entry ∈ data,
      bytesToNibbleList ⟨start.toArray⟩ ≤ bytesToNibbleList ⟨(keccak256 entry.1).toArray⟩) :
    verifyRange keccak256 root' start
      ((storageRangeEntries data).map fun entry => (entry.hash, entry.data)) [] = .ok false := by
  simp only [storageRangeEntries, List.map_map, Function.comp_def]
  apply verifyRange_whole keccak256 start
  · simpa [root_secured_eq_plain keccak256, storageRangeEntries, List.map_map,
      Function.comp_def] using hroot
  · simpa [storageRangeEntries, List.map_map, Function.comp_def] using hsorted
  · intro entry hentry
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hentry
    exact hstart original horiginal

/-- The storage check passes when each earlier range is whole and the last range passes. -/
private theorem verifyStorageRanges_of_checks {roots : List Hash32} {start first : Hash32}
    {slots : List (List RangeEntry)} {proof : List ByteArray}
    {lastRoot : Hash32} {lastRange : List RangeEntry} {more : Bool}
    (hslots : slots ≠ []) (hlength : slots.length ≤ roots.length)
    (hfirst : first = if roots.length = 1 then start else Vector.replicate 32 0)
    (hlast : (roots.zip slots).getLast? = some (lastRoot, lastRange))
    (hwhole : ∀ pair ∈ (roots.zip slots).dropLast,
      verifyRange keccak256 pair.1 first
        (pair.2.map fun entry => (entry.hash, entry.data)) [] = .ok false)
    (hcheck : verifyRange keccak256 lastRoot first
      (lastRange.map fun entry => (entry.hash, entry.data)) proof = .ok more) :
    verifyStorageRanges roots start slots proof = .ok (.ofMore more) := by
  have hloop : forIn (roots.zip slots).dropLast PUnit.unit
      (fun (pair : Hash32 × List RangeEntry) (_ : PUnit) => (do
        discard ((verifyRange keccak256 pair.1 first
          (pair.2.map fun entry => (entry.hash, entry.data)) []).mapError SnapRangeError.range)
        pure (.yield PUnit.unit) : Except SnapRangeError (ForInStep PUnit))) = .ok PUnit.unit := by
    have hnd : ∀ pair : Hash32 × List RangeEntry,
        (do
          discard ((verifyRange keccak256 pair.1 first
            (pair.2.map fun entry => (entry.hash, entry.data)) []).mapError SnapRangeError.range)
          pure (.yield PUnit.unit) : Except SnapRangeError (ForInStep PUnit)) ≠
            Except.ok (ForInStep.done PUnit.unit) := by
      intro pair h
      obtain ⟨_, -, h⟩ := bind_ok_iff.mp h
      cases h
    apply (forIn_unit_ok_iff hnd).mpr
    intro pair hpair
    simp [hwhole pair hpair, Except.mapError, discard, Functor.mapConst, Except.map,
      bind, Except.bind]
    rfl
  simp only [verifyStorageRanges, List.isEmpty_eq_false_iff.mpr hslots, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Nat.not_lt.mpr hlength]
  rw [← hfirst]
  rw [hloop]
  simp [hlast, hcheck, Except.mapError, bind, Except.bind]
  rfl

/-- Whole secured tries before a checked last range pass the storage check. -/
private theorem verifyStorageRanges_of_secured_last
    (whole : List (Hash32 × List (ByteArray × ByteArray)))
    (root' start first : Hash32) (remaining : List Hash32)
    (lastRange : List RangeEntry) (proof : List ByteArray) (more : Bool)
    (hfirst : first = if (whole.map Prod.fst ++ root' :: remaining).length = 1 then start
      else Vector.replicate 32 0)
    (hwhole : ∀ entry ∈ whole, root keccak256 ⟨true, entry.2⟩ = .ok entry.1 ∧
      strictlyIncreasing (entry.2.map fun slot =>
        bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hcheck : verifyRange keccak256 root' first
      (lastRange.map fun entry => (entry.hash, entry.data)) proof = .ok more) :
    verifyStorageRanges (whole.map Prod.fst ++ root' :: remaining) start
        (whole.map (fun entry => storageRangeEntries entry.2) ++ [lastRange]) proof =
      .ok (.ofMore more) := by
  -- Unanswered accounts follow the last range and do not enter the checked prefix.
  have hzip : (whole.map Prod.fst ++ root' :: remaining).zip
      (whole.map (fun entry => storageRangeEntries entry.2) ++ [lastRange]) =
      whole.map (fun entry => (entry.1, storageRangeEntries entry.2)) ++
        [(root', lastRange)] := by
    rw [List.zip_append (by simp)]
    simp [List.zip_map']
  refine verifyStorageRanges_of_checks
    (lastRoot := root') (lastRange := lastRange) (by simp) (by simp) hfirst
    (by rw [hzip]; simp) ?_ hcheck
  · intro pair hpair
    rw [hzip, List.dropLast_concat] at hpair
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hpair
    obtain ⟨hroot, hsorted⟩ := hwhole entry hentry
    apply verifyRange_storage_whole hroot hsorted
    intro slot hslot
    have hmany : (whole.map Prod.fst ++ root' :: remaining).length ≠ 1 := by
      have : 0 < whole.length := List.length_pos_of_mem hentry
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    rw [hfirst, ite_eq_right hmany]
    exact zeroHash_path_le _

/-- Honest StorageRanges pass for one account or several, or a node collision is found.

`whole` lists the whole tries before the last range.

The last range sends the first `count` slots of `data` from `first`, in increasing hash order.

The proof contains the proofs of `first` and of the last slot.

`remaining` lists requested accounts after the last range.

For one requested account, `first` is `start`; for several, it is the zero hash. -/
theorem verifyStorageRanges_complete
    (whole : List (Hash32 × List (ByteArray × ByteArray)))
    (root' start first : Hash32) (remaining : List Hash32)
    {data sent : List (ByteArray × ByteArray)} (count : Nat)
    {last : ByteArray × ByteArray} {left right proof : List ByteArray}
    (hfirst : first = if (whole.map Prod.fst ++ root' :: remaining).length = 1 then start
      else Vector.replicate 32 0)
    (hwhole : ∀ entry ∈ whole, root keccak256 ⟨true, entry.2⟩ = .ok entry.1 ∧
      strictlyIncreasing (entry.2.map fun slot =>
        bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hroot : root keccak256 ⟨true, data⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun slot =>
      bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hsent : sent = (data.filter fun slot => bytesToNibbleList ⟨first.toArray⟩ ≤
      bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩).take count)
    (hlast : sent.getLast? = some last)
    (hleft : getProof keccak256
      ⟨false, data.map fun slot => (⟨(keccak256 slot.1).toArray⟩, slot.2)⟩
      ⟨first.toArray⟩ = .ok left)
    (hright : getProof keccak256
      ⟨false, data.map fun slot => (⟨(keccak256 slot.1).toArray⟩, slot.2)⟩
      ⟨(keccak256 last.1).toArray⟩ = .ok right)
    (hproof : ∀ x ∈ left ++ right, x ∈ proof) :
    verifyStorageRanges (whole.map Prod.fst ++ root' :: remaining) start
        (whole.map (fun entry => storageRangeEntries entry.2) ++ [storageRangeEntries sent])
        proof = .ok (.ofMore (data.any fun slot =>
          bytesToNibbleList ⟨(keccak256 last.1).toArray⟩ <
            bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩)) ∨
      ∃ pair, findCrossCollision keccak256 (left ++ right) proof = some pair ∧
        IsCollision keccak256 pair := by
  have hentries : ((data.map fun slot => (keccak256 slot.1, slot.2)).filter fun entry =>
      bytesToNibbleList ⟨first.toArray⟩ ≤ bytesToNibbleList ⟨entry.1.toArray⟩).take count =
      sent.map fun slot => (keccak256 slot.1, slot.2) := by
    simp [hsent, List.filter_map, List.map_take, Function.comp_def]
  have h := verifyRange_complete keccak256 first count
    (data := data.map fun slot => (keccak256 slot.1, slot.2))
    (last := (keccak256 last.1, last.2))
    (by simpa [root_secured_eq_plain keccak256, List.map_map, Function.comp_def] using hroot)
    (by simpa [List.map_map, Function.comp_def] using hsorted)
    (by erw [hentries, List.getLast?_map, hlast]; rfl)
    (by simpa [List.map_map, Function.comp_def] using hleft)
    (by simpa [List.map_map, Function.comp_def] using hright) hproof
  rcases h with hcheck | hcollision
  · refine .inl (verifyStorageRanges_of_secured_last whole root' start first remaining
      (storageRangeEntries sent) proof _ hfirst hwhole ?_)
    erw [hentries] at hcheck
    simp only [List.any_map] at hcheck
    simp only [storageRangeEntries, List.map_map]
    exact hcheck
  · exact .inr hcollision

/-- An honest empty last storage range passes, or the node search returns a collision.

The last trie has no slot at or after `first`, and its proof contains the proof of `first`. -/
theorem verifyStorageRanges_complete_nil
    (whole : List (Hash32 × List (ByteArray × ByteArray)))
    (root' start first : Hash32) (remaining : List Hash32)
    {data : List (ByteArray × ByteArray)} {left proof : List ByteArray}
    (hfirst : first = if (whole.map Prod.fst ++ root' :: remaining).length = 1 then start
      else Vector.replicate 32 0)
    (hwhole : ∀ entry ∈ whole, root keccak256 ⟨true, entry.2⟩ = .ok entry.1 ∧
      strictlyIncreasing (entry.2.map fun slot =>
        bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hroot : root keccak256 ⟨true, data⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun slot =>
      bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hnone : ∀ slot ∈ data,
      bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩ < bytesToNibbleList ⟨first.toArray⟩)
    (hleft : getProof keccak256
      ⟨false, data.map fun slot => (⟨(keccak256 slot.1).toArray⟩, slot.2)⟩
      ⟨first.toArray⟩ = .ok left) (hproof : ∀ x ∈ left, x ∈ proof) :
    verifyStorageRanges (whole.map Prod.fst ++ root' :: remaining) start
        (whole.map (fun entry => storageRangeEntries entry.2) ++ [[]]) proof = .ok .toEnd ∨
      ∃ pair, findCrossCollision keccak256 left proof = some pair ∧
        IsCollision keccak256 pair := by
  have h := verifyRange_complete_nil keccak256 first
    (data := data.map fun slot => (keccak256 slot.1, slot.2))
    (by simpa [root_secured_eq_plain keccak256, List.map_map, Function.comp_def] using hroot)
    (by simpa [List.map_map, Function.comp_def] using hsorted)
    (by
      intro slot hslot
      obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hslot
      exact hnone original horiginal)
    (by simpa [List.map_map, Function.comp_def] using hleft) hproof
  rcases h with hcheck | hcollision
  · exact .inl (verifyStorageRanges_of_secured_last whole root' start first remaining [] proof
      false hfirst hwhole hcheck)
  · exact .inr hcollision

/-- An honest storage answer containing only whole tries passes without a proof.

For one requested account, every sent slot must be at or after the requested start.

For several requested accounts each range starts at the zero hash, so every slot meets it. -/
theorem verifyStorageRanges_whole
    (whole : List (Hash32 × List (ByteArray × ByteArray)))
    (root' start first : Hash32) (remaining : List Hash32)
    {data : List (ByteArray × ByteArray)}
    (hfirst : first = if (whole.map Prod.fst ++ root' :: remaining).length = 1 then start
      else Vector.replicate 32 0)
    (hwhole : ∀ entry ∈ whole, root keccak256 ⟨true, entry.2⟩ = .ok entry.1 ∧
      strictlyIncreasing (entry.2.map fun slot =>
        bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hroot : root keccak256 ⟨true, data⟩ = .ok root')
    (hsorted : strictlyIncreasing (data.map fun slot =>
      bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) = true)
    (hstart : ∀ slot ∈ data,
      bytesToNibbleList ⟨first.toArray⟩ ≤ bytesToNibbleList ⟨(keccak256 slot.1).toArray⟩) :
    verifyStorageRanges (whole.map Prod.fst ++ root' :: remaining) start
        (whole.map (fun entry => storageRangeEntries entry.2) ++ [storageRangeEntries data]) [] =
      .ok .toEnd :=
  verifyStorageRanges_of_secured_last whole root' start first remaining (storageRangeEntries data)
    [] false hfirst hwhole (verifyRange_storage_whole hroot hsorted hstart)

end EthLib.Execution.Network
