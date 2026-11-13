module

public import EthLib.Execution.Rpc.Header
public import EthLib.Serialization.Proofs.JsonRpc
public import EthLib.Execution.Proofs.Rpc.Base
-- The fields of an encoded object unfold Lean's `Json.mkObj` and `Json.isNull`.
import all Lean.Data.Json.Basic

/-!
# Proofs: the JSON form of a header

The header object at a fork has one name for the hash and one for each field of the header.

So it has one name more than the RLP form of the header has items.

Its names are those of the fields of the fork, with no field from a later fork.

The reader of the fork reads back the header from the object that the writer gives.
-/

public section

namespace EthLib.Execution.Rpc

open EthLib.Base
open EthLib.Serialization.JsonRpc
open EthLib.Execution.Blocks (Header)

/-- The header object has one name more than the RLP form of the header has items. -/
theorem length_headerNames (fork : Fork) :
    (headerNames fork).length = Header.fieldCount fork + 1 := by
  cases fork <;> decide

/-- No name of the header object comes twice. -/
theorem nodup_headerNames (fork : Fork) : (headerNames fork).Nodup := by
  cases fork <;> decide

/-- The fields of a header object have the names of the fork, in order. -/
theorem names_headerFields {fork : Fork} (hash : Hash32) (h : Header fork) :
    (headerFields hash h).map Prod.fst = headerNames fork := by
  unfold headerFields headerNames sinceField sinceName
  by_cases h1 : Fork.london ≤ fork <;> by_cases h2 : Fork.shapella ≤ fork <;>
    by_cases h3 : Fork.dencun ≤ fork <;> by_cases h4 : Fork.pectra ≤ fork <;>
    by_cases h5 : Fork.glamsterdam ≤ fork <;> simp [h1, h2, h3, h4, h5]

/-- A computation that has succeeded passes its value on. -/
private theorem ok_bind {α β : Type} (a : α) (f : α → Read β) :
    (Except.ok a >>= f : Read β) = f a := rfl

/-- The reader of hashes reads back a hash that its writer writes. -/
private theorem hash32_hash32Json (what : String) (x : Hash32) :
    hash32 what (hash32Json x) = .ok x :=
  fixed_dataJson what x false

/-- The fields of a header have distinct names. -/
theorem names_distinct_headerFields {fork : Fork} (hash : Hash32) (h : Header fork) :
    (headerFields hash h).Pairwise fun a b => a.1 ≠ b.1 := by
  have := nodup_headerNames fork
  rw [← names_headerFields hash h, List.Nodup, List.pairwise_map] at this
  exact this

/-- No field of a header is `null`. -/
private theorem present {fork : Fork} (hash : Hash32) (h : Header fork) :
    ∀ p ∈ headerFields hash h, p.2.isNull = false := by
  intro p hp
  simp only [headerFields, sinceField, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with (((((((((hp | hp) | hp) | hp) | hp) | hp) | hp) | hp) | hp)) <;>
    first
    | (rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> exact isNull_str _)
    | (split at hp <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hp <;>
        first | (subst hp; exact isNull_str _) | cases hp)

/-- The writer succeeds only on a header with a hash, and then writes the object of the fields. -/
private theorem headerJson_ok {fork : Fork} {h : Header fork} {j : Lean.Json}
    (hj : headerJson h = .ok j) :
    ∃ hash, h.hash = .ok hash ∧ j = Lean.Json.mkObj (headerFields hash h) := by
  unfold headerJson at hj
  cases hh : h.hash with
  | error e => rw [hh] at hj; cases hj
  | ok hash =>
    rw [hh] at hj
    exact ⟨hash, rfl, (Except.ok.inj hj).symm⟩

/-- The object that the writer gives for a header has exactly the names of its fork. -/
theorem keys_headerJson {fork : Fork} {h : Header fork} {j : Lean.Json}
    (hj : headerJson h = .ok j) :
    ∃ kvs, j = .obj kvs ∧ (kvs.toList.map Prod.fst).Perm (headerNames fork) := by
  obtain ⟨hash, -, rfl⟩ := headerJson_ok hj
  obtain ⟨kvs, hobj, -, hmem, hd⟩ := toList_mkObj (names_distinct_headerFields hash h)
  refine ⟨kvs, hobj, ?_⟩
  have nodup : ∀ l : List (String × Lean.Json), (l.Pairwise fun a b => a.1 ≠ b.1) → l.Nodup :=
    fun l h => h.imp_of_mem (fun {a b} _ _ hne heq => hne (by rw [heq]))
  have hp : kvs.toList.Perm (headerFields hash h) :=
    (List.perm_ext_iff_of_nodup (nodup _ hd)
      (nodup _ (names_distinct_headerFields hash h))).mpr hmem
  rw [← names_headerFields hash h]
  exact hp.map _

/-- A field from a fork reads back its value, from the object of the fields. -/
private theorem readSince_of {f fork : Fork} {α : Type} {read : Lean.Json → Read α}
    {g : α → Lean.Json} {x : Since f fork α} {name : String}
    {fs pairs : List (String × Lean.Json)} (hp : fs.Perm pairs)
    (hd : pairs.Pairwise fun a b => a.1 ≠ b.1)
    (hm : ∀ h : f ≤ fork, (name, g (x h)) ∈ pairs)
    (hr : ∀ h : f ≤ fork, read (g (x h)) = .ok (x h)) :
    readSince fork read fs name = .ok x := by
  unfold readSince
  by_cases h : f ≤ fork
  · refine (dite_eq_left_of_eq_true (eq_true h)).trans ?_
    rw [field_of_perm hp hd (hm h)]
    simp only [ok_bind, hr h]
    exact congrArg Except.ok (funext fun _ => rfl)
  · refine (dite_eq_right_of_eq_false (eq_false h)).trans ?_
    exact congrArg Except.ok (funext fun h' => absurd h' h)

/-- A field from a fork is a field of its object. -/
private theorem mem_sinceField {f fork : Fork} {α : Type} {g : α → Lean.Json}
    {x : Since f fork α} {name : String} (hf : f ≤ fork) :
    (name, g (x hf)) ∈ sinceField name g x := by
  unfold sinceField
  refine (dite_eq_left_of_eq_true (eq_true hf)).symm ▸ ?_
  simp

/-- The reader of the fork reads back the header from the object that the writer gives. -/
theorem headerOfJson_headerJson {fork : Fork} {h : Header fork} {j : Lean.Json}
    (hj : headerJson h = .ok j) : headerOfJson fork j = .ok h := by
  obtain ⟨hash, hh, rfl⟩ := headerJson_ok hj
  have hd := names_distinct_headerFields hash h
  obtain ⟨fs, hfs, hp⟩ := fields_mkObj "header" hd (present hash h)
  have hex : hasExactly fs (headerNames fork) = true := by
    rw [← names_headerFields hash h]
    exact hasExactly_of_perm hp
  have rd : ∀ {k : String} {v : Lean.Json}, (k, v) ∈ headerFields hash h →
      field "header" fs k = .ok v := fun hm => field_of_perm hp hd hm
  unfold headerOfJson
  simp only [hfs, ok_bind]
  rw [ite_eq_left hex]
  have r1 := rd (k := "hash") (v := hash32Json hash) (by simp [headerFields])
  have r2 := rd (k := "parentHash") (v := hash32Json h.parentHash) (by simp [headerFields])
  have r3 := rd (k := "sha3Uncles") (v := hash32Json h.ommersHash) (by simp [headerFields])
  have r4 := rd (k := "miner") (v := dataJson h.coinbase.toList) (by simp [headerFields])
  have r5 := rd (k := "stateRoot") (v := hash32Json h.stateRoot) (by simp [headerFields])
  have r6 := rd (k := "transactionsRoot") (v := hash32Json h.transactionsRoot)
    (by simp [headerFields])
  have r7 := rd (k := "receiptsRoot") (v := hash32Json h.receiptRoot) (by simp [headerFields])
  have r8 := rd (k := "logsBloom") (v := dataJson h.bloom.toList) (by simp [headerFields])
  have r9 := rd (k := "difficulty") (v := quantityJson h.difficulty) (by simp [headerFields])
  have r10 := rd (k := "number") (v := quantityJson h.number) (by simp [headerFields])
  have r11 := rd (k := "gasLimit") (v := quantityJson h.gasLimit) (by simp [headerFields])
  have r12 := rd (k := "gasUsed") (v := quantityJson h.gasUsed) (by simp [headerFields])
  have r13 := rd (k := "timestamp") (v := quantityJson h.timestamp.toNat)
    (by simp [headerFields])
  have r14 := rd (k := "extraData") (v := dataJson h.extraData.data.toList)
    (by simp [headerFields])
  have r15 := rd (k := "mixHash") (v := hash32Json h.prevRandao) (by simp [headerFields])
  have r16 := rd (k := "nonce") (v := dataJson h.nonce.toList) (by simp [headerFields])
  have s1 : readSince fork (uint "baseFeePerGas") fs "baseFeePerGas" = .ok h.baseFeePerGas :=
    readSince_of hp hd (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => uint_quantityJson _ _)
  have s2 : readSince fork (hash32 "withdrawalsRoot") fs "withdrawalsRoot" =
      .ok h.withdrawalsRoot :=
    readSince_of hp hd (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => hash32_hash32Json _ _)
  have s3 : readSince fork (uint64 "blobGasUsed") fs "blobGasUsed" = .ok h.blobGasUsed :=
    readSince_of (g := fun x : UInt64 => quantityJson x.toNat) hp hd
      (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => uint64_toDigits _ _)
  have s4 : readSince fork (uint64 "excessBlobGas") fs "excessBlobGas" = .ok h.excessBlobGas :=
    readSince_of (g := fun x : UInt64 => quantityJson x.toNat) hp hd
      (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => uint64_toDigits _ _)
  have s5 : readSince fork (hash32 "parentBeaconBlockRoot") fs "parentBeaconBlockRoot" =
      .ok h.parentBeaconBlockRoot :=
    readSince_of hp hd (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => hash32_hash32Json _ _)
  have s6 : readSince fork (hash32 "requestsHash") fs "requestsHash" = .ok h.requestsHash :=
    readSince_of hp hd (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => hash32_hash32Json _ _)
  have s7 : readSince fork (hash32 "blockAccessListHash") fs "blockAccessListHash" =
      .ok h.blockAccessListHash :=
    readSince_of hp hd (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => hash32_hash32Json _ _)
  have s8 : readSince fork (uint64 "slotNumber") fs "slotNumber" = .ok h.slotNumber :=
    readSince_of (g := fun x : UInt64 => quantityJson x.toNat) hp hd
      (fun hf => by simp [headerFields, mem_sinceField hf])
      (fun _ => uint64_toDigits _ _)
  simp only [r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, s1, s2, s3,
    s4, s5, s6, s7, s8, ok_bind, hash32_hash32Json, address_dataJson, uint_quantityJson,
    uint256_quantityJson, bytes_dataJson]
  have b1 : bytes256 "logsBloom" (dataJson h.bloom.toList) = .ok h.bloom :=
    fixed_dataJson _ _ false
  have b2 : bytes8 "nonce" (dataJson h.nonce.toList) = .ok h.nonce := fixed_dataJson _ _ false
  simp only [b1, b2, ok_bind, hh, ite_true]
  rfl

end EthLib.Execution.Rpc
