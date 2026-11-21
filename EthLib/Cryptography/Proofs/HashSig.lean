module

public import EthLib.Base.Proofs.Bytes
public import EthLib.Cryptography.HashSig

/-!
# Proofs: the common frame of the hash-based signatures

A read of a fixed-size object succeeds exactly when the buffer has room, and reads back a write.

A read out of a concatenation reads the part it covers.

In the identity monad, a vector computed in order is the vector of its entries.

A map of monads that keeps `pure` and `bind` commutes with computing a vector in order.

Between lawful monads, such a map keeps `map` too.

The models of the security proofs compute a function in order instead of a vector.

Both make the same calls in the same order.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open EthLib.Base (packBytes readBytes readBytes_eq_ofFn_data readBytes_packBytes)

/-! ## Reading fixed-size objects -/

/-- Reading succeeds exactly when the buffer has room for the object.

Nothing weaker is accepted, so a caller cannot slip a short buffer through. -/
@[simp] theorem isSome_unpackBytes? {n : Nat} (b : ByteArray) (offset : Nat) :
    (unpackBytes? n b offset).isSome ↔ offset + n ≤ b.size := by
  -- Acceptance is the guard itself, so both branches close by case analysis.
  rw [unpackBytes?]
  split <;> simp_all

/-- Writing an object and reading it back returns the same object. -/
@[simp] theorem unpackBytes?_packBytes {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n (packBytes v) = some v := by
  -- A buffer holding exactly one object has room for it, so the guard passes.
  rw [unpackBytes?, dite_eq_left (by simp : 0 + n ≤ (packBytes v).size)]
  -- Reading back index `i` gives entry `i`, which rebuilds the object.
  exact congrArg some (readBytes_packBytes v _)

/-- Reading a full-length buffer and writing it back returns it unchanged.

So no buffer is unreachable, and no object has two encodings. -/
theorem packBytes_unpackBytes? {n : Nat} {b : ByteArray} (hb : b.size = n) :
    (unpackBytes? n b).map packBytes = some b := by
  -- A buffer of exactly the right length has room, so the guard passes.
  rw [unpackBytes?, dite_eq_left (by omega : 0 + n ≤ b.size)]
  simp only [Option.map_some, packBytes, readBytes_eq_ofFn_data, Vector.toArray_ofFn, Nat.zero_add]
  -- The object's length is the buffer's, so the read indices cover it exactly.
  have hdata : b.data.size = n := hb
  subst hdata
  -- Tabulating every entry of an array rebuilds that array.
  exact congrArg (some ∘ ByteArray.mk) Array.ofFn_getElem

/-- Reading back the raw array of an object returns that object. -/
@[simp] theorem unpackBytes?_toArray {n : Nat} (v : Vector UInt8 n) :
    unpackBytes? n ⟨v.toArray⟩ = some v :=
  unpackBytes?_packBytes v

/-! ## Reading out of a concatenation -/

/-- Two concatenations with first parts of the same size agree part by part. -/
theorem byteArray_append_inj {a b c d : ByteArray} (h : a ++ b = c ++ d) (hs : a.size = c.size) :
    a = c ∧ b = d := by
  have := congrArg ByteArray.data h
  simp only [ByteArray.data_append] at this
  obtain ⟨ha, hb⟩ := Array.append_inj this hs
  exact ⟨ByteArray.ext ha, ByteArray.ext hb⟩

/-- A read that ends inside the first part of a concatenation reads that part. -/
theorem readBytes_append_left {a b : ByteArray} {offset n : Nat} (h)
    (inside : offset + n ≤ a.size) :
    readBytes (a ++ b) offset n h = readBytes a offset n inside := by
  apply Vector.ext
  intro i hi
  simp only [readBytes_eq_ofFn_data, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_left (by simp only [ByteArray.size] at inside; omega)]

/-- A read that starts after the first part of a concatenation reads the second. -/
theorem readBytes_append_right {a b : ByteArray} {offset n : Nat} (h) :
    readBytes (a ++ b) (a.size + offset) n h
      = readBytes b offset n (by simp only [ByteArray.size_append] at h; omega) := by
  apply Vector.ext
  intro i hi
  simp only [readBytes_eq_ofFn_data, Vector.getElem_ofFn, ByteArray.data_append]
  rw [Array.getElem_append_right (by simp only [ByteArray.size]; omega)]
  -- The index past the first part is the index into the second.
  congr 1
  simp only [ByteArray.size]
  omega

/-- A read that covers exactly the middle part of a concatenation returns that part. -/
theorem readBytes_middle {b a c : ByteArray} {n : Nat} {v : Vector UInt8 n} {offset : Nat}
    (hb : b = a ++ packBytes v ++ c) (ho : offset = a.size) (h : offset + n ≤ b.size) :
    readBytes b offset n h = v := by
  subst hb ho
  -- Strip the last part, then the first, leaving the object itself.
  rw [readBytes_append_left _ (by simp)]
  have past := readBytes_append_right (a := a) (b := packBytes v) (offset := 0) (n := n)
    (by simp)
  simp only [Nat.add_zero] at past
  rw [past, readBytes_packBytes]

/-- The bytes of a read are the slice of the buffer it covers. -/
theorem packBytes_readBytes (b : ByteArray) (offset n : Nat) (h) :
    packBytes (readBytes b offset n h) = ⟨b.data.extract offset (offset + n)⟩ := by
  apply ByteArray.ext
  apply Array.ext
  · simp only [ByteArray.size] at h
    simp only [packBytes, readBytes_eq_ofFn_data, Vector.toArray_ofFn, Array.size_ofFn,
      Array.size_extract]
    omega
  · intro i h₁ h₂
    simp [packBytes, readBytes_eq_ofFn_data]

/-! ## Computing a vector in order -/

section Builder

/-- No entries make the empty vector. -/
theorem ofFnInOrder_zero {m : Type → Type} [Monad m] {α : Type} (f : Fin 0 → m α) :
    ofFnInOrder 0 f = pure #v[] :=
  rfl

/-- The builder after the results in `acc` appends the vector of the remaining entries.

The remaining entries are the indices from the size of `acc` on. -/
private theorem ofFnInOrder_go_eq {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} :
    ∀ (k n : Nat) (f : Fin n → m α) (acc : Array α) (h : acc.size + k = n),
      ofFnInOrder.go n f k acc h =
        (fun v : Vector α k => (⟨acc ++ v.toArray, by simp; omega⟩ : Vector α n)) <$>
          ofFnInOrder k fun j => f ⟨acc.size + j.val, by omega⟩
  | 0, n, f, acc, h => by
    rw [ofFnInOrder.go, ofFnInOrder_zero, map_pure]
    congr 1
  | k + 1, n, f, acc, h => by
    -- Both sides run the entry at the size of `acc` first, then the rest from one index on.
    rw [ofFnInOrder.go, ofFnInOrder, ofFnInOrder.go, map_bind]
    refine bind_congr fun x => ?_
    rw [ofFnInOrder_go_eq k n f (acc.push x), ofFnInOrder_go_eq k (k + 1), Functor.map_map]
    -- The rest starts at index `acc.size + 1` of `f` on both sides.
    have hrest : (fun j : Fin k => f ⟨(acc.push x).size + j.val, by simp; omega⟩) =
        fun j : Fin k => f ⟨acc.size + ((Array.emptyWithCapacity (k + 1)).push x).size + j.val,
          by simp; omega⟩ := by
      funext j
      congr 1
      ext
      simp only [Array.size_push, Array.emptyWithCapacity_eq, List.size_toArray, List.length_nil]
    simp only [Nat.add_assoc] at hrest ⊢
    rw [hrest]
    congr 1
    funext v
    apply Vector.ext
    intro i hi
    simp [Array.getElem_append, Array.getElem_push]

/-- Computing `n + 1` entries in order computes entry 0, then the `n` after it. -/
theorem ofFnInOrder_succ {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type} (n : Nat)
    (f : Fin (n + 1) → m α) :
    ofFnInOrder (n + 1) f = (do
      let head ← f 0
      let tail ← ofFnInOrder n fun i => f i.succ
      return (#v[head] ++ tail).cast (Nat.add_comm 1 n)) := by
  rw [ofFnInOrder, ofFnInOrder.go]
  refine bind_congr fun head => ?_
  rw [ofFnInOrder_go_eq, ← bind_pure_comp]
  -- Entry `i` of the rest is entry `i + 1`.
  have hrest : (fun j : Fin n =>
        f ⟨((Array.emptyWithCapacity (n + 1)).push head).size + j.val, by simp; omega⟩) =
      fun i : Fin n => f i.succ := by
    funext j
    congr 1
    ext
    simp only [Array.size_push, Array.emptyWithCapacity_eq, List.size_toArray, List.length_nil,
      Fin.val_succ]
    omega
  rw [hrest]
  refine bind_congr fun tail => ?_
  congr 1

end Builder

/-- In the identity monad, computing a vector in order is building it from its entries. -/
@[simp] theorem ofFnInOrder_run {α : Type} :
    ∀ (n : Nat) (f : Fin n → Id α), (ofFnInOrder n f).run = Vector.ofFn fun i => (f i).run
  | 0, _ => Vector.ext fun _ hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, f => by
    simp only [ofFnInOrder_succ, Id.run_bind, Id.run_pure, ofFnInOrder_run n]
    apply Vector.ext
    intro i hi
    -- Entry 0 is the head, entry `i + 1` is entry `i` of the tail.
    cases i with
    | zero => simp
    | succ i => simp [Fin.succ]

/-- The builder after `acc` commutes with a map of monads that keeps `pure` and `bind`. -/
private theorem ofFnInOrder_go_map_monad {m n : Type → Type} [Monad m] [Monad n]
    (φ : ∀ {β : Type}, m β → n β) (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
    (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
    {α : Type} {k : Nat} (f : Fin k → m α) :
    ∀ (r : Nat) (acc : Array α) (h : acc.size + r = k),
      φ (ofFnInOrder.go k f r acc h) = ofFnInOrder.go k (fun i => φ (f i)) r acc h
  | 0, _, _ => map_pure _
  | r + 1, acc, h => by
    rw [ofFnInOrder.go, ofFnInOrder.go, map_bind]
    exact bind_congr fun x => ofFnInOrder_go_map_monad φ map_pure map_bind f r _ _

/-- A map of monads that keeps `pure` and `bind` commutes with computing a vector in order. -/
theorem ofFnInOrder_map_monad {m n : Type → Type} [Monad m] [Monad n]
    (φ : ∀ {β : Type}, m β → n β) (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
    (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
    {α : Type} :
    ∀ (k : Nat) (f : Fin k → m α), φ (ofFnInOrder k f) = ofFnInOrder k fun i => φ (f i) :=
  fun k f => ofFnInOrder_go_map_monad φ map_pure map_bind f k _ _

/-! ## Maps of monads -/

/-- A map of lawful monads that keeps `pure` and `bind` keeps `map` too. -/
theorem map_monad_map {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
    (φ : ∀ {β : Type}, m β → n β) (map_pure : ∀ {β : Type} (b : β), φ (pure b) = pure b)
    (map_bind : ∀ {β γ : Type} (x : m β) (f : β → m γ), φ (x >>= f) = φ x >>= fun b => φ (f b))
    {β γ : Type} (g : β → γ) (x : m β) : φ (g <$> x) = g <$> φ x := by
  rw [← bind_pure_comp, ← bind_pure_comp, map_bind]
  simp only [map_pure]

/-! ## Computing a function in order -/

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

section InOrder

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- A vector computed in order is the function computed in order, each result mapped. -/
theorem ofFnInOrder_eq_sequenceFin {α β : Type} :
    ∀ (n : Nat) (c : Fin n → m α) (g : α → β),
      ofFnInOrder n (fun i => g <$> c i)
        = (fun f => Vector.ofFn fun i => g (f i)) <$> sequenceFin c
  | 0, c, g => by
    simp only [ofFnInOrder_zero, sequenceFin, map_pure]
    congr 1
  | n + 1, c, g => by
    simp only [ofFnInOrder_succ, sequenceFin, map_bind, bind_map_left, map_pure]
    refine bind_congr fun head => ?_
    rw [ofFnInOrder_eq_sequenceFin n (fun i => c i.succ) g]
    simp only [bind_map_left]
    refine bind_congr fun tail => ?_
    congr 1
    apply Vector.ext
    intro i hi
    -- Entry 0 is the head, entry `i + 1` is entry `i` of the tail.
    cases i with
    | zero => simp
    | succ i => simp

/-- A vector computed in order is the function computed in order, over equal lengths. -/
theorem ofFnInOrder_eq_sequenceFin_cast {α β : Type} {n n' : Nat} (h : n = n')
    (c : Fin n' → m α) (g : α → β) :
    ofFnInOrder n (fun i => g <$> c (Fin.cast h i))
      = (fun f => Vector.ofFn fun i => g (f (Fin.cast h i))) <$> sequenceFin c := by
  subst h
  exact ofFnInOrder_eq_sequenceFin n c g

/-- A vector computed in order is the function computed in order, as a vector. -/
theorem ofFnInOrder_eq_map_sequenceFin {α : Type} (n : Nat) (c : Fin n → m α) :
    ofFnInOrder n c = (fun f => Vector.ofFn f) <$> sequenceFin c := by
  have h := ofFnInOrder_eq_sequenceFin n c id
  simp only [id_map] at h
  exact h

end InOrder

end EthLib.Cryptography.HashSig
