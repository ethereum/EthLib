module

public import EthLib.Cryptography.Proofs.EvalDistEq

/-!
# Proofs: disjoint reads of a uniform vector are independent

Read a uniform vector at positions that no two reads share.

The values read then follow a product law: each read is uniform, and the reads are independent.

One result covers any family of reads of equal length.

The others cover one range, and two disjoint ranges of any lengths.
-/

@[expose] public section

open OracleComp ENNReal

/-- A bijection maps a computation with a uniform law to one with a uniform law. -/
private theorem EvalDistEq.map_uniformSample_of_bijective {α β : Type} [SampleableType α]
    [SampleableType β] {mx : ProbComp α} (h : mx =ᵈ ($ᵗ α)) {f : α → β}
    (hf : Function.Bijective f) : (f <$> mx) =ᵈ ($ᵗ β) :=
  (h.map f).trans (SampleableType.map_uniformSample_evalDistEq_of_bijective hf)

/-- Reads of a uniform vector at pairwise distinct positions form a uniform table.

Each read is one row, and read `a` takes position `p a j` for its `j`-th value.

A uniform table is a product of independent uniform rows. -/
theorem evalDistEq_uniformSample_vector_map_disjoint_reads {R ι : Type} {m k : Nat}
    [Finite ι] [Finite R] [Nonempty R] [SampleableType (Vector R m)]
    [SampleableType (ι → Fin k → R)] {p : ι → Fin k → Fin m}
    (disjoint : Function.Injective fun position : ι × Fin k => p position.1 position.2) :
    ((fun v : Vector R m => fun a j => v[(p a j).val]) <$> ($ᵗ (Vector R m))) =ᵈ
      ($ᵗ (ι → Fin k → R)) := by
  let : SampleableType (ι × Fin k → R) := SampleableType.ofEquiv (Equiv.curry ι (Fin k) R).symm
  have h := EvalDistEq.map_uniformSample_of_bijective
    (evalDistEq_uniformSample_vector_map_getElem_injective
      (e := fun q : ι × Fin k => p q.1 q.2) disjoint) (Equiv.curry ι (Fin k) R).bijective
  rw [Functor.map_map] at h
  exact h

/-- The range of `k` values from position `a` of a uniform vector of length `m` is uniform.

It needs `a + k ≤ m`. -/
theorem evalDistEq_uniformSample_vector_range {R : Type} [Finite R] [Nonempty R]
    [SampleableType R] {m : Nat} (a k : Nat) (inside : a + k ≤ m) :
    ((fun v : Vector R m => Vector.ofFn fun j : Fin k => v[a + j.val]) <$>
      ($ᵗ (Vector R m))) =ᵈ ($ᵗ (Vector R k)) := by
  have h := EvalDistEq.map_uniformSample_of_bijective
    (evalDistEq_uniformSample_vector_map_getElem_injective
      (e := fun j : Fin k => (⟨a + j.val, by omega⟩ : Fin m))
      fun x y hxy => Fin.ext (by simpa using hxy)) (arrayVectorEquivFin R k).symm.bijective
  rw [Functor.map_map] at h
  exact h

/-- Two disjoint ranges of a uniform vector are independent uniform vectors.

The first range has `k` values from position `a`, the second `l` values from position `b`.

Both lie inside the vector, and neither meets the other. -/
theorem evalDistEq_uniformSample_vector_two_ranges {R : Type} [Finite R] [Nonempty R]
    [SampleableType R] {m : Nat} (a k b l : Nat) (first : a + k ≤ m) (second : b + l ≤ m)
    (apart : a + k ≤ b ∨ b + l ≤ a) :
    ((fun v : Vector R m => (Vector.ofFn fun j : Fin k => v[a + j.val],
        Vector.ofFn fun j : Fin l => v[b + j.val])) <$> ($ᵗ (Vector R m))) =ᵈ
      (do
        let x ← $ᵗ (Vector R k)
        let y ← $ᵗ (Vector R l)
        pure (x, y)) := by
  let split := Equiv.sumArrowEquivProdArrow (Fin k) (Fin l) R
  let : SampleableType (Fin k ⊕ Fin l → R) := SampleableType.ofEquiv split.symm
  have h := EvalDistEq.map_uniformSample_of_bijective
    (evalDistEq_uniformSample_vector_map_getElem_injective
      (e := Sum.elim (fun j : Fin k => (⟨a + j.val, by omega⟩ : Fin m))
        fun j : Fin l => (⟨b + j.val, by omega⟩ : Fin m))
      (by rintro (x | x) (y | y) hxy <;> simp [Fin.ext_iff] at hxy ⊢ <;> omega))
    (split.trans
      ((arrayVectorEquivFin R k).symm.prodCongr (arrayVectorEquivFin R l).symm)).bijective
  rw [Functor.map_map, SampleableType.uniformSample_prod_eq_bind] at h
  exact h

/-- An event on one range and an event on a disjoint range have the product chance.

The first range has `k` values from position `a`, the second `l` values from position `b`.

Both lie inside the vector, and neither meets the other.

Each factor is the chance of its event on a uniform vector of the range's length. -/
theorem prEvent_uniformSample_vector_two_ranges {R : Type} [Finite R] [Nonempty R]
    [SampleableType R] {m : Nat} (a k b l : Nat) (first : a + k ≤ m) (second : b + l ≤ m)
    (apart : a + k ≤ b ∨ b + l ≤ a) (P : Vector R k → Prop) (Q : Vector R l → Prop) :
    Pr{let v ← $ᵗ (Vector R m)}[P (Vector.ofFn fun j : Fin k => v[a + j.val]) ∧
        Q (Vector.ofFn fun j : Fin l => v[b + j.val])] =
      Pr{let x ← $ᵗ (Vector R k)}[P x] * Pr{let y ← $ᵗ (Vector R l)}[Q y] := by
  rw [← prEvent_bind_bind_and, ← prEvent_map (p := fun z => P z.1 ∧ Q z.2)
      (f := fun v : Vector R m => (Vector.ofFn fun j : Fin k => v[a + j.val],
        Vector.ofFn fun j : Fin l => v[b + j.val])),
    (evalDistEq_uniformSample_vector_two_ranges a k b l first second apart).prEvent_eq]
  simp only [prEvent_norm]
