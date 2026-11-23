module

public import EthLib.Base.Json.Document
public import EthLib.Base.Proofs.Json
public import EthLib.Base.Proofs.Json.Escape
public import EthLib.Base.Proofs.Json.Number
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.TreeMap.Raw.WF

/-!
# Proofs: a printed document reads back

The printer writes a text that the reader reads back, for a document whose objects repeat no name.

The reader rebuilds each object from its members, in increasing order of names.

So the document read back holds the same names and values, though a tree may differ in shape.

A name looked up in a rebuilt object gives the rebuilt value that the object held under it.
-/

@[expose] public section

namespace EthLib.Base.Json

open Lean

/-- No object of a document repeats a name, at any depth. -/
inductive Distinct : Lean.Json → Prop
  | null : Distinct .null
  | bool (b : Bool) : Distinct (.bool b)
  | num (number : JsonNumber) : Distinct (.num number)
  | str (text : String) : Distinct (.str text)
  | arr {items : Array Lean.Json} (each : ∀ item ∈ items, Distinct item) : Distinct (.arr items)
  | obj {members : Std.TreeMap.Raw String Lean.Json} (names : members.keys.Nodup)
      (each : ∀ name item, (name, item) ∈ members.toList → Distinct item) :
      Distinct (.obj members)

mutual

/-- The document that the reader builds from the text of a document whose objects repeat no name.

Each object is rebuilt from its members, in increasing order of names. -/
def canonical (document : Lean.Json) : Lean.Json :=
  match document with
  | .arr ⟨items⟩ => .arr ⟨canonicalItems items⟩
  | .obj ⟨⟨members⟩⟩ => .obj (canonicalMembers members ∅)
  | document => document
termination_by structural document

/-- The rebuilt items of an array. -/
def canonicalItems (items : List Lean.Json) : List Lean.Json :=
  match items with
  | [] => []
  | item :: rest => canonical item :: canonicalItems rest
termination_by structural items

/-- The rebuilt members of an object, inserted in increasing order of names after the others. -/
def canonicalMembers (members : Std.DTreeMap.Internal.Impl String fun _ => Lean.Json)
    (acc : Std.TreeMap.Raw String Lean.Json) : Std.TreeMap.Raw String Lean.Json :=
  match members with
  | .leaf => acc
  | .inner _ name item left right =>
    canonicalMembers right ((canonicalMembers left acc).insert name (canonical item))
termination_by structural members

end

/-! ## The members of an object in order -/

/-- The members of a tree, in order. -/
private def inorder : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) →
    List (String × Lean.Json)
  | .leaf => []
  | .inner _ name item left right => inorder left ++ (name, item) :: inorder right

private theorem inorder_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    inorder t = t.toListModel.map fun e => (e.1, e.2) := by
  induction t with
  | leaf => rfl
  | inner _ k v l r ihl ihr => simp [inorder, ihl, ihr]

private theorem toList_mk (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json).toList = inorder t := by
  rw [inorder_eq, ← Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map]
  rfl

private theorem keys_mk (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json).keys = (inorder t).map Prod.fst := by
  rw [← toList_mk, Std.TreeMap.Raw.map_fst_toList_eq_keys]

/-- Induction over documents, with a hypothesis for each item and each member. -/
private theorem induct (P : Lean.Json → Prop) (null : P .null) (bool : ∀ b, P (.bool b))
    (num : ∀ n, P (.num n)) (str : ∀ s, P (.str s))
    (arr : ∀ items : List Lean.Json, (∀ x ∈ items, P x) → P (.arr ⟨items⟩))
    (obj : ∀ t, (∀ p ∈ inorder t, P p.2) → P (.obj ⟨⟨t⟩⟩)) (j : Lean.Json) : P j :=
  go j
where
  go (j : Lean.Json) : P j := match j with
    | .null => null
    | .bool b => bool b
    | .num n => num n
    | .str s => str s
    | .arr ⟨items⟩ => arr items (goItems items)
    | .obj ⟨⟨t⟩⟩ => obj t (goMembers t)
  termination_by structural j
  goItems (items : List Lean.Json) : ∀ x ∈ items, P x := match items with
    | [] => by simp
    | x :: xs => List.forall_mem_cons.2 ⟨go x, goItems xs⟩
  termination_by structural items
  goMembers (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
      ∀ p ∈ inorder t, P p.2 := match t with
    | .leaf => by simp [inorder]
    | .inner _ k v l r => by
      have hl := goMembers l
      have hv := go v
      have hr := goMembers r
      simp only [inorder, List.mem_append, List.mem_cons]
      rintro p (hp | rfl | hp)
      · exact hl p hp
      · exact hv
      · exact hr p hp
  termination_by structural t

/-! ## Inserting members in order -/

/-- The members of a list inserted in order, each value mapped first. -/
private def insertAll (g : Lean.Json → Lean.Json) (l : List (String × Lean.Json))
    (acc : Std.TreeMap.Raw String Lean.Json) : Std.TreeMap.Raw String Lean.Json :=
  l.foldl (fun a p => a.insert p.1 (g p.2)) acc

private theorem insertAll_wf (g : Lean.Json → Lean.Json) :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      (insertAll g l acc).WF
  | [], _, h => h
  | _ :: r, _, h => insertAll_wf g r _ h.insert

private theorem getElem?_insertAll_of_not_mem (g : Lean.Json → Lean.Json) {name : String} :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      name ∉ l.map Prod.fst → (insertAll g l acc)[name]? = acc[name]?
  | [], _, _, _ => rfl
  | (k, v) :: r, acc, h, hn => by
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    simp only [insertAll, List.foldl_cons]
    rw [← insertAll, getElem?_insertAll_of_not_mem g r _ h.insert hn.2,
      Std.TreeMap.Raw.getElem?_insert h]
    have : ¬ compare k name = .eq := fun e => hn.1 (Std.LawfulEqOrd.compare_eq_iff_eq.mp e).symm
    simp [this]

private theorem getElem?_insertAll_of_mem (g : Lean.Json → Lean.Json) {name : String}
    {v : Lean.Json} :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      (l.map Prod.fst).Nodup → (name, v) ∈ l → (insertAll g l acc)[name]? = some (g v)
  | [], _, _, _, hm => by simp at hm
  | (k, w) :: r, acc, h, hd, hm => by
    simp only [List.map_cons, List.nodup_cons] at hd
    simp only [insertAll, List.foldl_cons]
    rw [← insertAll]
    rcases List.mem_cons.mp hm with e | hm
    · cases e
      rw [getElem?_insertAll_of_not_mem g r _ h.insert hd.1,
        Std.TreeMap.Raw.getElem?_insert h]
      simp
    · exact getElem?_insertAll_of_mem g r _ h.insert hd.2 hm

/-- A string is its own rebuilt document. -/
@[simp] theorem canonical_str (text : String) : canonical (.str text) = .str text := by
  simp [canonical]

/-- The rebuilt items are the items rebuilt one by one. -/
private theorem canonicalItems_eq (items : List Lean.Json) :
    canonicalItems items = items.map canonical := by
  induction items with
  | nil => simp [canonicalItems]
  | cons x xs ih => simp [canonicalItems, ih]

/-- The rebuilt array holds the rebuilt items. -/
@[simp] theorem canonical_arr (items : Array Lean.Json) :
    canonical (.arr items) = .arr (items.map canonical) := by
  obtain ⟨items⟩ := items
  simp [canonical, canonicalItems_eq]

/-- The rebuilt members are inserted in order, each with its rebuilt value. -/
private theorem canonicalMembers_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json))
    (acc : Std.TreeMap.Raw String Lean.Json) :
    canonicalMembers t acc = (inorder t).foldl (fun a p => a.insert p.1 (canonical p.2)) acc := by
  induction t generalizing acc with
  | leaf => simp [canonicalMembers, inorder]
  | inner _ k v l r ihl ihr => simp [canonicalMembers, inorder, ihl, ihr]

/-! ## The text of a document -/

/-- The text of one character of a string. -/
private def esc (c : Char) : List Char := (escape "" c).toList

private theorem escape_toList (acc : String) (c : Char) :
    (escape acc c).toList = acc.toList ++ esc c := by
  unfold esc escape
  repeat' split
  all_goals simp_all [String.toList_append, String.toList_push]

private theorem foldl_escape_toList :
    ∀ (cs : List Char) (acc : String), (cs.foldl escape acc).toList = acc.toList ++ cs.flatMap esc
  | [], _ => by simp
  | c :: cs, acc => by simp [foldl_escape_toList cs, escape_toList]

private theorem writeString_toList (s acc : String) :
    (writeString s acc).toList = acc.toList ++ '"' :: (s.toList.flatMap esc ++ ['"']) := by
  simp [writeString, foldl_escape_toList, String.toList_push]

/-- The text of a number. -/
private def numText (n : JsonNumber) : List Char :=
  n.mantissa.repr.toList ++ if n.exponent = 0 then [] else 'e' :: '-' :: n.exponent.repr.toList

private theorem writeNumber_toList (n : JsonNumber) (acc : String) :
    (writeNumber n acc).toList = acc.toList ++ numText n := by
  unfold writeNumber numText
  split <;> simp_all [String.toList_append]

/-- The members of a list as the text writes them, each after a comma but the first. -/
private def wm : List (String × Lean.Json) → String → Bool → String
  | [], acc, _ => acc
  | (k, v) :: r, acc, first =>
    wm r (write v ((writeString k (if first then acc else acc.push ',')).push ':')) false

private theorem wm_append :
    ∀ (l₁ l₂ : List (String × Lean.Json)) (acc : String) (first : Bool),
      wm (l₁ ++ l₂) acc first = wm l₂ (wm l₁ acc first) (first && l₁.isEmpty)
  | [], _, _, _ => by simp [wm]
  | (k, v) :: r, l₂, acc, first => by simp [wm, wm_append r]

private theorem writeMembers_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    ∀ (acc : String) (first : Bool),
      writeMembers t acc first = (wm (inorder t) acc first, first && (inorder t).isEmpty) := by
  induction t with
  | leaf => intro acc first; simp [writeMembers, inorder, wm]
  | inner _ k v l r ihl ihr =>
    intro acc first
    rw [writeMembers, ihl]
    simp only [inorder, ihr, wm_append, wm]
    simp

/-- A document whose text after other text is that text, then its own. -/
private def Appends (j : Lean.Json) : Prop :=
  ∀ acc : String, (write j acc).toList = acc.toList ++ (write j "").toList

private theorem writeItems_toList :
    ∀ (l : List Lean.Json), (∀ x ∈ l, Appends x) → ∀ (acc : String) (first : Bool),
      (writeItems l acc first).toList = acc.toList ++ (writeItems l "" first).toList
  | [], _, _, _ => by simp [writeItems]
  | x :: xs, h, acc, first => by
    have hx := h x (by simp)
    have hxs := writeItems_toList xs (fun y hy => h y (by simp [hy]))
    simp only [writeItems]
    rw [hxs (write x (if first then acc else acc.push ',')),
      hxs (write x (if first then "" else "".push ',')), hx (if first then acc else acc.push ','),
      hx (if first then "" else "".push ',')]
    cases first <;> simp [String.toList_push]

private theorem wm_toList :
    ∀ (l : List (String × Lean.Json)), (∀ p ∈ l, Appends p.2) → ∀ (acc : String) (first : Bool),
      (wm l acc first).toList = acc.toList ++ (wm l "" first).toList
  | [], _, _, _ => by simp [wm]
  | (k, v) :: r, h, acc, first => by
    have hv := h (k, v) (by simp)
    have hr := wm_toList r (fun p hp => h p (by simp [hp]))
    simp only [wm]
    rw [hr, hr (write v _), hv, hv ((writeString k _).push ':')]
    cases first <;> simp [String.toList_push, writeString_toList]

/-- The text of a document after other text is that text, then its own. -/
private theorem write_toList (j : Lean.Json) :
    ∀ acc : String, (write j acc).toList = acc.toList ++ (write j "").toList := by
  refine induct Appends ?_ ?_ ?_ ?_ ?_ ?_ j
  · intro acc; simp [write, String.toList_append]
  · intro b acc; cases b <;> simp [write, String.toList_append]
  · intro n acc; simp [write, writeNumber_toList]
  · intro s acc; simp [write, writeString_toList]
  · intro items h acc
    simp [write, String.toList_push, writeItems_toList items h (acc.push '['),
      writeItems_toList items h "["]
  · intro t h acc
    simp [write, writeMembers_eq, String.toList_push, wm_toList (inorder t) h (acc.push '{'),
      wm_toList (inorder t) h "{"]

/-- The text of a document, as characters. -/
private def text (j : Lean.Json) : List Char := (write j "").toList

private theorem text_arr (items : List Lean.Json) :
    text (.arr ⟨items⟩) = '[' :: ((writeItems items "" true).toList ++ [']']) := by
  simp [text, write, String.toList_push, writeItems_toList items (fun x _ => write_toList x) "["]

private theorem writeItems_cons_true (x : Lean.Json) (xs : List Lean.Json) :
    (writeItems (x :: xs) "" true).toList = text x ++ (writeItems xs "" false).toList := by
  simp [writeItems, text, writeItems_toList xs (fun x _ => write_toList x) (write x "")]

private theorem writeItems_cons_false (x : Lean.Json) (xs : List Lean.Json) :
    (writeItems (x :: xs) "" false).toList =
      ',' :: (text x ++ (writeItems xs "" false).toList) := by
  simp [writeItems, text, writeItems_toList xs (fun x _ => write_toList x) (write x _),
    write_toList x ","]

private theorem text_obj (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    text (.obj ⟨⟨t⟩⟩) = '{' :: ((wm (inorder t) "" true).toList ++ ['}']) := by
  simp [text, write, writeMembers_eq, String.toList_push,
    wm_toList (inorder t) (fun p _ => write_toList p.2) "{"]

private theorem wm_cons (k : String) (v : Lean.Json) (r : List (String × Lean.Json))
    (first : Bool) :
    (wm ((k, v) :: r) "" first).toList = (if first then [] else [',']) ++
      '"' :: (k.toList.flatMap esc ++ '"' :: ':' :: (text v ++ (wm r "" false).toList)) := by
  simp only [wm]
  rw [wm_toList r (fun p _ => write_toList p.2), write_toList v]
  cases first <;> simp [writeString_toList, String.toList_push, text]

/-! ## Reading a string back -/

private theorem string_step (c : Char) (Y acc : List Char) (n : Nat) :
    string (n + 1) (esc c ++ Y) acc = string n Y (c :: acc) := by
  unfold esc escape
  by_cases h1 : c = '"'
  · subst h1; simp [string]
  by_cases h2 : c = '\\'
  · subst h2; simp [string]
  by_cases h3 : c = '\n'
  · subst h3; simp [string]
  by_cases h4 : c = '\r'
  · subst h4; simp [string]
  by_cases h5 : c.toNat < 0x20
  · simp only [h1, h2, h3, h4, h5, ite_false, dite_true]
    have ha := hexValue?_hexDigitChar ⟨c.toNat / 16, by omega⟩
    have hb := hexValue?_hexDigitChar ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩
    have hx : hex4 ('0' :: '0' :: hexDigitChar ⟨c.toNat / 16, by omega⟩ ::
        hexDigitChar ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩ :: Y) = some (c.toNat, Y) := by
      refine hex4_cons_eq_some_iff.mpr ⟨rfl, 0, 0, _, _, by decide, by decide, ha, hb, ?_⟩
      have : (0 : UInt8).toNat = 0 := rfl
      simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
      omega
    have hu := (unicodeEscape_eq_of_not_surrogate hx (Or.inl (by omega))).1
    rw [Char.ofNat_toNat] at hu
    simp only [String.toList_push, String.toList_append, List.append_assoc]
    simp [string, hu]
  · simp only [h1, h2, h3, h4, h5, ite_false, dite_false, String.toList_push]
    rw [String.toList_empty, List.nil_append, List.singleton_append, string.eq_def]
    split <;> simp_all
    intro h
    omega

private theorem string_esc : ∀ (cs X acc : List Char) (fuel : Nat), cs.length < fuel →
    string fuel (cs.flatMap esc ++ '"' :: X) acc = some (String.ofList (acc.reverse ++ cs), X)
  | [], X, acc, fuel + 1, _ => by simp [string]
  | c :: cs, X, acc, fuel + 1, h => by
    have ih := string_esc cs X (c :: acc) fuel (by simp at h; omega)
    simp only [List.flatMap_cons, List.append_assoc]
    rw [show acc.reverse ++ c :: cs = (c :: acc).reverse ++ cs by simp, ← ih]
    exact string_step c _ acc fuel

/-! ## Reading a number back -/

/-- What may follow the text of a document inside the text of another. -/
private def Good (rest : List Char) : Prop := ∀ c ∈ rest.head?, c = ',' ∨ c = ']' ∨ c = '}'

private theorem good_digit {rest : List Char} (hr : Good rest) :
    ∀ c ∈ rest.head?, digit c = false ∧ c ≠ '.' ∧ c ≠ 'e' ∧ c ≠ 'E' := by
  intro c hc
  rcases hr c hc with rfl | rfl | rfl <;> decide

/-- The digits of a number, with or without a minus sign, then an exponent or none. -/
private theorem number_digits (neg : Bool) (a : Nat) (hpos : neg = true → 0 < a)
    (X rest : List Char) (expo : Int) (hr : Good rest)
    (hX : (X = rest ∧ expo = 0) ∨
      ∃ b, 0 < b ∧ X = 'e' :: '-' :: (Nat.toDigits 10 b ++ rest) ∧ expo = -(b : Int)) :
    number ((if neg then ['-'] else []) ++ Nat.toDigits 10 a ++ X) =
      some (⟨if neg then -(a : Int) else a, expo⟩, rest) := by
  have hg := good_digit hr
  have hXh : ∀ c ∈ X.head?, digit c = false ∧ c ≠ '.' := by
    rcases hX with ⟨rfl, -⟩ | ⟨b, -, rfl, -⟩
    · exact fun c hc => ⟨(hg c hc).1, (hg c hc).2.1⟩
    · intro c hc
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc
      subst hc
      decide
  have hspan := span_toDigits a X (fun c hc => (hXh c hc).1)
  have hval := digitsValue_toDigits a
  obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 a = d :: ds :=
    List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
  have hdig := digit_of_mem_toDigits (c := d) (n := a) (by simp [hd])
  have hminus : d ≠ '-' := by rintro rfl; revert hdig; decide
  have hlead : ¬ ((d :: ds).head? = some '0' ∧ (d :: ds).length > 1) := by
    rintro ⟨h0, hl⟩
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [Nat.toDigits_zero, List.cons.injEq] at hd
      simp [← hd.2] at hl
    · exact head_toDigits_ne_zero a ha (hd ▸ h0)
  rw [hd] at hspan hval
  rw [hd]
  unfold number
  split
  rename_i minus rest' heq
  have : (minus, rest') = (neg, d :: ds ++ X) := by
    rw [← heq]
    cases neg <;> split <;> simp_all
  simp only [Prod.mk.injEq] at this
  obtain ⟨rfl, rfl⟩ := this
  simp only [hspan]
  split
  · simp_all
  split
  · exact absurd rfl (hXh '.' (by simp)).2
  · simp only [bind, Option.bind, pure, hval, List.append_nil, List.length_nil]
    rcases hX with ⟨h1, rfl⟩ | ⟨b, hb, rfl, rfl⟩
    · rw [h1]
      rcases rest with _ | ⟨c, tl⟩
      · simp
      · rcases hr c rfl with rfl | rfl | rfl <;> simp
    · have hspan' := span_toDigits b rest (fun c hc => (hg c hc).1)
      obtain ⟨d', ds', hd'⟩ : ∃ d ds, Nat.toDigits 10 b = d :: ds :=
        List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
      have hval' := digitsValue_toDigits b
      rw [hd', List.cons_append] at hspan'
      rw [hd'] at hval'
      simp [hd', hspan', hval']
private theorem number_numText (n : JsonNumber) (rest : List Char) (hr : Good rest) :
    number (numText n ++ rest) = some (⟨n.mantissa, -(n.exponent : Int)⟩, rest) := by
  obtain ⟨m, e⟩ := n
  have hX : (((if e = 0 then [] else 'e' :: '-' :: Nat.toDigits 10 e) ++ rest) = rest ∧
      -(e : Int) = 0) ∨ ∃ b, 0 < b ∧
        ((if e = 0 then [] else 'e' :: '-' :: Nat.toDigits 10 e) ++ rest) =
          'e' :: '-' :: (Nat.toDigits 10 b ++ rest) ∧ -(e : Int) = -(b : Int) := by
    by_cases he : e = 0
    · left; simp [he]
    · right; exact ⟨e, by omega, by simp [he], rfl⟩
  simp only [numText, List.append_assoc, Nat.toList_repr]
  rw [Int.repr_eq_ite]
  by_cases hm : 0 ≤ m
  · have := number_digits false m.toNat (by simp) _ rest _ hr hX
    simp only [Bool.false_eq_true, ite_false, List.nil_append] at this
    simp only [hm, ite_true, Nat.toList_repr]
    rw [this]
    congr
    omega
  · have := number_digits true (-m).toNat (fun _ => by omega) _ rest _ hr hX
    simp only [ite_true, List.cons_append, List.nil_append] at this
    simp only [hm, ite_false, String.toList_append, Nat.toList_repr, List.append_assoc]
    rw [show "-".toList = ['-'] from rfl, List.singleton_append, this]
    congr
    omega

/-! ## Reading a document back -/

mutual

/-- The value that the reader builds from the text of a document. -/
private def toValue (j : Lean.Json) : Value :=
  match j with
  | .null => .null
  | .bool b => .bool b
  | .num n => .num ⟨n.mantissa, -(n.exponent : Int)⟩
  | .str s => .str s
  | .arr ⟨items⟩ => .arr (toValueItems items)
  | .obj ⟨⟨t⟩⟩ => .obj (toValueMembers t)
termination_by structural j

/-- The values of the items of an array. -/
private def toValueItems (items : List Lean.Json) : List Value :=
  match items with
  | [] => []
  | x :: xs => toValue x :: toValueItems xs
termination_by structural items

/-- The members of an object as values, in order. -/
private def toValueMembers (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    List (String × Value) :=
  match t with
  | .leaf => []
  | .inner _ k v l r => toValueMembers l ++ (k, toValue v) :: toValueMembers r
termination_by structural t

end

private theorem toValueItems_eq (items : List Lean.Json) :
    toValueItems items = items.map toValue := by
  induction items with
  | nil => simp [toValueItems]
  | cons x xs ih => simp [toValueItems, ih]

private theorem toValueMembers_eq (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    toValueMembers t = (inorder t).map fun p => (p.1, toValue p.2) := by
  induction t with
  | leaf => simp [toValueMembers, inorder]
  | inner _ k v l r ihl ihr => simp [toValueMembers, inorder, ihl, ihr]

private theorem text_head (j : Lean.Json) :
    ∃ c tl, text j = c :: tl ∧ whitespace c = false ∧ c ≠ ']' := by
  match j with
  | .null => exact ⟨'n', _, rfl, by decide, by decide⟩
  | .bool true => exact ⟨'t', _, rfl, by decide, by decide⟩
  | .bool false => exact ⟨'f', _, rfl, by decide, by decide⟩
  | .str s =>
    exact ⟨'"', s.toList.flatMap esc ++ ['"'], by simp [text, write, writeString_toList],
      by decide, by decide⟩
  | .arr ⟨items⟩ => exact ⟨'[', _, text_arr items, by decide, by decide⟩
  | .obj ⟨⟨t⟩⟩ => exact ⟨'{', _, text_obj t, by decide, by decide⟩
  | .num ⟨m, e⟩ =>
    simp only [text, write, writeNumber_toList, numText, String.toList_empty, List.nil_append]
    rw [Int.repr_eq_ite]
    by_cases hm : 0 ≤ m
    · simp only [hm, ite_true, Nat.toList_repr]
      obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 m.toNat = d :: ds :=
        List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
      have hdig := digit_of_mem_toDigits (c := d) (n := m.toNat) (by simp [hd])
      refine ⟨d, _, by rw [hd, List.cons_append], ?_, ?_⟩
      · simp only [digit, Bool.and_eq_true, decide_eq_true_eq] at hdig
        simp only [whitespace, Bool.or_eq_false_iff, decide_eq_false_iff_not]
        refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> rintro rfl <;> revert hdig <;> decide
      · rintro rfl; revert hdig; decide
    · simp only [hm, ite_false, String.toList_append]
      exact ⟨'-', _, rfl, by decide, by decide⟩

private theorem dropWhile_text (j : Lean.Json) (X : List Char) :
    (text j ++ X).dropWhile whitespace = text j ++ X := by
  obtain ⟨c, tl, hc, hws, -⟩ := text_head j
  rw [hc, List.cons_append, List.dropWhile_cons_of_neg (by simp [hws])]

/-- The reader reads the text of a document followed by what may follow it. -/
private def Reads (j : Lean.Json) : Prop :=
  ∀ (f : Nat) (rest : List Char), 2 * (text j).length < f → Good rest →
    value f (text j ++ rest) = some (toValue j, rest)

private theorem array_read :
    ∀ (xs : List Lean.Json) (x : Lean.Json) (acc : List Value) (empty : Bool) (f : Nat)
      (rest : List Char), (∀ y ∈ x :: xs, Reads y) → Good rest →
      2 * (text x ++ (writeItems xs "" false).toList).length + 2 < f →
      array f (text x ++ ((writeItems xs "" false).toList ++ ']' :: rest)) acc empty =
        some (acc.reverse ++ (x :: xs).map toValue, rest) := by
  intro xs
  induction xs with
  | nil =>
    intro x acc empty f rest h hr hf
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    obtain ⟨c, tl, hc, -, hbr⟩ := text_head x
    have hv := h x (by simp) n (']' :: rest) (by simp at hf; omega) (by simp [Good])
    simp only [writeItems, String.toList_empty, List.nil_append] at hv ⊢
    rw [array]
    · rw [hv]
      simp [whitespace]
    · intro r e
      rw [hc] at e
      exact hbr (List.cons.inj e).1
  | cons y ys ih =>
    intro x acc empty f rest h hr hf
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    obtain ⟨c, tl, hc, -, hbr⟩ := text_head x
    rw [writeItems_cons_false] at hf ⊢
    simp only [List.length_append, List.length_cons] at hf
    have hv := h x (by simp) n
      (',' :: (text y ++ ((writeItems ys "" false).toList ++ ']' :: rest)))
      (by omega) (by simp [Good])
    have hi := ih y (toValue x :: acc) false n rest (fun z hz => h z (by simp_all)) hr
      (by simp only [List.length_append]; omega)
    simp only [List.cons_append, List.append_assoc] at hv ⊢
    rw [array]
    · rw [hv]
      simp only [bind, Option.bind]
      rw [List.dropWhile_cons_of_neg (by decide)]
      simp only
      rw [dropWhile_text, hi]
      simp
    · intro r e
      rw [hc] at e
      exact hbr (List.cons.inj e).1

private theorem length_esc (c : Char) : 1 ≤ (esc c).length := by
  unfold esc escape
  repeat' split
  all_goals simp [String.toList_push]

private theorem length_flatMap_esc : ∀ cs : List Char, cs.length ≤ (cs.flatMap esc).length
  | [] => by simp
  | c :: cs => by
    have := length_esc c
    have := length_flatMap_esc cs
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem object_read :
    ∀ (r : List (String × Lean.Json)) (k : String) (v : Lean.Json)
      (acc : List (String × Value)) (empty : Bool) (f : Nat) (rest : List Char),
      (∀ p ∈ (k, v) :: r, Reads p.2) → Good rest →
      2 * (wm ((k, v) :: r) "" true).toList.length + 2 < f →
      object f ((wm ((k, v) :: r) "" true).toList ++ '}' :: rest) acc empty =
        some (acc.reverse ++ ((k, v) :: r).map (fun p => (p.1, toValue p.2)), rest) := by
  intro r
  induction r with
  | nil =>
    intro k v acc empty f rest h hr hf
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have hk := length_flatMap_esc k.toList
    rw [wm_cons] at hf ⊢
    simp only [wm, String.toList_empty, List.append_nil, ite_true, List.nil_append,
      List.length_cons, List.length_append] at hf ⊢
    have hR : Reads v := h (k, v) (by simp)
    have hv := hR n ('}' :: rest) (by omega) (by simp [Good])
    have hs := string_esc k.toList (':' :: (text v ++ '}' :: rest)) [] n (by omega)
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hs
    simp only [List.cons_append, List.append_assoc]
    rw [object]
    simp only [hs, bind, Option.bind]
    rw [List.dropWhile_cons_of_neg (by decide)]
    simp only [hv]
    rw [List.dropWhile_cons_of_neg (by decide)]
    simp
  | cons p r ih =>
    intro k v acc empty f rest h hr hf
    obtain ⟨k', v'⟩ := p
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have hk := length_flatMap_esc k.toList
    have hM : (wm ((k', v') :: r) "" false).toList =
        ',' :: (wm ((k', v') :: r) "" true).toList := by
      rw [wm_cons, wm_cons]
      simp
    obtain ⟨M, hM'⟩ : ∃ M, (wm ((k', v') :: r) "" true).toList = '"' :: M :=
      ⟨_, wm_cons k' v' r true⟩
    have hi := ih k' v' ((k, toValue v) :: acc) false n rest (fun q hq => h q (by simp_all)) hr
      (by rw [wm_cons k v, hM] at hf; simp only [List.length_append, List.length_cons] at hf ⊢
          simp at hf; omega)
    rw [wm_cons k v, hM] at hf ⊢
    simp only [ite_true, List.nil_append, List.length_cons, List.length_append] at hf ⊢
    have hR : Reads v := h (k, v) (by simp)
    have hv := hR n (',' :: ((wm ((k', v') :: r) "" true).toList ++ '}' :: rest)) (by omega)
      (by simp [Good])
    have hs := string_esc k.toList (':' :: (text v ++ ',' ::
      ((wm ((k', v') :: r) "" true).toList ++ '}' :: rest))) [] n (by omega)
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hs
    simp only [List.cons_append, List.append_assoc]
    rw [object]
    simp only [hs, bind, Option.bind]
    rw [List.dropWhile_cons_of_neg (by decide)]
    simp only [hv]
    rw [List.dropWhile_cons_of_neg (by decide)]
    simp only
    rw [hM', List.cons_append, List.dropWhile_cons_of_neg (by decide), ← List.cons_append, ← hM',
      hi]
    simp

private theorem numText_head (n : JsonNumber) :
    ∃ c tl, numText n = c :: tl ∧ (c = '-' ∨ digit c = true) := by
  obtain ⟨m, e⟩ := n
  simp only [numText]
  rw [Int.repr_eq_ite]
  by_cases hm : 0 ≤ m
  · simp only [hm, ite_true, Nat.toList_repr]
    obtain ⟨d, ds, hd⟩ : ∃ d ds, Nat.toDigits 10 m.toNat = d :: ds :=
      List.exists_cons_of_ne_nil Nat.toDigits_ne_nil
    exact ⟨d, _, by rw [hd, List.cons_append],
      Or.inr (digit_of_mem_toDigits (c := d) (n := m.toNat) (by simp [hd]))⟩
  · simp only [hm, ite_false, String.toList_append]
    exact ⟨'-', _, rfl, Or.inl rfl⟩

/-- The reader reads back the text of every document. -/
private theorem reads (j : Lean.Json) : Reads j := by
  refine induct Reads ?_ ?_ ?_ ?_ ?_ ?_ j
  · intro f rest hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    simp [text, write, value, whitespace, toValue]
  · intro b f rest hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    cases b <;> simp [text, write, value, whitespace, toValue]
  · intro num f rest hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    obtain ⟨c, tl, hc, hcd⟩ := numText_head num
    have hnum := number_numText num rest hr
    have ht : text (.num num) = numText num := by simp [text, write, writeNumber_toList]
    rw [value, dropWhile_text, ht, hc]
    rw [hc] at hnum
    split <;> simp_all [digit, toValue]
  · intro s f rest hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    have hk := length_flatMap_esc s.toList
    simp only [text, write, writeString_toList, String.toList_empty, List.nil_append,
      List.length_cons, List.length_append] at hf
    have hs := string_esc s.toList rest [] n (by omega)
    simp only [List.reverse_nil, List.nil_append, String.ofList_toList] at hs
    simp only [text, write, writeString_toList, String.toList_empty, List.nil_append,
      List.cons_append, List.append_assoc]
    rw [value, List.dropWhile_cons_of_neg (by decide)]
    simp [hs, toValue]
  · intro items h f rest hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    rw [text_arr] at hf ⊢
    simp only [List.cons_append, List.append_assoc]
    rw [value, List.dropWhile_cons_of_neg (by decide)]
    simp only [toValue, toValueItems_eq]
    cases items with
    | nil =>
      simp only [writeItems, String.toList_empty, List.nil_append]
      rw [List.dropWhile_cons_of_neg (by decide)]
      cases n with
      | zero => simp at hf
      | succ n => simp [array, bind, Option.bind]
    | cons x xs =>
      rw [writeItems_cons_true] at hf ⊢
      simp only [List.length_cons, List.length_append, List.append_assoc] at hf ⊢
      rw [dropWhile_text]
      have ha := array_read xs x [] true n rest h hr
        (by simp only [List.length_append]; omega)
      simp only [bind, Option.bind, List.nil_append]
      rw [ha]
      simp
  · intro t h f rest hf hr
    obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
    rw [text_obj] at hf ⊢
    simp only [List.cons_append, List.append_assoc]
    rw [value, List.dropWhile_cons_of_neg (by decide)]
    simp only [toValue, toValueMembers_eq]
    cases hi : inorder t with
    | nil =>
      simp only [wm, String.toList_empty, List.nil_append]
      rw [List.dropWhile_cons_of_neg (by decide)]
      cases n with
      | zero => simp [hi, wm] at hf
      | succ n => simp [object, bind, Option.bind]
    | cons p r =>
      obtain ⟨k, v⟩ := p
      rw [hi] at h hf
      obtain ⟨M, hM⟩ : ∃ M, (wm ((k, v) :: r) "" true).toList = '"' :: M :=
        ⟨_, wm_cons k v r true⟩
      have ho := object_read r k v [] true n rest h hr
        (by simp only [List.length_cons, List.length_append] at hf; omega)
      simp only [List.nil_append]
      rw [hM, List.cons_append, List.dropWhile_cons_of_neg (by decide), ← List.cons_append,
        ← hM, ho]
      simp [bind, Option.bind]

/-! ## The document of the value read back -/

/-- A document whose value read back gives its rebuilt document, when it repeats no name. -/
private def Builds (j : Lean.Json) : Prop :=
  Distinct j → (toValue j).toJson = .ok (canonical j)

private theorem itemsToJson_map :
    ∀ (l : List Lean.Json) (acc : Array Lean.Json),
      (∀ x ∈ l, (toValue x).toJson = .ok (canonical x)) →
      itemsToJson (l.map toValue) acc = .ok (acc ++ (l.map canonical).toArray)
  | [], acc, _ => by simp [itemsToJson]
  | x :: xs, acc, h => by
    have hx := h x (by simp)
    simp only [List.map_cons, itemsToJson, hx]
    show itemsToJson (xs.map toValue) (acc.push (canonical x)) = _
    rw [itemsToJson_map xs _ (fun y hy => h y (by simp [hy]))]
    simp

private theorem membersToJson_map :
    ∀ (l : List (String × Lean.Json)) (acc : Std.TreeMap.Raw String Lean.Json), acc.WF →
      (l.map Prod.fst).Nodup → (∀ p ∈ l, acc.contains p.1 = false) →
      (∀ p ∈ l, (toValue p.2).toJson = .ok (canonical p.2)) →
      membersToJson (l.map fun p => (p.1, toValue p.2)) acc = .ok (insertAll canonical l acc)
  | [], acc, _, _, _, _ => by simp [membersToJson, insertAll]
  | (k, v) :: r, acc, wf, hd, hc, h => by
    simp only [List.map_cons, List.nodup_cons] at hd
    have hv := h (k, v) (by simp)
    have hk := hc (k, v) (by simp)
    simp only at hv hk
    simp only [List.map_cons, membersToJson, hk, hv, Bool.false_eq_true, ite_false]
    show membersToJson (r.map fun p => (p.1, toValue p.2)) (acc.insert k (canonical v)) = _
    rw [membersToJson_map r _ wf.insert hd.2 ?_ (fun p hp => h p (by simp [hp]))]
    · rfl
    · intro p hp
      rw [Std.TreeMap.Raw.contains_insert wf, hc p (by simp [hp])]
      have : ¬ compare k p.1 = .eq := fun e =>
        hd.1 ((Std.LawfulEqOrd.compare_eq_iff_eq.mp e) ▸ List.mem_map.mpr ⟨p, hp, rfl⟩)
      simp [this]

private theorem builds (j : Lean.Json) : Builds j := by
  refine induct Builds ?_ ?_ ?_ ?_ ?_ ?_ j
  · intro _; simp [toValue, Value.toJson, canonical]
  · intro b _; simp [toValue, Value.toJson, canonical]
  · intro n _
    obtain ⟨m, e⟩ := n
    cases e with
    | zero => simp [toValue, Value.toJson, canonical, Number.toJsonNumber, maxExponent]
    | succ k =>
      have : -((k + 1 : Nat) : Int) = Int.negSucc k := rfl
      simp only [toValue, Value.toJson, canonical, Number.toJsonNumber, this]
  · intro s _; simp [toValue, Value.toJson, canonical]
  · intro items h hd
    cases hd with
    | arr each =>
      simp only [toValue, toValueItems_eq, Value.toJson]
      rw [itemsToJson_map items #[] (fun x hx => h x hx (each x (by simpa using hx))),
        canonical_arr]
      simp
      rfl
  · intro t h hd
    cases hd with
    | obj names each =>
      rw [keys_mk] at names
      simp only [toValue, toValueMembers_eq, Value.toJson]
      rw [membersToJson_map (inorder t) ∅ Std.TreeMap.Raw.WF.emptyc names
        (fun p _ => Std.TreeMap.Raw.contains_emptyc)
        (fun p hp => h p hp (each p.1 p.2 (by rw [toList_mk]; exact hp)))]
      simp only [canonical, canonicalMembers_eq, insertAll]
      rfl

/-- A printed document whose objects repeat no name reads back as its rebuilt document. -/
theorem ofText_toText {document : Lean.Json} (distinct : Distinct document) :
    ofText (toText document) = .ok (canonical document) := by
  have hv := reads document (2 * (text document).length + 1) [] (by omega) (by simp [Good])
  rw [List.append_nil] at hv
  have hr : read (toText document) = some (toValue document) := by
    simp only [read, toText]
    rw [show (write document "").toList = text document from rfl, hv]
    rfl
  simp only [ofText, hr]
  exact builds document distinct

/-- An object built from pairs of distinct names, each value without a repeated name. -/
theorem distinct_mkObj {pairs : List (String × Lean.Json)}
    (names : pairs.Pairwise fun a b => a.1 ≠ b.1) (each : ∀ pair ∈ pairs, Distinct pair.2) :
    Distinct (Json.mkObj pairs) := by
  rw [Toolchain.Json.mkObj_eq]
  have wf : (Std.TreeMap.Raw.ofList pairs compare).WF := Std.TreeMap.Raw.WF.ofList
  have keys : pairs.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    names.imp fun different equal => different (Std.LawfulEqOrd.compare_eq_iff_eq.mp equal)
  refine .obj (Std.TreeMap.Raw.nodup_keys wf) fun name item mem => ?_
  rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf] at mem
  by_cases h : name ∈ pairs.map Prod.fst
  · obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp h
    rw [Std.TreeMap.Raw.getElem?_ofList_of_mem Std.ReflCmp.compare_self keys hp] at mem
    cases mem
    exact each _ hp
  · rw [Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false (by simpa using h)] at mem
    cases mem

/-- A name in a rebuilt well-formed object gives the rebuilt value that the object holds under it.

A name that the object does not hold gives none. -/
theorem getObjVal?_canonical {members : Std.TreeMap.Raw String Lean.Json} (wf : members.WF)
    (name : String) :
    (canonical (.obj members)).getObjVal? name =
      ((Json.obj members).getObjVal? name).map canonical := by
  obtain ⟨⟨t⟩⟩ := members
  have hc : canonical (.obj ⟨⟨t⟩⟩) = .obj (insertAll canonical (inorder t) ∅) := by
    simp [canonical, canonicalMembers_eq, insertAll]
  have hd : ((inorder t).map Prod.fst).Nodup := by
    rw [← keys_mk]
    exact Std.TreeMap.Raw.nodup_keys wf
  have key : (insertAll canonical (inorder t) ∅)[name]? =
      ((⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json)[name]?).map canonical := by
    by_cases h : name ∈ (inorder t).map Prod.fst
    · obtain ⟨⟨k, v⟩, hp, rfl⟩ := List.mem_map.mp h
      have hm := hp
      rw [← toList_mk, Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf] at hm
      rw [hm, getElem?_insertAll_of_mem canonical _ _ Std.TreeMap.Raw.WF.emptyc hd hp]
      rfl
    · rw [getElem?_insertAll_of_not_mem canonical _ _ Std.TreeMap.Raw.WF.emptyc h,
        Std.TreeMap.Raw.getElem?_emptyc]
      cases hg : (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json)[name]? with
      | none => rfl
      | some v =>
        rw [← Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some wf, toList_mk] at hg
        exact absurd (List.mem_map.mpr ⟨_, hg, rfl⟩) h
  rw [hc, Toolchain.Json.getObjVal?_eq, Toolchain.Json.getObjVal?_eq]
  simp only [Std.TreeMap.Raw.get?_eq_getElem?, key]
  cases (⟨⟨t⟩⟩ : Std.TreeMap.Raw String Lean.Json)[name]? <;> rfl

end EthLib.Base.Json
