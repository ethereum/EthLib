module

public import Std.Data.TreeMap.Basic
public import Std.Data.TreeSet.Basic

/-!
# `Base.List`

Prefixes and suffixes of lists, which text formats read around their fields.

Also a table of values by key, kept in order, as stream multiplexers keep their streams.

Also the first element of a list that occurs again, as duplicate checks name it.

Also the distinct elements of a list, as batch checks share one copy of each.
-/

@[expose] public section

namespace EthLib.Base

/-- The rest of a list after a prefix, if the list starts with it. -/
def dropPrefix? {α : Type} [DecidableEq α] : List α → List α → Option (List α)
  | [], cs => some cs
  -- Each element of the prefix must match the next element of the list.
  | p :: ps, c :: cs => if p = c then dropPrefix? ps cs else none
  | _ :: _, [] => none

/-- The start of a list before a suffix, if the list ends with it. -/
def dropSuffix? {α : Type} [DecidableEq α] (suf cs : List α) : Option (List α) :=
  if suf.isSuffixOf cs then some (cs.take (cs.length - suf.length)) else none

/-- A table of pairs with the value of a key set, in place if the table has it, else at the end.

A lookup by key reads it. -/
def replaceKey {κ α : Type} [BEq κ] (pairs : List (κ × α)) (key : κ) (value : α) :
    List (κ × α) :=
  -- Replacing in place keeps the order of the keys, so the table lists them as they came.
  if pairs.any (·.1 == key) then pairs.map fun e => if e.1 == key then (key, value) else e
  else pairs ++ [(key, value)]

/-- The first element of a list that occurs again later in it, if any. -/
def firstRepeated {α : Type} [Ord α] (l : List α) : Option α :=
  -- One pass from the end, with the set of the elements after the current one.
  --
  -- The set is a search tree of the order, so each element costs one lookup and one insertion.
  --
  -- The last one found is the first.
  (l.foldr (init := ((∅ : Std.TreeSet α), (none : Option α))) fun x (later, found) =>
    -- The lookup comes before the insertion, so the insertion updates the set in place.
    let again := later.contains x
    (later.insert x, if again then some x else found)).2

/-- The scan for a repeat from a place, given the set of the elements before it. -/
def firstRepeatIndexFrom {α : Type} [Ord α] (earlier : Std.TreeSet α) (place : Nat) :
    List α → Option Nat
  | [] => none
  -- The first element in the set ends the scan.
  | x :: xs =>
    if earlier.contains x then some place
    else firstRepeatIndexFrom (earlier.insert x) (place + 1) xs

/-- The place of the first element of a list that equals an earlier one, if any. -/
def firstRepeatIndex {α : Type} [Ord α] (l : List α) : Option Nat :=
  -- One pass from the start, with a search tree of the elements before the current one.
  firstRepeatIndexFrom ∅ 0 l

/-- The distinct elements of a list in order, and the place of each element among them. -/
def distinctPlaces {α : Type} [Ord α] (l : List α) : Array α × Array Nat :=
  -- One pass, with a search tree from each distinct element to its place.
  let (distinct, places, _) :=
    l.foldl (init := ((#[] : Array α), (#[] : Array Nat), (∅ : Std.TreeMap α Nat)))
      fun (distinct, places, seen) x =>
        match seen.get? x with
        -- A repeat takes the place of its first copy.
        | some j => (distinct, places.push j, seen)
        -- A new element goes at the end.
        | none => (distinct.push x, places.push distinct.size, seen.insert x distinct.size)
  (distinct, places)

end EthLib.Base
