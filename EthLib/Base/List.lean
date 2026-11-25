module

public import Std.Data.HashSet.Basic

/-!
# `Base.List`

Prefixes and suffixes of lists, which text formats read around their fields.

Also a table of values by key, kept in order, as stream multiplexers keep their streams.

Also the first element of a list that occurs again, as duplicate checks name it.
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
def firstRepeated {α : Type} [BEq α] [Hashable α] (l : List α) : Option α :=
  -- One pass from the end, with the set of the elements after the current one.
  --
  -- So each element costs one lookup and one insertion, and the last one found is the first.
  (l.foldr (init := ((∅ : Std.HashSet α), (none : Option α))) fun x (later, found) =>
    -- The lookup comes before the insertion, so the insertion updates the set in place.
    let again := later.contains x
    (later.insert x, if again then some x else found)).2

end EthLib.Base
