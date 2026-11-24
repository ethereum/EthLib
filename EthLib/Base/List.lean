module

/-!
# `Base.List`

Prefixes and suffixes of lists, which text formats read around their fields.

Also a table of values by key, kept in order, as stream multiplexers keep their streams.
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

end EthLib.Base
