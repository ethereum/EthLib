module

/-!
# `Base.List`

Prefixes and suffixes of lists, which text formats read around their fields.
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

end EthLib.Base
