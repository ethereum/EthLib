import Lean

/-!
# Attribute registration for the theorem placement fixtures

The declarations that use these attributes import this module so its initializers have run.
-/

open Lean Meta

register_simp_attr placement_simp
register_label_attr placement_tag
