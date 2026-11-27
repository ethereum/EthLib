module

public import EthLib.Cryptography.Proofs.RandomOracleDisjoint
public import EthLib.Cryptography.Proofs.HashSig.Oracle

/-!
# Proofs: domain separation of Keccak-256 inputs under one random oracle

The oracle takes byte strings and answers 32 bytes, as leanXMSS and leanSPHINCS use Keccak-256.

The random-permutation proofs show Keccak-256 on byte strings indifferentiable from this oracle.

Under two tags where neither starts the other, no hash input of one computation is one of the other.

The same holds for hash inputs of two different lengths.

In both cases, the outputs of the two computations are independent.
-/

@[expose] public section

namespace EthLib.Cryptography.HashSig

open OracleSpec OracleComp

/-! ## Disjoint sets of inputs -/

/-- No input starts with two tags when neither tag starts the other. -/
private theorem not_prefix_of_prefix {tag tag' : HashInput} (htag : ¬tag <+: tag')
    (htag' : ¬tag' <+: tag) (x : HashInput) (hx : tag <+: x) : ¬tag' <+: x := fun hx' =>
  (List.prefix_or_prefix_of_prefix hx hx').elim htag htag'

/-- No input has two lengths. -/
private theorem length_ne_of_length_eq {n n' : Nat} (hn : n ≠ n') (x : HashInput) (hx : x.length = n) :
    ¬x.length = n' := hx ▸ hn

/-! ## Independence -/

/-- **Hashing under two tags, where neither starts the other, gives independent outputs.**

Every hash input of the first computation starts with `tag`.

Every hash input of the second, for each output of the first, starts with `tag'`. -/
theorem run'_romImpl_bind_evalDistEq_of_prefix {α β : Type} {tag tag' : HashInput}
    (htag : ¬tag <+: tag') (htag' : ¬tag' <+: tag) {oa : OracleComp OracleWorld α}
    {f : α → OracleComp OracleWorld β}
    (ha : oa.AllQueriesSatisfy (CoinOrHashIn HashSpec (tag <+: ·)))
    (hf : ∀ a, (f a).AllQueriesSatisfy (CoinOrHashIn HashSpec (tag' <+: ·))) :
    (simulateQ HashSpec.romImpl (oa >>= f)).run' ∅ =ᵈ
      ((simulateQ HashSpec.romImpl oa).run' ∅ >>= fun a =>
        (simulateQ HashSpec.romImpl (f a)).run' ∅) :=
  run'_simulateQ_romImpl_bind_evalDistEq (not_prefix_of_prefix htag htag') ha hf

/-- **Hashing inputs of two different lengths gives independent outputs.**

Every hash input of the first computation has `n` bytes.

Every hash input of the second, for each output of the first, has `n'` bytes. -/
theorem run'_romImpl_bind_evalDistEq_of_length {α β : Type} {n n' : Nat} (hn : n ≠ n')
    {oa : OracleComp OracleWorld α} {f : α → OracleComp OracleWorld β}
    (ha : oa.AllQueriesSatisfy (CoinOrHashIn HashSpec (·.length = n)))
    (hf : ∀ a, (f a).AllQueriesSatisfy (CoinOrHashIn HashSpec (·.length = n'))) :
    (simulateQ HashSpec.romImpl (oa >>= f)).run' ∅ =ᵈ
      ((simulateQ HashSpec.romImpl oa).run' ∅ >>= fun a =>
        (simulateQ HashSpec.romImpl (f a)).run' ∅) :=
  run'_simulateQ_romImpl_bind_evalDistEq (length_ne_of_length_eq hn) ha hf

end EthLib.Cryptography.HashSig
