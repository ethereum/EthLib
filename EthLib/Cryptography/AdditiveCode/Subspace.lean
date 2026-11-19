module

public import EthLib.Cryptography.BinaryField.GF64

/-!
# `AdditiveCode.Subspace`

The basis of `K = GF(2^64)`, the points of its additive domains, and subspace polynomial values.

Lin, Chung and Han, Novel Polynomial Basis (FOCS 2014), section II, define these polynomials.

The paper is [arXiv 1404.3458](https://arxiv.org/abs/1404.3458).

The basis of `K` over `GF(2)` is `e_c = x^c` for `c < 64`.

The point `x_v` of a number `v < 2^64` is `sum_c v_c e_c`, where `v_c` is bit `c` of `v`.

So the 64-bit word of `x_v` is `v`, and `x_5` is `x^2 + 1`.

The subspace `S_i` spans `e_0, ..., e_{i-1}`, so its `2^i` points are the `x_v` with `v < 2^i`.

Its vanishing polynomial is `W_i(X) = prod_{u in S_i} (X + u)`, of degree `2^i`.

Lin, Chung and Han state that `W_i(a + b) = W_i(a) + W_i(b)` for all `a` and `b` in `K`.

The points of `S_{i+1}` are those of `S_i` and those of `e_i + S_i`.

So `W_{i+1}(a) = W_i(a) * W_i(a + e_i) = W_i(a) * (W_i(a) + W_i(e_i))` for each `a` in `K`.

The values of `W_i` then follow a recursion that never expands a product over `S_i`.

It starts at `W_0(a) = a` and steps by `W_{j+1}(a) = W_j(a)^2 + W_j(e_j) * W_j(a)`.

The normalizers `W_i(e_i)` come out of the same recursion, each from the ones before it.
-/

@[expose] public section

namespace EthLib.Cryptography.AdditiveCode

open EthLib.Cryptography.BinaryField (GF64)

/-- The basis element `e_c = x^c` of `GF64` over `GF(2)`: the word with only bit `c` set. -/
def basisElem (c : Fin 64) : GF64 := ⟨1 <<< c.val.toUInt64⟩

/-- The domain point `x_v = sum_c v_c e_c`: the `GF64` whose 64-bit word is `v mod 2^64`.

Bit `c` of `v` is the coefficient `v_c` of `x^c`, so the point of `5` is `x^2 + 1`. -/
def domainPoint (v : Nat) : GF64 := ⟨v.toUInt64⟩

/-- `W_i(a)`, from the normalizers `norms[j] = W_j(e_j)` for `j < i`.

It starts at `W_0(a) = a` and steps by `W_{j+1}(a) = W_j(a)^2 + norms[j] * W_j(a)`.

It reads only the entries below `i`. -/
def subspacePolyEval {n : Nat} (norms : Vector GF64 n) (i : Nat) (hi : i ≤ n) (a : GF64) :
    GF64 :=
  match i, hi with
  | 0, _ => a
  | j + 1, hj =>
    let w := subspacePolyEval norms j (Nat.le_of_succ_le hj) a
    w.square + norms[j] * w

/-- The normalizers `W_i(e_i)` for `i <= n`, with `n <= 63` so that `e_n` is a basis element.

Entry `i` is the value at `e_i` of `W_i`, computed from entries `0, ..., i-1`.

Entry `0` is `W_0(e_0) = e_0 = 1`.

The vector for `n + 1` extends the one for `n` by one entry. -/
def subspaceNormalizers (n : Nat) (hn : n ≤ 63) : Vector GF64 (n + 1) :=
  match n, hn with
  | 0, _ => #v[].push (subspacePolyEval #v[] 0 (Nat.le_refl 0) (basisElem 0))
  | m + 1, hm =>
    let acc := subspaceNormalizers m (by omega)
    acc.push (subspacePolyEval acc (m + 1) (Nat.le_refl _) (basisElem ⟨m + 1, by omega⟩))

end EthLib.Cryptography.AdditiveCode
