module

/-!
# Inverses in a prime field

The inverse of `a` mod `m` comes from the extended Euclidean algorithm on `a` and `m`.

It is Algorithm 2.142 of the Handbook of Applied Cryptography, chapter 2:
<https://cacr.uwaterloo.ca/hac/about/chap2.pdf>.

The algorithm finds `s` with `s * a = gcd(a, m) mod m`.

When `m` is prime and `a` is not zero, the gcd is `1`, so `s` is the inverse of `a`.
-/

@[expose] public section

namespace EthLib.Cryptography

/-- The extended Euclidean algorithm on the remainders `r` and `r'`.

Each remainder carries a coefficient, `s` for `r` and `s'` for `r'`.

A step replaces `(r, r')` with `(r', r mod r')`, and the coefficients follow the same rule.

When `r'` reaches `0`, `r` is the gcd, and the result is its coefficient `s`. -/
def euclid (r r' : Nat) (s s' : Int) : Int :=
  if r' = 0 then s
  else euclid r' (r % r') s' (s - ((r / r' : Nat) : Int) * s')
termination_by r'
decreasing_by exact Nat.mod_lt _ (by omega)

/-- The inverse of `a` mod `m`, by the extended Euclidean algorithm.

The run starts on `a` and `m`, with the coefficients `1` and `0`.

So each coefficient times `a` equals its remainder, mod `m`.

The result is the coefficient of the gcd, reduced mod `m`.

When `m` is prime, it is the inverse of `a` for `a != 0`, and it sends `0` to `0`. -/
def Fin.inverse {m : Nat} [NeZero m] (a : Fin m) : Fin m :=
  Fin.ofNat m (euclid a.val m 1 0 % m).toNat

end EthLib.Cryptography
