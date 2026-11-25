module

public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Game
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.Reasons
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.SeedHops
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.IdealFailure
public import EthLib.Cryptography.Proofs.Xmss.Unforgeability.AdversaryBudget

/-!
# Proofs: leanXMSS as EthLib computes it is unforgeable

Source: the leanXMSS specification draft, section "Security".

The game is the generic strong-unforgeability game, with leanXMSS as its scheme.

The theorem holds in the random oracle model.

The game's signer keeps its key across requests, as a real signer does.

Take an adversary whose game makes at most `q >= 1` hash calls on every run.

It forges a signature with probability at most `q / 2^127`.

`q` counts every hash call of the game, the signer's and key generation's included.

Key generation alone makes about `2^23.7` calls.

A signing request can make more than `2^32` calls, when its randomizer trials keep missing.

It can make more than `2^33` when it builds a bottom tree, which runs a second search.

So the bound is never below about `2^-103.3`, and each signing request adds at least `2^-95`.

With all `2^32` leaf indices signed, `q` exceeds `2^64`, and the bound exceeds `2^-63`.

A second form counts only the adversary's own calls: `qH` calls of `H` and `r` requests.

Its bound is `Q / 2^127`, with `Q = 205 * 2^16 + 1 + qH + r (2^33 + 205 * 2^16 + 407) + 384`.

For `r <= 2^32` it is at most `(qH + 2^65 + 205 * 2^48 + 407 * 2^32 + 205 * 2^16 + 385) / 2^127`.

The game runs EthLib's key generation, signing and verification.

Their hash `H` is a query to the oracle.

The security proof in `Security/` reasons over EthLib's algorithms too.

It compares them with a model of the scheme with precomputed keys, its own game-hopping device:

- EthLib's bytes, addresses and codewords are the model's.
- Each hashing routine of EthLib is the model's, call for call.
- EthLib's adversary is one of the model's.
- EthLib's game wins as often as the model's, and makes at least its hash calls.

The game's signer reads its trees from its key instead of rebuilding them.

Every call those trees stand for was made before, so the oracle's cache answers them alike.

A variant game has a signer that replies with its error, which tells which layer failed.

There the bound gains the probability that some signing request fails.

Two hidden-seed hops move that probability to a game whose derivations come from a lazy table.

Take an adversary that makes at most `qH` hash queries and `r` signing requests on every run.

The hops cost at most `2 Q / 2^256`, where `Q` bounds the hash calls of the game on every run.

Here `Q = 205 * 2^16 + 1 + qH + r (2^33 + 205 * 2^16 + 407) + 384`.

So it charges each request's worst case.

After the hops, some request fails with probability at most `r (Q / 2^95 + 2 exp(-4000))`.

A new search meets a cached trial with chance `<= Q / 2^96`, and fresh trials all fail rarely.

A repeated search succeeds once its first run did, since a trial with a codeword stays cached.

Until a request fails, every kept tree holds the top signature of a search that succeeded.

So the variant game's bound is `q / 2^127 + 2 Q / 2^256 + r (Q / 2^95 + 2 exp(-4000))`.

The last term is at least `r^2 / 2^62`, so it says nothing from about `2^31` requests.

That loss comes from the proof, which charges each new search the whole cache.
-/
