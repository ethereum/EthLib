module

public import EthLib.Cryptography.Proofs.Bls.Security.PopBound
public import EthLib.Cryptography.Proofs.Bls.Security.PopByteGame
public import EthLib.Cryptography.Proofs.Bls.Security.PopEager
public import EthLib.Cryptography.Proofs.Bls.Security.PopExtract
public import EthLib.Cryptography.Proofs.Bls.Security.PopReduction
public import EthLib.Cryptography.Proofs.Bls.Security.PopRefinement
public import EthLib.Cryptography.Proofs.Bls.Security.PopWins
public import EthLib.Cryptography.Proofs.Bls.Security.PopZeroKey
public import EthLib.Cryptography.Proofs.Bls.Security.Refinement

/-!
# Proofs: the security of BLS signatures

In the random oracle model, a BLS forger gives a solver of a co-Diffie-Hellman problem.

A forger within `q` hash calls wins at most `q` times as often as that solver.

EthLib's signing and verification compute the scheme of that game.

The byte game reduces a forger on compressed encodings to a group-element forger.

Freshness excludes every message submitted to signing, regardless of signature bytes.

A second game states unforgeability of aggregates with proofs of possession.

The algebraic step of its reduction is proved, on programmed hashes.

A valid aggregate with valid proofs on key hashes `r x • Z` gives `a • Z`, for the key `a • g1`.

That needs every key to be a multiple of `g1`, no `r x` to be zero, and a nonzero honest count.

The game is unchanged in distribution when one message hash scalar is drawn right after the key.

The aggregate game's reduction answers every oracle without the secret key.

Fix the guess `j`, and let the co-CDH challenge be `z • g2`, with `z` the scalar drawn first.

Let `z ≠ 0`.

Then an event of the game, read on the state the reduction sees, is at most as likely in its run.

This holds until the message at position `j` is signed.

Fix the secret and the scalar of the honest key hash, in a game within `qK` key hash calls.

Then some other key gets the scalar 0 with probability at most `(qK - 1) / |F|`.

A winning forgery at the guessed position gives the reduction its answer.

That needs `z ≠ 0`, every key a multiple of `g1`, no other key of scalar 0, and a nonzero count.

So such a win is at most as likely as a success of the reduction.

Take a forger on aggregates within `q` message and `qK` key hash calls.

It wins at most `q` times as often as the reduction at co-CDH, plus `(q + qK - 1) / |F|`.
-/
