# Bridges to ArkLib

Some leanVM proofs need coding theory that [ArkLib](https://github.com/Verified-zkEVM/ArkLib) already proves.
The soundness of WHIR with affine folds needs Theorem 4.10 of [Chiesa, Weissenberg, Yogev and Zheng](https://eprint.iacr.org/2026/2863), on affine combiners for Reed-Solomon proximity gaps.
The proofs also need the Johnson bound, which limits how many codewords lie close to one word.
EthLib does not prove these results again.
It uses ArkLib's theorems through bridge theorems, and the files that hold them live in this directory.

A bridge theorem restates one ArkLib result over EthLib's own definitions.
ArkLib states its results over its own types, such as its Reed-Solomon codes and its distances, and EthLib's specification has types of its own.
The bridge converts between the two and then applies ArkLib's theorem, so the proof is a translation and contains no coding theory of its own.
EthLib never copies an ArkLib proof.

Four rules keep ArkLib's types out of the rest of the proofs:

- A bridge file is `EthLib/Cryptography/Proofs/Bridge/ArkLib/<Topic>.lean`, and it is the only kind of EthLib file that imports ArkLib's coding theory.
- A bridge file states one theorem per ArkLib result, over EthLib's definitions.
- The doc comment of a bridge theorem cites the paper and its section, such as Theorem 4.10 of Chiesa, Weissenberg, Yogev and Zheng, and names the ArkLib theorem it applies.
- Every other EthLib proof imports the bridge file, never ArkLib's coding theory.

One file is an exception.
The multilinear extension of EthLib's specification is ArkLib's multilinear extension on the same values, so `EthLib/Cryptography/Proofs/Multilinear/Extension.lean`, the file that proves the two equal, imports `ArkLib.Data.MvPolynomial.Multilinear` directly.
That file is itself the bridge for multilinear extensions.

ArkLib is a dependency of the proofs only.
The specification never imports it, so building the `EthLib` library compiles no ArkLib module.
