# Transaction test vectors

The files here are the transaction tests of `ethereum/execution-specs`, from the release `tests@v21.0.2`.
The release targets commit `e27f097ec7b3e6e8ee9c2c1873c183e8f7da7a6e`, and its fixtures are under CC0-1.0.
Its archive `fixtures.tar.gz` has sha256 `e2fa7ea2ea516459f9ab92284b2927892f318f4e1f78ca802cb05a6c3b479ed9`.

Each file is a copy, without change, of a file under `fixtures/transaction_tests/` in that archive, at the same path.
A test holds the bytes of one transaction and, for each fork, the outcome that a client must reach.
The outcome is the hash, the sender and the intrinsic gas of the transaction, or the exception that rejects it.

The copy covers every fork that the release fills from Frontier to Osaka: 656 vectors in 178 files.
It leaves out the directory `for_amsterdam`, because EthLib does not yet specify the Amsterdam rules for transactions.

The Python test `bindings/python/tests/transactions/test_transactions.py` reads these files and never rewrites them.
`SHA256SUMS` pins each file.
