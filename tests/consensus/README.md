# Consensus test vectors

A preset or a configuration of the beacon chain is a list of named values.
EthLib writes each list in Lean, and a typo in one value would change every rule that reads it.
So the Python suite compares the Lean values with the files that consensus-specs publishes.

The directory `parameters/` holds those files: the mainnet and minimal presets from Phase 0 to Fulu, and the mainnet and minimal configurations.
They come from `ethereum/consensus-specs` at commit `aa16bb4c156184e9548a997d53efaf2a228a6304`, the release `v1.7.0-beta.4`.
Each file keeps its upstream bytes and its upstream path below `parameters/`, and `parameters/SHA256SUMS` records its digest.

`bindings/python/tests/consensus/test_parameters.py` reads them and runs three comparisons:

- Each preset in Lean holds every value of the preset files, under the same name.
- Each configuration in Lean holds every value of its file up to Fulu.
  The gossip message ID defines the two message domains of the file as constants, so the configuration leaves them out.
- At each fork from Phase 0 on, the parameters in Lean hold each value that a fork replaces.
  Each one is the value of the latest fork that names it.

A replacement carries the name of its fork as a suffix, such as `INACTIVITY_PENALTY_QUOTIENT_ALTAIR` in the Altair preset.
One suffixed value is new rather than a replacement: `MAX_EFFECTIVE_BALANCE_ELECTRA`, the largest effective balance of a compounding validator.
The suite fails on any other suffixed value, so a replacement that Lean does not hold cannot pass unnoticed.

The directory `networking/` holds the custody vectors of Fulu from the test release `v1.7.0-beta.4` of `ethereum/consensus-specs`, built at the same commit.
They are the cases of the handlers `get_custody_groups` and `compute_columns_for_custody_group`, copied byte for byte under their path in `mainnet.tar.gz` and `minimal.tar.gz`.
The minimal cases hold the same values as the mainnet ones, because the two presets share every custody parameter.
They still run the Lean definitions on the minimal preset.
The release repeats the same cases for Gloas and Heze, with only the fork name changed, so the directory keeps those of Fulu.
`bindings/python/tests/consensus/test_custody.py` runs each case through the Lean definitions.

The directory `ssz_static/` holds static SSZ cases of the containers that EthLib defines.
A case gives the bytes of a container, compressed with Snappy, and the root of its value.
They are copied byte for byte under their path in `minimal.tar.gz` and `mainnet.tar.gz`, from Phase 0 to Fulu.
From each archive the directory keeps the first case of each suite.
It keeps the files `serialized.ssz_snappy` and `roots.yaml` of each case, and leaves out `value.yaml`.
`bindings/python/tests/consensus/test_ssz_static.py` decodes each case in Lean, then checks the root and the bytes encoded again.
Every week, the same test also runs every case of both archives for the containers that EthLib defines.
It then checks that the vendored files are copies of the archived ones.

The directory `shuffling/` holds the shuffling cases of Phase 0 from the same test release, for the minimal and the mainnet presets.
They are copied byte for byte under their path in `minimal.tar.gz` and `mainnet.tar.gz`.
Each case gives a seed, a count of indices and the shuffled position of each index.
The shuffle runs the 10 rounds of the minimal preset or the 90 rounds of the mainnet preset.
`bindings/python/tests/consensus/test_shuffling.py` compares each list with the shuffle in Lean.

The run on each change reads only the cases of this directory, and the weekly parity job reads every case of the archives.
That job also fails when a preset, fork and handler that a runner covers has no case here.
So a new runner comes with vendored cases of each preset and fork.

The directory `merkle_proof/` holds every `single_merkle_proof` case of `BeaconBlockBody`, from Deneb to Fulu, in both archives.
A case gives a body, a generalized index, the node at that index and its branch.
Each case keeps its files `object.ssz_snappy` and `proof.yaml` under its path in the archive.
`bindings/python/tests/consensus/test_merkle_proof.py` builds the node and the branch in Lean, and compares them with the case.

The directory `light_client/` holds the `single_merkle_proof` cases of the light client, from Altair to Fulu, in both archives.
A case gives a beacon state or a block body, and the node of a sync committee, the finalized root or the execution payload.
It also gives the generalized index of that node and its branch.
Each case keeps its files `object.ssz_snappy` and `proof.yaml` under its path in the archive.
The release also has cases for Gloas and Heze, and the directory leaves them out until EthLib specifies those forks.
`bindings/python/tests/consensus/test_light_client_proofs.py` builds the node and the branch in Lean, and compares them with the case.
It also climbs the branch with the SHA-256 of `hashlib`, to check that it reaches the root of the value.
Every week, the same test also runs every case of both archives and checks that the vendored files are copies.

The same directory holds the minimal `sync` and `update_ranking` cases of the light client, from Altair to Fulu.
A `sync` case gives a trusted block root, a bootstrap and a list of steps.
A step processes an update or forces one, then gives the slot and the roots of the finalized and the optimistic header.
A `sync` case also gives its configuration, which replaces values of the minimal configuration.
The directory keeps the four `sync` cases of each fork that stay at one fork.
The other cases upgrade the bootstrap or the store to a later fork, which EthLib does not specify yet.
An `update_ranking` case lists updates from the best to the worst.
`bindings/python/tests/consensus/test_light_client_sync.py` runs both kinds of cases in Lean.

The directory `data_columns/` holds the Fulu, Gloas and Heze cases of the gossip handler `gossip_data_column_sidecar`, in both archives.
Each case keeps its files under its path in the archive, except the state, which the checks of a sidecar alone do not read.
A case gives some sidecars, each with the verdict of gossip validation and the reason for a rejection.
`bindings/python/tests/consensus/test_data_column.py` runs the three checks of a sidecar alone at Fulu: its shape, its branch and its cell proofs.
A sidecar rejected for one of them fails that check, and every other sidecar passes all three.
From Gloas a sidecar has no branch, and its commitments are in the bid of the block whose root it names.
So from Gloas the file finds that block among the blocks of the case, and runs the two other checks against it.
A sidecar whose block the case does not give must be rejected before gossip validation reads the block.
The rest of gossip validation reads the store of the fork choice, which EthLib does not hold yet.
The same file rebuilds every sidecar of a block from one sidecar, and from the bodies of `merkle_proof/` for Fulu.
From Gloas it rebuilds each valid sidecar from its block, and from itself.
It also builds the matrix of two blobs of the KZG vectors under `tests/cryptography/kzg/`, and recovers it from half of its columns.

The directory `operations/` holds block operation cases of `minimal.tar.gz`, copied byte for byte under their path in the archive.
A case gives a state before the operation, the operation, and the state after it when the operation is valid.
A case without a state after it must be rejected.
The directory keeps two cases of each handler that EthLib runs, at each fork where it runs.
These are the block header and the proposer and attester slashings from Phase 0 to Fulu.
They are also the attestation and the deposit at Phase 0, and the voluntary exit from Phase 0 to Capella.
The withdrawals and the changes of BLS credentials run from Capella to Fulu.
At Gloas they are the payload attestation, the execution payload bid, and the builder deposit and exit requests.
From Gloas a slashing also removes the pending builder payments of the slashed proposer, which EthLib does not hold yet.
Where the handler has both, one case is valid and one invalid.
Every builder deposit or exit request case of the release has a state after it.
So the second case of these two handlers is a request that leaves the state as it was.
A mainnet state is a few hundred kilobytes, so only the weekly parity job reads the mainnet cases.
`bindings/python/tests/consensus/test_operations.py` runs each case through the Lean transition and compares the state after it.

The directory `epoch_processing/` holds epoch step cases of `minimal.tar.gz` in the same way.
A case gives a state before the step and the state after it.
The directory keeps two cases of each step that EthLib runs, at each fork where it runs.
These are justification and finalization, and the rewards and penalties, at Phase 0.
They are also the proposer lookahead at Fulu and Gloas.
Then come the builder pending payments and the window of payload committees at Gloas.
The release has a single case of the window, so the directory keeps that one.
`bindings/python/tests/consensus/test_epoch_processing.py` runs each case through the Lean step and compares the state after it.

The test release publishes its cases in three archives.
Their SHA-256 digests are:

- `general.tar.gz`: `c4f395f71f606c28093500e32067990e430cc73a2277be6f3bf5090adcce3f67`, 3,228 bytes.
- `mainnet.tar.gz`: `67762986572372a08d3b182535aa760433c86e174e14e0bbd756f350dd19398c`, 967,886,924 bytes.
- `minimal.tar.gz`: `26d09aea70c62ed235a120a95082d544ab1c2e6fe36bd35ea1bd5da62f3b7b68`, 468,730,308 bytes.
