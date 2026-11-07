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
They are copied byte for byte under their path in `minimal.tar.gz` and `mainnet.tar.gz`, from Phase 0 to Heze.
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

The directory `light_client/` holds the `single_merkle_proof` cases of the light client, from Altair to Heze, in both archives.
A case gives a beacon state or a block body, and the node of a sync committee, the finalized root or the execution data.
From Capella to Fulu that data is the execution payload, and from Gloas the parent block hash of the bid.
It also gives the generalized index of that node and its branch.
Each case keeps its files `object.ssz_snappy` and `proof.yaml` under its path in the archive.
`bindings/python/tests/consensus/test_light_client_proofs.py` builds the node and the branch in Lean, and compares them with the case.
It also climbs the branch with the SHA-256 of `hashlib`, to check that it reaches the root of the value.
Every week, the same test also runs every case of both archives and checks that the vendored files are copies.

The same directory holds the minimal `sync` and `update_ranking` cases of the light client, from Altair to Gloas.
A `sync` case gives a trusted block root, a bootstrap and a list of steps.
A step processes an update or forces one, then gives the slot and the roots of the finalized and the optimistic header.
A `sync` case also gives its configuration, which replaces values of the minimal configuration.
The directory keeps every `sync` case: the four of each fork that stay at one fork, and those that upgrade to a later fork.
An upgrade case brings the bootstrap, the updates or the store to the form of a later fork first.
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
The Fulu and Gloas cases run in full from `gossip/`, which keeps them with their state.
At Heze the rest of gossip validation waits for the Heze rules.
The same file rebuilds every sidecar of a block from one sidecar, and from the bodies of `merkle_proof/` for Fulu.
From Gloas it rebuilds each valid sidecar from its block, and from itself.
It also builds the matrix of two blobs of the KZG vectors under `tests/cryptography/kzg/`, and recovers it from half of its columns.


The directory `operations/` holds block operation cases of `minimal.tar.gz`, copied byte for byte under their path in the archive.
A case gives a state before the operation, the operation, and the state after it when the operation is valid.
A case without a state after it must be rejected.
The directory keeps two cases of each handler that EthLib runs, at each fork where it runs.
These are the block header from Phase 0 to Fulu, and the proposer and attester slashings from Phase 0 to Gloas.
They are also the attestation from Phase 0 to Gloas and the deposit from Phase 0 to Electra.
The voluntary exit runs from Phase 0 to Gloas too.
The attestation at Electra and Fulu and the voluntary exit at Electra, Fulu and Gloas keep one case each.
The deposit, withdrawal and consolidation requests run from Electra to Gloas.
After Electra the requests keep one case each.
The sync aggregate runs from Altair to Fulu.
The execution payload runs from Bellatrix to Fulu.
Its cases also fix the answer of the execution layer, in `execution.yaml`.
Bellatrix keeps two more of them: a payload with a transaction of no bytes, and a wrong parent hash.
The withdrawals and the changes of BLS credentials run from Capella to Fulu.
At Gloas they are the payload attestation, the execution payload bid, and the builder deposit and exit requests.
The parent execution payload also runs at Gloas, from a block whose payload is in its parent.
From Gloas a slashing also removes the pending builder payments of the slashed proposer.
At Gloas the attestation keeps four cases.
In the two valid cases, a builder payment gains weight, and a payload vote that does not match earns no head flag.
The two invalid cases have an index above one, and index one in a vote for the block of its own slot.
The exit churn cases of Gloas run as voluntary exits, and the directory keeps one of them.
Where the handler has both, one case is valid and one invalid.
Every builder deposit or exit request case of the release has a state after it.
So the second case of these two handlers is a request that leaves the state as it was.
A mainnet state is a few hundred kilobytes, so only the weekly parity job reads the mainnet cases.
`bindings/python/tests/consensus/test_operations.py` runs each case through the Lean transition and compares the state after it.

The directory `epoch_processing/` holds epoch step cases of `minimal.tar.gz` in the same way.
A case gives a state before the step and the state after it.
The directory keeps two cases of each step that EthLib runs, at each fork where it runs.
These are justification and finalization, and the rewards and penalties, from Phase 0 to Gloas.
The inactivity scores, the rotation of the flags and the sync committee update run from Altair to Gloas.
The historical summaries run from Capella to Gloas.
The registry updates, the slashings and the effective balances run from Phase 0 to Gloas.
They keep one case each at Electra, Fulu and Gloas.
The resets of the deposit votes, the slashings and the RANDAO mixes run from Phase 0 to Gloas.
The historical roots run from Phase 0 to Bellatrix, and the rotation of pending attestations at Phase 0.
They are also the proposer lookahead at Fulu and Gloas.
Then come the builder pending payments and the window of payload committees at Gloas.
The pending deposits and the pending consolidations run from Electra to Gloas.
Electra keeps three cases of the deposits and two of the consolidations, and Fulu and Gloas one each.
The deposit churn cases of Gloas run as pending deposits, and the directory keeps two of them.
The release has a single case of the window, so the directory keeps that one.
Where a step has no case without a state after it, both kept cases are valid.
The release has no mainnet case of the sync committee update, since its period is 256 epochs.
`bindings/python/tests/consensus/test_epoch_processing.py` runs each case through the Lean step and compares the state after it.

The directory `rewards/` holds rewards cases of `minimal.tar.gz` in the same way.
A case gives a state, and the rewards and penalties of each validator for each kind of vote.
Before Altair the kinds are the source, the target, the head, the inclusion delay and inactivity.
From Altair the source, the target and the head are participation flags, and the inclusion delay is gone.
The directory keeps one case of each group at each fork from Phase 0 to Gloas.
The groups are `basic`, `leak` and `random`, and from Altair also `inactivity_scores`.
`bindings/python/tests/consensus/test_rewards.py` computes each kind of deltas in Lean and compares them with the case.

The directory `transition/` holds cases of the whole state transition from `minimal.tar.gz` in the same way.
A `sanity/slots` case advances a state by some slots.
A `sanity/blocks`, `finality` or `random` case runs a list of signed blocks, and must be rejected when it has no state after it.
The directory keeps two cases of each group at each fork whose whole transition EthLib holds.
These forks are Phase 0, Altair, Bellatrix, Capella and Deneb.
Electra, Fulu and Gloas run too, with one case of each group at each of them.
Gloas keeps three `sanity/slots` cases: two reset the availability of a payload, and one crosses an epoch.
`bindings/python/tests/consensus/test_transition.py` runs each case through the Lean transition and compares the state after it.

The directory `fork/` holds upgrade cases from `minimal.tar.gz` in the same way.
A case gives a state of one fork and the state that the upgrade to the next fork makes of it.
The directory keeps at least two cases of each upgrade from Altair to Heze.
It keeps more where the upgrade has steps of its own: the attestations of Altair, the queues of Electra and the builders of Gloas.
`bindings/python/tests/consensus/test_fork.py` runs each case through the Lean upgrade and compares the state after it.

The directory `fork_choice/` holds cases of the fork choice from `minimal.tar.gz` in the same way.
A case starts a store from an anchor state and an anchor block, then runs a list of steps.
A step moves the clock, adds a block, an attestation, an attester slashing or a block of proof of work, or checks the store.
From Deneb a block step can also give the blobs and the proofs that the node holds for the block.
The directory keeps one case of each handler at Altair, Bellatrix, Capella and Deneb, and two of `on_block`, one of which a store must reject.
At Bellatrix it also keeps two `on_merge_block` cases.
In the first, the first payload follows a terminal block of proof of work.
In the second, the store does not know the parent of the block that the payload follows.
At Deneb it also keeps two `on_block` cases with blobs.
In the first, the proofs show that the blobs match the commitments of each block.
In the second, a proof does not match, so the store rejects the block.
At Electra and Fulu it keeps the smallest case of each handler, of the optimistic sync and of each fast confirmation suite.
Electra adds the handler `deposit_with_reorg`.
At Fulu its `on_block` case is one whose block lacks the columns that the node samples.
`bindings/python/tests/consensus/test_fork_choice.py` runs each case on one store in Lean and compares each step with the case.

The directory `gossip/` holds gossip validation cases from `minimal.tar.gz` in the same way.
A case starts a store from an anchor state and an anchor block, then validates a list of messages of one topic in turn.
Each message expects to be valid, ignored or rejected, and a failure names its reason.
The directory keeps the cases of attester slashings, proposer slashings, voluntary exits and changes of BLS credentials.
It keeps every case of these topics at Capella and Deneb, since Deneb changes the domain of an exit signature.
At Phase 0, Altair, Bellatrix, Electra and Fulu it keeps the case with one valid message of each topic.
It also keeps the cases of the two sync committee topics, which start at Altair.
It keeps every case of these two topics at Altair, and the case with one valid message at each later fork.
It keeps every case of the block topic from Altair to Deneb.
A block case may import more blocks after the anchor, and mark some as failed or pending.
It may also give the status of their payloads, and replace the finalized checkpoint.
At Phase 0, Electra and Fulu it keeps the case with one valid block.
It keeps every case of the attestation and aggregate topics at Altair, Deneb and Electra.
Deneb changes the window of time of a vote, and Electra moves the committee out of the attestation data.
At Phase 0, Bellatrix, Capella and Fulu it keeps the case with one valid message of each of these topics.
It keeps every blob sidecar case at Deneb, and at Electra the valid case and the case of an index past the limit.
It keeps every Fulu case of the column sidecar topic, with its state.
It keeps every Fulu case of the partial column topic too.
A partial message carries some cells of one column and a bitmap of the blobs that they belong to.
On the first push it also carries the header of its block.
A case gives a group ID with each message, and may list headers that the node has already validated.
At Gloas it keeps four cases of the topic of proposer preferences.
It also keeps every Gloas case of the topics of payload envelopes and of payload votes.
From Gloas a block of a case may come with the envelope of its payload, which the store keeps.
It keeps nine Gloas cases of the topic of bids.
A bid case also sends the proposer preferences and the envelopes that its bids rely on.
It keeps 24 Gloas cases of blocks, attestations and aggregates, for the checks that Gloas adds.
Those checks read the bid of a block, its parent payload, and the payload that a vote sees.
The anchor block of a case may come with the envelope of its payload too.
At Gloas it keeps one valid case of each of the six topics that Gloas leaves unchanged.
It keeps every minimal Gloas case of the column sidecar topic too.
`bindings/python/tests/consensus/test_gossip_validation.py` validates each message in Lean and compares the outcome and the reason with the case.

The directory `genesis/` holds every genesis case of `minimal.tar.gz` in the same way.
An `initialization` case builds the genesis state from a block hash, a time and some deposits.
A `validity` case tells whether a candidate state launches the chain.
The release has genesis cases only at Phase 0 and only for the minimal preset.
`bindings/python/tests/consensus/test_genesis.py` runs each case through the Lean genesis and compares the result.

The test release publishes its cases in three archives.
Their SHA-256 digests are:

- `general.tar.gz`: `c4f395f71f606c28093500e32067990e430cc73a2277be6f3bf5090adcce3f67`, 3,228 bytes.
- `mainnet.tar.gz`: `67762986572372a08d3b182535aa760433c86e174e14e0bbd756f350dd19398c`, 967,886,924 bytes.
- `minimal.tar.gz`: `26d09aea70c62ed235a120a95082d544ab1c2e6fe36bd35ea1bd5da62f3b7b68`, 468,730,308 bytes.
