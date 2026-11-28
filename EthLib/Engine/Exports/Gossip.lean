module

public import EthLib.Consensus.Exports.BeaconApiPost
public import EthLib.Engine.ExecutionEngine

/-!
# `Exports.Gossip`

The C exports of gossip validation and of the Beacon API endpoints that publish through it.

From Gloas the envelope topic checks the block hash of a payload against the hash of its header.

That hash needs the trie roots of the execution layer, so these exports live here and pass it in.
-/

public section

namespace EthLib.Engine.Exports

open EthLib.Exports (Result PyValue pyExport)
open EthLib.Consensus.Exports

/-- Validate the messages of a topic in turn, against the store of an anchor and later blocks.

The arguments are the names of the preset and the fork, the anchor state and the anchor block.

Then come the later blocks, the finalized checkpoint or none, the topic and the messages.

Then come replacements of values of the configuration, and whether the signature checks run.

Every topic is specified here up to Heze. -/
@[export eth_consensus_gossip_validation]
def gossipValidationExport (args : PyValue) : Result PyValue :=
  pyExport (gossipValidationOf envelopeBlockHash) args

/-- Answer the requests to pool and publish endpoints in turn.

The arguments are the names of the preset and the fork, the anchor state and the anchor block.

Then come the later blocks, the finalized checkpoint or none, and the requests.

Then come replacements of values of the configuration, and whether the signature checks run.

Each answer gives its status code, the position and the message of each item that failed.

It also gives the events of the request, each as the name of its topic and its JSON data. -/
@[export eth_consensus_api_post]
def apiPostExport (args : PyValue) : Result PyValue := pyExport (apiPostOf envelopeBlockHash) args

end EthLib.Engine.Exports
