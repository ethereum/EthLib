//! The BLS operations, one module per handler.
//!
//! The handlers follow consensus-specs, `altair/bls.md`.

mod fixtures;

mod eth_aggregate_pubkeys;
mod eth_fast_aggregate_verify;

use crate::Case;

/// The suite directory of the BLS vectors.
const KIND: &str = "bls";

/// Collects the cases of each BLS operation.
pub(crate) const OPERATIONS: [fn(&mut Vec<Case>); 2] = [
    Case::collect::<eth_aggregate_pubkeys::EthAggregatePubkeys>,
    Case::collect::<eth_fast_aggregate_verify::EthFastAggregateVerify>,
];
