import LeanEthCS.Primitives
import LeanEthCS.Forks.Gloas.Primitives
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Electra.Requests
import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving

/-!
# `LeanEthCS.Forks.Gloas.Execution` — ePBS execution-envelope containers

EIP-7732 splits the beacon block from its execution payload. The
proposer commits to a builder's *bid* (`ExecutionPayloadBid`) in the
beacon block; the builder later reveals the actual payload in a
signed *envelope* (`ExecutionPayloadEnvelope`).

## Note on `ExecutionPayload`

Gloas's `ExecutionPayload` adds two fields beyond Deneb's:
* `block_access_list : BlockAccessList` (EIP-7928) — a complex new
  container not yet ported in this library;
* `slot_number : uint64` (EIP-7843).

This file re-uses Deneb's `ExecutionPayload` inside the envelope
for now. When `BlockAccessList` lands, swap the field type to a
new `Gloas.ExecutionPayload`.

## Containers

* `ExecutionPayloadBid` — what the proposer signs into the beacon
  block: the builder's commitment to a future payload (parent
  hashes, block hash, gas limit, value, etc.).
* `SignedExecutionPayloadBid` — bid + builder signature.
* `ExecutionPayloadEnvelope` — the post-attestation reveal: actual
  payload + execution requests + builder/block linkage.
* `SignedExecutionPayloadEnvelope` — envelope + builder signature.
-/

set_option autoImplicit false

namespace LeanEthCS.Forks.Gloas

open SizzLean

open SizzLean.Repr

open LeanEthCS
open LeanEthCS.Forks.Electra (ExecutionRequests)
open LeanEthCS.Macros

ssz_struct_for_presets ExecutionPayloadBid in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  parentBlockHash       : Hash32,
  parentBlockRoot       : Root,
  blockHash             : Hash32,
  prevRandao            : Bytes32,
  feeRecipient          : ExecutionAddress,
  gasLimit              : UInt64,
  builderIndex          : BuilderIndex,
  slot                  : Slot,
  value                 : Gwei,
  executionPayment      : Gwei,
  blobKzgCommitments    : SSZList KZGCommitment @@MAX_BLOB_COMMITMENTS_PER_BLOCK,
  executionRequestsRoot : Root

ssz_struct_for_presets SignedExecutionPayloadBid in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  message   : @%ExecutionPayloadBid,
  signature : BLSSignature

/-! The post-PTC-attestation envelope: the builder's actual
payload plus execution requests, linked back to the proposer's
beacon block. `payload` reuses Deneb's `ExecutionPayload` until
Gloas's `BlockAccessList` / `slot_number` additions are ported. -/
ssz_struct_for_presets ExecutionPayloadEnvelope in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  payload              : @%LeanEthCS.Forks.Deneb.ExecutionPayload,
  executionRequests    : ExecutionRequests,
  builderIndex         : BuilderIndex,
  beaconBlockRoot      : Root,
  parentBeaconBlockRoot : Root

ssz_struct_for_presets SignedExecutionPayloadEnvelope in LeanEthCS.Forks.Gloas
    for [minimal, mainnet] where
  message   : @%ExecutionPayloadEnvelope,
  signature : BLSSignature

end LeanEthCS.Forks.Gloas
