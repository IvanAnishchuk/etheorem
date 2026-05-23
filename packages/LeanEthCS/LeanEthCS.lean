import LeanEthCS.Primitives
import LeanEthCS.Forks.Phase0.BeaconBlockHeader
import LeanEthCS.Forks.Phase0.Containers
import LeanEthCS.Forks.Phase0.Attestations
import LeanEthCS.Forks.Phase0.Block
import LeanEthCS.Forks.Phase0.State
import LeanEthCS.Forks.Altair.Sync
import LeanEthCS.Forks.Altair.LightClient
import LeanEthCS.Forks.Altair.Block
import LeanEthCS.Forks.Altair.State
import LeanEthCS.Forks.Bellatrix.Execution
import LeanEthCS.Forks.Bellatrix.Block
import LeanEthCS.Forks.Bellatrix.State
import LeanEthCS.Forks.Capella.Withdrawal
import LeanEthCS.Forks.Capella.Execution
import LeanEthCS.Forks.Capella.LightClient
import LeanEthCS.Forks.Capella.Block
import LeanEthCS.Forks.Capella.State
import LeanEthCS.Forks.Deneb.Primitives
import LeanEthCS.Forks.Deneb.Execution
import LeanEthCS.Forks.Deneb.Block
import LeanEthCS.Forks.Deneb.State
import LeanEthCS.Forks.Deneb.Blob
import LeanEthCS.Forks.Deneb.LightClient
import LeanEthCS.Forks.Electra.PendingOperations
import LeanEthCS.Forks.Electra.Requests
import LeanEthCS.Forks.Electra.Attestation
import LeanEthCS.Forks.Electra.Block
import LeanEthCS.Forks.Electra.State
import LeanEthCS.Forks.Electra.LightClient
import LeanEthCS.Forks.Fulu.Primitives
import LeanEthCS.Forks.Fulu.DataColumn
import LeanEthCS.Forks.Fulu.Block
import LeanEthCS.Forks.Fulu.State
import LeanEthCS.Forks.Fulu.LightClient
import LeanEthCS.Forks.Gloas.Primitives
import LeanEthCS.Forks.Gloas.Builder
import LeanEthCS.Forks.Gloas.PayloadAttestation
import LeanEthCS.Forks.Gloas.Execution
import LeanEthCS.Forks.Gloas.Block
import LeanEthCS.Forks.Gloas.State
import LeanEthCS.Forks.Gloas.LightClient
import LeanEthCS.Preset
import LeanEthCS.PresetStruct

/-!
# LeanEthCS

The Ethereum Consensus Spec containers, expressed against the SSZ
type system from `SizzLean`. Importing this file pulls in every
fork's primitives, container definitions, and the preset-struct
macro used to stamp out minimal / mainnet variants.

Conformance tests (consensus-spec-tests `ssz_static`, cached-
update spec-shaped property tests) live in `LeanEthCS`;
build them with `lake build LeanEthCS`.
-/
