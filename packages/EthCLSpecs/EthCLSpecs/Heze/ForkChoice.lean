import EthCLSpecs.Heze.Transition
import EthCLSpecs.Gloas.ForkChoice
import EthCLSpecs.Heze.Committees
import EthCLLib.Spec.FiniteMap
import EthCLLib.Spec.Engine

/-!
# `EthCLSpecs.Heze.ForkChoice`: the ePBS node-based fork choice with EIP-7805 (FOCIL)

Heze inherits Gloas's whole ePBS node fork choice and adds the EIP-7805 inclusion-list layer
on top (`consensus-specs/specs/heze/fork-choice.md`). `ForkChoiceNode` / `LatestMessage` are
`inherit`ed unchanged; the `Store` is re-declared (a `forkstruct` rather than an `inherit`) to
carry the two `[New in Heze:EIP7805]` fields, `payloadInclusionListSatisfaction` and the folded-in
`inclusionListStore`. The spec keeps a separate process-lifetime `InclusionListStore`, but this
framework's pure `EStateM` fork choice threads one `Store`, so the inclusion-list store rides inside
it (see the `InclusionListStore` block below for the full rationale). Most handlers are
inherited verbatim; the FOCIL touch points are re-declared here:

* `get_forkchoice_store` seeds the two new store fields empty;
* `is_payload_inclusion_list_satisfied` / `record_payload_inclusion_list_satisfaction` /
  `get_inclusion_list_due_ms` / `is_inclusion_list_satisfied` are the new helpers;
* `should_extend_payload` gains the inclusion-list gate;
* `on_execution_payload_envelope` records satisfaction before storing the payload;
* `on_inclusion_list` is the new wire handler.

EIP-7805 also extends `PayloadAttributes` with `inclusion_list_transactions` and threads it through
`notify_forkchoice_updated` (`heze/fork-choice.md:65-104`). Both are the production-side Engine-API
surface a proposer drives to build its own payload, so they sit outside the modeled
state-transition and fork-choice scope and stay unmodeled here, the same boundary every fork keeps.
Only the consumption-side `is_inclusion_list_satisfied` is modeled, through the `[ExecutionEngine]`
seam that `record_payload_inclusion_list_satisfaction` calls to judge a revealed payload.

The `on_execution_payload_envelope` fork_choice vectors do drive the two overrides, but only the
empty-inclusion-list, always-satisfied path they share with Gloas; the FOCIL-specific behavior (the
discriminating satisfaction gate and `on_inclusion_list`) has no vector, so the pinned alpha.11 spec
is its oracle. Each override mirrors its Python branch-for-branch, and the `InclusionListStore`
`#guard`s below pin the inclusion-list store logic. The three node smart constructors and the `deriving` lines are
plain declarations in Gloas (not captured), so they are restated here.
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher
open EthCLSpecs.Fulu

namespace EthCLSpecs.Heze

inherit ForkChoiceNode
deriving instance BEq, Inhabited for ForkChoiceNode

inherit LatestMessage
deriving instance Inhabited for LatestMessage

/-- `InclusionListStore` (`consensus-specs/specs/heze/inclusion-list.md:28-38`): the
fork-choice node's view of the inclusion lists it has seen. `inclusionLists` files each
stored `InclusionList` under its committee root then its own hash-tree root
(`DefaultDict[Root, Dict[Root, InclusionList]]`); `inclusionListTimeliness` records, per
stored-list root, whether it arrived before `INCLUSION_LIST_DUE_BPS`; `equivocators` is the
per-committee set of validator indices caught publishing two different lists. A `forkstruct`
rather than a bare `structure`, so a later fork can `inherit` it, and so it carries the auto
`[Preset]` / `[HasherTag]` uniformly with the containers it nests.

Declared here, above the fork-choice `Store` that carries it as a field, rather than in a
separate feature file: the spec keeps `InclusionListStore` as a process-lifetime singleton reached
through `get_inclusion_list_store()`, but this framework's fork choice is a pure `EStateM` over one
`Store`, so the store is modeled as a field of that `Store`. It is fork-choice state, so it lives
with fork choice, next to the handlers that drive it. -/
forkstruct InclusionListStore (map : MapKind) [HasherTag] where
  inclusionLists          : map Root (map Root InclusionList)
  inclusionListTimeliness : map Root Bool
  equivocators            : map Root (Array ValidatorIndex)

section

variable [Preset] [HasherTag] [Config] {map : MapKind} [FcMap map]

/-- The empty `InclusionListStore`: no stored lists, no timeliness, no equivocators. The seed
`get_forkchoice_store` plants (`consensus-specs/specs/heze/fork-choice.md:165`) and the base
every pin builds from, so the all-empty literal lives in one place. -/
def InclusionListStore.empty : InclusionListStore map :=
  { inclusionLists := FcMap.empty, inclusionListTimeliness := FcMap.empty, equivocators := FcMap.empty }

/-- The inner comprehension of `get_inclusion_list_transactions`
(`consensus-specs/specs/heze/inclusion-list.md:105-114`): over the inclusion lists stored for
one committee key, keep those from non-equivocating validators (and, when `onlyTimely`, only
the timely ones), gather their transactions, and deduplicate. Factored out of the accessor so
the equivocator / timeliness / dedup logic is unit-checkable without building a `BeaconState`
for the committee key (the `cyclicSample` pattern). One pass with `FcMap.fold` over the stored
map, which hands each `(ilRoot, il)` straight to the step (no second `lookup`, no dead `none`
branch). `timeliness[ilRoot]` is a plain dict read in the spec (every stored list has a
timeliness entry, written together in `process_inclusion_list`); the structurally-present key
reads through `.getD false`, the default never reached on the spec path. The dedup is the house
`arrayUnion #[] …` first-occurrence union: the spec's `list(set(transactions))` keeps each
transaction once and calls the order irrelevant, so a deterministic first-occurrence
representative lets the result be pinned by `#guard`. -/
private def collectInclusionListTransactions (inclusionLists : map Root InclusionList)
    (equivocators : Array ValidatorIndex) (timeliness : map Root Bool) (onlyTimely : Bool) :
    Array Transaction :=
  let collected : Array Transaction :=
    FcMap.fold (fun acc ilRoot il =>
      let timely := FcMap.lookupD timeliness ilRoot
      if !equivocators.contains il.validatorIndex && (!onlyTimely || timely) then
        acc ++ il.transactions.toArray
      else acc) #[] inclusionLists
  arrayUnion #[] collected

/-- `process_inclusion_list(store, inclusion_list, is_timely)`
(`consensus-specs/specs/heze/inclusion-list.md:57-82`): file a newly-received inclusion list,
or record an equivocation. Pure here (returns the updated `InclusionListStore`); the spec
mutates in place. The three branches mirror the Python:

* (A) the list is from a known equivocator for this committee (`validator_index in
  store.equivocators[key]`) → ignore it, return the store unchanged.
* (B) we already hold a list from this validator for this committee → if the new list differs
  from the stored one, add the validator to `equivocators[key]`; either way we have processed
  it, so return (storing nothing new). At most one stored list per validator exists (a list is
  filed only on branch (C), reached only when none matches), so the single `find?` match is
  exactly the Python loop's first-and-only hit. The equivocator `push` is guarded by branch
  (A) above, so it never duplicates.
* (C) otherwise → store the list under its `hash_tree_root` and record its timeliness.

`key` is the list's `inclusion_list_committee_root` (a field, no rehash). -/
forkdef processInclusionList (store : InclusionListStore map) (inclusionList : InclusionList)
    (isTimely : Bool) : InclusionListStore map :=
  let key := inclusionList.inclusionListCommitteeRoot
  let equivs := FcMap.lookupD store.equivocators key
  -- (A) ignore inclusion lists from known equivocators for this committee
  if equivs.contains inclusionList.validatorIndex then store
  else
    let stored := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
    match (FcMap.values stored).find? (fun il => il.validatorIndex == inclusionList.validatorIndex) with
    -- (B) already hold a list from this validator: equivocate iff it differs, then stop
    | some existing =>
      if existing == inclusionList then store
      else
        { store with
            equivocators := FcMap.insert store.equivocators key (equivs.push inclusionList.validatorIndex) }
    -- (C) first list from this validator: store it and its timeliness
    | none =>
      let inclusionListRoot := htr inclusionList
      let stored' := FcMap.insert stored inclusionListRoot inclusionList
      { store with
          inclusionLists := FcMap.insert store.inclusionLists key stored',
          inclusionListTimeliness := FcMap.insert store.inclusionListTimeliness inclusionListRoot isTimely }

/-- `get_inclusion_list_transactions(store, state, slot, only_timely=True)`
(`consensus-specs/specs/heze/inclusion-list.md:95-114`): the unique transactions from every
valid, non-equivocating inclusion list whose committee root matches the one `state`/`slot`
compute, optionally restricted to lists received before `INCLUSION_LIST_DUE_BPS`. Mirrors the
Python: derive the committee, key it by `hash_tree_root`, read the `defaultdict` entries for
that key, then run the comprehension (here `collectInclusionListTransactions`). Returns an
`Array` for the spec's `Sequence[Transaction]`; the dedup leaves order unspecified, as the
spec notes. -/
forkdef getInclusionListTransactions (store : InclusionListStore map) (state : State)
    (slot : Slot) (onlyTimely : Bool := true) : Array Transaction :=
  let committee := getInclusionListCommittee state slot
  let key := htr committee
  let inclusionLists := (FcMap.lookup store.inclusionLists key).getD FcMap.empty
  let equivocators := FcMap.lookupD store.equivocators key
  collectInclusionListTransactions inclusionLists equivocators store.inclusionListTimeliness onlyTimely

end

/-- The Heze fork-choice store: the Gloas store plus the EIP-7805 fields. Re-declared as a
`forkstruct` rather than an `inherit Store`, so the two `[New in Heze:EIP7805]` fields can be added.
`payloadInclusionListSatisfaction` tracks, per beacon-block root, whether the revealed payload
satisfied the inclusion-list constraints (`consensus-specs/specs/heze/fork-choice.md:134`);
`inclusionListStore` folds in the spec's separate `InclusionListStore` (see the module docstring).
The seventeen Gloas fields are restated verbatim. -/
forkstruct Store (map : MapKind) [HasherTag] where
  time                          : UInt64
  genesisTime                   : UInt64
  justifiedCheckpoint           : Checkpoint
  finalizedCheckpoint           : Checkpoint
  unrealizedJustifiedCheckpoint : Checkpoint
  unrealizedFinalizedCheckpoint : Checkpoint
  proposerBoostRoot             : Root
  equivocatingIndices           : Array ValidatorIndex
  blocks                        : map Root BeaconBlock
  blockStates                   : map Root State
  blockTimeliness               : map Root (Array Bool)
  checkpointStates              : map Checkpoint State
  latestMessages                : map ValidatorIndex LatestMessage
  unrealizedJustifications      : map Root Checkpoint
  payloads                      : map Root ExecutionPayloadEnvelope
  payloadTimelinessVote         : map Root (Array (Option Bool))
  payloadDataAvailabilityVote   : map Root (Array (Option Bool))
  -- [New in Heze:EIP7805] (consensus-specs/specs/heze/fork-choice.md:134)
  payloadInclusionListSatisfaction : map Root Bool
  -- [New in Heze:EIP7805] the spec's standalone `InclusionListStore`, folded in here as a field
  inclusionListStore            : InclusionListStore map

fork_choice_section map

/-- A PENDING node at `root`: the undecided block, before either payload realisation is
committed. -/
def ForkChoiceNode.pending (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusPending }

/-- An EMPTY node at `root`: the realisation in which the block's payload is absent. -/
def ForkChoiceNode.empty (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusEmpty }

/-- A FULL node at `root`: the realisation in which the block's payload is present. -/
def ForkChoiceNode.full (root : Root) : ForkChoiceNode :=
  { root := root, payloadStatus := Const.payloadStatusFull }

inherit fcZeroRoot
inherit getSlotsSinceGenesis
inherit getCurrentSlot
inherit getCurrentStoreEpoch
inherit timeIntoSlotMs
inherit bpsDeadlineMs
inherit getParentPayloadStatus
inherit isParentNodeFull
inherit getAncestor
inherit isAncestor
inherit getCheckpointBlock
inherit getSupportedNode
inherit getDependentRoot
inherit isPayloadVerified
inherit voteCount
inherit payloadTimeliness
inherit payloadDataAvailability
inherit isPreviousSlotPayloadDecision

/-- `is_payload_inclusion_list_satisfied(store, root)`
(`consensus-specs/specs/heze/fork-choice.md:199-212`): whether the payload for `root` satisfied
the inclusion-list constraints and is locally available. The spec opens with `assert root in
store.payload_inclusion_list_satisfaction`; a pure `Bool` predicate cannot throw, so a missing
key reads as `false` through `lookupD`, the same default-on-miss the sibling `payloadTimeliness`
uses. That default sits off the spec path thanks to the `payloads`/satisfaction co-write; the
INVARIANT note in `onExecutionPayloadEnvelope` is the canonical statement. -/
forkdef isPayloadInclusionListSatisfied (store : Store map) (root : Root) : Bool :=
  isPayloadVerified store root && FcMap.lookupD store.payloadInclusionListSatisfaction root

/-- `should_extend_payload(store, root)` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:221-236`): the Gloas body with the one new
inclusion-list gate. After the `is_payload_verified` check, a payload that fails the
inclusion-list constraints is not extended (`fork-choice.md:226`). The rest is Gloas verbatim.
-/
forkdef shouldExtendPayload (store : Store map) (root : Root) : Bool :=
  if !isPayloadVerified store root then false
  -- [New in Heze:EIP7805] do not extend a payload that fails the inclusion-list constraints
  else if !isPayloadInclusionListSatisfied store root then false
  else
    let proposerRoot := store.proposerBoostRoot
    let payloadIsTimely := payloadTimeliness store root true
    let payloadDataIsAvailable := payloadDataAvailability store root true
    (payloadIsTimely && payloadDataIsAvailable)
      || proposerRoot == fcZeroRoot
      || (match FcMap.lookup store.blocks proposerRoot with
          | some pb => pb.parentRoot != root || isParentNodeFull store pb
          | none    => true)

inherit getPayloadStatusTiebreaker
inherit committeeWeight
inherit calculateCommitteeFraction
inherit getProposerScore
inherit getAttestationScore
inherit isHeadWeak
inherit isParentStrong
inherit shouldApplyProposerBoost
inherit getWeight
inherit getVotingSource
inherit filterBlockTree
inherit getFilteredBlockTree
inherit getNodeChildren
inherit getHead
inherit updateCheckpoints
inherit updateUnrealizedCheckpoints
inherit computePulledUpTip
inherit onTickPerSlot
inherit advanceStoreTime
inherit onTick
inherit recordBlockTimeliness
inherit updateProposerBoostRoot
inherit recordPtcVotes
inherit notifyPtcMessages
inherit onBlock
inherit computeTimeAtSlot
inherit verifyExecutionPayloadEnvelopeSignature
inherit verifyExecutionPayloadEnvelope

-- The `is_inclusion_list_satisfied` verdict comes from an external EL over the Engine API
-- (`consensus-specs/specs/heze/fork-choice.md:54-62`), so it enters through the framework's
-- `[ExecutionEngine]` seam (`EthCLLib.Spec.Engine`, the canonical home of the optimistic-mock
-- rationale), instantiated at Heze's payload / transaction types.
variable [ExecutionEngine ExecutionPayload Transaction]

/-- `is_inclusion_list_satisfied(execution_payload, inclusion_list_transactions)`
(`consensus-specs/specs/heze/fork-choice.md:54-62`): the `ExecutionEngine` predicate deciding
whether a payload includes the required inclusion-list transactions. Its verdict is
EL-implementation-defined (the Engine API answers it against an external EL), so it reads the
`[ExecutionEngine]` seam rather than a fixed value; the default and the trust boundary are
documented on `EthCLLib.Spec.ExecutionEngine`. -/
forkdef isInclusionListSatisfied (payload : ExecutionPayload) (ilTxs : Array Transaction) : Bool :=
  ExecutionEngine.isInclusionListSatisfied payload ilTxs

/-- `record_payload_inclusion_list_satisfaction(store, state, root, payload, execution_engine)`
(`consensus-specs/specs/heze/fork-choice.md:180-193`): record whether `payload` satisfies the
inclusion-list constraints for `root`. Pure here (returns the updated store); the spec mutates
in place. `get_inclusion_list_store()` is `store.inclusionListStore`; the required
transactions are read for the previous slot (`state.slot - 1`) at the default `only_timely =
True`, and the EL verdict comes from `isInclusionListSatisfied`, which reads the
`[ExecutionEngine]` seam (the spec's `execution_engine` argument, modeled injectably). -/
forkdef recordPayloadInclusionListSatisfaction (store : Store map) (state : State) (root : Root)
    (payload : ExecutionPayload) : Store map :=
  -- The spec reads `Slot(state.slot - 1)`, which assumes `state.slot ≥ 1` (a genesis/slot-0 state
  -- never reaches a payload envelope). Guard the `UInt64` underflow explicitly: at slot 0 there is
  -- no previous slot, so no inclusion-list transactions are required.
  let stateSlot := sszGet state slot
  let ilTxs := if stateSlot == 0 then #[]
               else getInclusionListTransactions store.inclusionListStore state (stateSlot - 1)
  let satisfied := isInclusionListSatisfied payload ilTxs
  { store with
      payloadInclusionListSatisfaction := FcMap.insert store.payloadInclusionListSatisfaction root satisfied }

/-- `on_execution_payload_envelope` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:273-300`): the Gloas body with one added step,
`record_payload_inclusion_list_satisfaction` is called on the verified envelope *before* the
payload is stored (`fork-choice.md:295`), so `should_extend_payload` can later read the
recorded verdict. `state` is the pre-verify `block_states[root]`, as in the spec; the warm
state from `verify_execution_payload_envelope` is kept only for `blockStates`. -/
forkdef onExecutionPayloadEnvelope (signedEnv : SignedExecutionPayloadEnvelope) : StoreTransition Unit := do
  let store ← get
  let envelope := signedEnv.message
  let state ← FcMap.getOrThrow store.blockStates envelope.beaconBlockRoot

  match verifyExecutionPayloadEnvelope state signedEnv with
  | .error e => throw e
  | .ok warm =>
    -- [New in Heze:EIP7805] record whether the payload satisfies the inclusion-list constraints
    let store := recordPayloadInclusionListSatisfaction store state envelope.beaconBlockRoot envelope.payload
    -- INVARIANT: `payloads[root]` and `payloadInclusionListSatisfaction[root]` are co-written here
    -- (the satisfaction key via `recordPayloadInclusionListSatisfaction` just above). Keep them
    -- co-written: `isPayloadInclusionListSatisfied`'s default-false-on-miss is sound only because a
    -- verified `root` (present in `payloads`) always carries a satisfaction entry.
    set { store with
      blockStates := FcMap.insert store.blockStates envelope.beaconBlockRoot warm,
      payloads := FcMap.insert store.payloads envelope.beaconBlockRoot envelope }

inherit onPayloadAttestationMessage
inherit storeTargetCheckpointState
inherit validateOnAttestation
inherit updateLatestMessages
inherit onAttestation
inherit onAttesterSlashing

/-- `get_forkchoice_store(anchor_state, anchor_block)` (Heze override,
`consensus-specs/specs/heze/fork-choice.md:140-166`): the Gloas anchor store with the two
`[New in Heze:EIP7805]` fields seeded empty, `payloadInclusionListSatisfaction` as an empty
map and `inclusionListStore` as the empty `InclusionListStore` (`fork-choice.md:165`, decision
A). The rest is Gloas verbatim. -/
forkdef getForkchoiceStore (anchorState : State) (anchorBlock : BeaconBlock) : Store map :=
  let anchorRoot := htr anchorBlock
  let epoch := currentEpochOf anchorState
  let cp : Checkpoint := { epoch := epoch, root := anchorRoot }

  { time := (sszGet anchorState genesisTime) + Const.slotDurationMs * (sszGet anchorState slot) / 1000
    genesisTime := sszGet anchorState genesisTime
    justifiedCheckpoint := cp, finalizedCheckpoint := cp
    unrealizedJustifiedCheckpoint := cp, unrealizedFinalizedCheckpoint := cp
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.insert FcMap.empty anchorRoot anchorBlock
    blockStates := FcMap.insert FcMap.empty anchorRoot anchorState
    blockTimeliness := FcMap.insert FcMap.empty anchorRoot #[true, true]
    checkpointStates := FcMap.insert FcMap.empty cp anchorState
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.insert FcMap.empty anchorRoot cp
    payloads := FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    -- [New in Heze:EIP7805] seeded empty in lockstep with `payloads` above (the co-write
    -- INVARIANT in `onExecutionPayloadEnvelope`).
    payloadInclusionListSatisfaction := FcMap.empty
    inclusionListStore := InclusionListStore.empty }

/-- `get_inclusion_list_due_ms()` (`consensus-specs/specs/heze/fork-choice.md:242-243`):
`get_slot_component_duration_ms(INCLUSION_LIST_DUE_BPS)`. `bpsDeadlineMs` (inherited from Gloas)
IS `get_slot_component_duration_ms`. A fork-choice deadline helper leaning on that inherited
fork-choice function, so it lives here with the rest of the fork-choice layer. -/
forkdef getInclusionListDueMs : UInt64 := bpsDeadlineMs Const.inclusionListDueBps

/-- `on_inclusion_list(store, signed_inclusion_list)` (the new wire handler,
`consensus-specs/specs/heze/fork-choice.md:256-267`): on receiving an inclusion list, judge its
timeliness against `INCLUSION_LIST_DUE_BPS` and hand it to `process_inclusion_list`. The spec's
`seconds_to_milliseconds(store.time - store.genesis_time) % SLOT_DURATION_MS` is exactly the
inherited `timeIntoSlotMs`. `process_inclusion_list` is total, so the spec's "an invalid call
MUST NOT modify the store" is automatic here. The inclusion-list store rides inside `Store`, so
`get_inclusion_list_store()` is `store.inclusionListStore`. -/
forkdef onInclusionList (signed : SignedInclusionList) : StoreTransition Unit := do
  let store ← get
  let inclusionList := signed.message
  let isTimely := timeIntoSlotMs store < getInclusionListDueMs
  set { store with
    inclusionListStore := processInclusionList store.inclusionListStore inclusionList isTimely }

end

/-! ### Build-enforced pin (vectorless): the inclusion-list satisfaction gate

`is_payload_inclusion_list_satisfied` is the FOCIL fork-choice gate `should_extend_payload` reads
to refuse a payload that failed its inclusion-list constraints. No conformance vector exercises it,
and the no-regression sweep only runs the optimistic `is_inclusion_list_satisfied = true` mock, so
the discriminating `false` branch is otherwise dead. This pin drives the predicate on a minimal
`Store` directly, fixing its outcomes by hand: verified + recorded-`false` ⇒ `false` (the gate's
whole point), verified + recorded-`true` ⇒ `true`, unverified ⇒ `false` even with the bit recorded
`true` (the `is_payload_verified` membership gate dominates), and verified-but-absent ⇒ `false`
through the `lookupD` default (off the spec path; the co-write INVARIANT in
`onExecutionPayloadEnvelope`). Hash-free (`is_payload_verified` is a `payloads`
membership test, no `htr`), so kernel `#guard`. The pin reaches the predicate end-to-end, including
the `isPayloadVerified` composition; it fixes the recorded bit by hand rather than through the EL,
so the `isInclusionListSatisfied` verdict is out of its reach. That verdict is the
`[ExecutionEngine]` seam's job: `pinRecordRefuted` below drives its refuting branch through the
record path into this gate. -/

private def pinPilsRoot : Root := Vector.replicate 32 9

/-- A minimal Heze `Store` exercising `isPayloadInclusionListSatisfied` at `pinPilsRoot`.
`payloadPresent` controls whether `root ∈ payloads` (the `is_payload_verified` gate); `recorded` is
the optional `payloadInclusionListSatisfaction[root]` entry. Every other field is empty/zero
(`FcMap.empty`, default checkpoints, `fcZeroRoot`), mirroring the `getForkchoiceStore` literal. The
`payloads` value is never read (the predicate tests membership only), so a `default` envelope
serves. The `letI`s fix the preset / hasher so the anonymous `Store` constructor synthesizes them. -/
private def pinPilsStore (payloadPresent : Bool) (recorded : Option Bool) :
    @Store minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { time := 0, genesisTime := 0
    justifiedCheckpoint := default, finalizedCheckpoint := default
    unrealizedJustifiedCheckpoint := default, unrealizedFinalizedCheckpoint := default
    proposerBoostRoot := fcZeroRoot
    equivocatingIndices := #[]
    blocks := FcMap.empty
    blockStates := FcMap.empty
    blockTimeliness := FcMap.empty
    checkpointStates := FcMap.empty
    latestMessages := FcMap.empty
    unrealizedJustifications := FcMap.empty
    payloads := if payloadPresent then FcMap.insert FcMap.empty pinPilsRoot default else FcMap.empty
    payloadTimelinessVote := FcMap.empty
    payloadDataAvailabilityVote := FcMap.empty
    payloadInclusionListSatisfaction :=
      match recorded with
      | some b => FcMap.insert FcMap.empty pinPilsRoot b
      | none   => FcMap.empty
    inclusionListStore := InclusionListStore.empty }

/-- The predicate's verdict on `pinPilsStore payloadPresent recorded`. The `letI`s re-supply the
preset / hasher the `forkdef` parameters want (Lean re-synthesizes them rather than reading the
store's fixed type), the same pattern the `InclusionListStore` pins in this file use. -/
private def pinPils (payloadPresent : Bool) (recorded : Option Bool) : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  isPayloadInclusionListSatisfied (pinPilsStore payloadPresent recorded) pinPilsRoot

-- verified + recorded `false` ⇒ `false` (do not extend this payload).
#guard pinPils true (some false) = false
-- verified + recorded `true` ⇒ `true`.
#guard pinPils true (some true) = true
-- unverified (root ∉ payloads) ⇒ `false`, even with the satisfaction bit recorded `true`.
#guard pinPils false (some true) = false
-- verified but no recorded entry ⇒ `false` via the `lookupD` default (off the spec path).
#guard pinPils true none = false

/-! ### Build-enforced pins (vectorless): the FOCIL fork-choice helpers

`get_inclusion_list_due_ms`, `record_payload_inclusion_list_satisfaction`, and `on_inclusion_list`
ship no conformance vector either. These drive them end-to-end so a future edit can't regress them
silently: the deadline constant, the recorded EL verdict, and the timeliness bit `on_inclusion_list`
threads into `process_inclusion_list`. -/

/-- `get_inclusion_list_due_ms = INCLUSION_LIST_DUE_BPS * SLOT_DURATION_MS // BASIS_POINTS`. Under
the minimal config that is `6667 * 6000 / 10000 = 4000` (truncating divide), pinning both the
`INCLUSION_LIST_DUE_BPS = 6667` constant and the inherited `bpsDeadlineMs` composition. Arithmetic
only (no hash), so kernel `#guard`. -/
private def pinIlDueMs : UInt64 :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  getInclusionListDueMs
#guard pinIlDueMs = 4000

/-- `record_payload_inclusion_list_satisfaction` records the EL verdict at `root`. With the
optimistic `isInclusionListSatisfied = true` mock (the `ExecutionEngine` default) it writes
`true`; the slot-0 `state` drives the underflow-guard branch (no previous slot ⇒ empty required
set, `getInclusionListTransactions` never reached), though the pinned value alone does not
discriminate the guard: with an empty store and the optimistic oracle the verdict is `true`
either way. `state` is a `FastBox` of the default minimal `BeaconState`, the boxed `State` the
forkdef wants (`State = SSZ.Box HasherTag.H BeaconState`); `FastBox` is FFI-backed, so this is a
`native_decide` `example`
(`Lean.ofReduceBool`). -/
private def pinRecordSatisfied : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Heze.BeaconState minimal)
  let after := recordPayloadInclusionListSatisfaction (pinPilsStore false none) state pinPilsRoot
    (default : @EthCLSpecs.Heze.ExecutionPayload minimal)
  FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot
example : pinRecordSatisfied = some true := by native_decide

/-- The discriminating counterpart to `pinRecordSatisfied`: the same record path, now under a
*refuting* `[ExecutionEngine]`. A local `letI` answering `false` overrides the global optimistic
instance, the whole reason the seam exists. So the record path writes `false` at a *verified* `root`
and `isPayloadInclusionListSatisfied` then refuses to extend it. This drives the
`isInclusionListSatisfied = false` branch the optimistic default and every conformance vector leave
dead, end-to-end: oracle → recorded verdict → gate. `pinPilsStore true none` puts `root ∈ payloads`
so the membership check passes and the recorded bit is what decides. `State` is FFI-backed
(`FastBox`), so `native_decide`. -/
private def pinRecordRefuted : Option Bool × Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : ExecutionEngine (@EthCLSpecs.Heze.ExecutionPayload minimal) Transaction :=
    { isInclusionListSatisfied := fun _ _ => false }
  let state : State := SSZ.FastBox (default : @EthCLSpecs.Heze.BeaconState minimal)
  let after := recordPayloadInclusionListSatisfaction (pinPilsStore true none) state pinPilsRoot
    (default : @EthCLSpecs.Heze.ExecutionPayload minimal)
  (FcMap.lookup after.payloadInclusionListSatisfaction pinPilsRoot,
   isPayloadInclusionListSatisfied after pinPilsRoot)
-- refuting oracle ⇒ recorded `false`, and the gate rejects the verified payload.
example : pinRecordRefuted = (some false, false) := by native_decide

/-- `on_inclusion_list` threads the slot-timeliness bit into `process_inclusion_list`: a list
received before `INCLUSION_LIST_DUE_BPS` is filed timely, one at/after the deadline untimely. Runs
the handler end-to-end on a minimal store whose `time` puts `timeIntoSlotMs` below vs at the
`getInclusionListDueMs = 4000` deadline, then reads the stored timeliness bit back at `htr il`.
`process_inclusion_list` files the default list on branch (C), computing `htr` (FFI `Sha256`), so
this is a `native_decide` `example` (`Lean.ofReduceBool`). -/
private def pinOnIlTimely (time : UInt64) : Option Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let signed : @SignedInclusionList minimal := default
  match runOn { pinPilsStore false none with time := time }
      (onInclusionList (map := treeMap) signed : EStateM StoreTransitionError (Store treeMap) Unit) with
  | .ok after => FcMap.lookup after.inclusionListStore.inclusionListTimeliness (htr signed.message)
  | .error _  => none
-- time 0: timeIntoSlotMs = 0 < 4000 ⇒ timely.
example : pinOnIlTimely 0 = some true := by native_decide
-- time 4: timeIntoSlotMs = 4000, not < 4000 ⇒ untimely.
example : pinOnIlTimely 4 = some false := by native_decide

/-! ### Build-enforced pins for the inclusion-list store (vectorless)

FOCIL has no conformance vector, so these pin `process_inclusion_list`'s three branches and
`get_inclusion_list_transactions`'s comprehension to hand-derived outcomes. They build a small
`InclusionListStore treeMap` (deterministic key order) under the minimal preset and the FFI
hasher. The branch-(A)/(B) pins and every `collectInclusionListTransactions` pin are
hash-free, so kernel `#guard`; the branch-(C) pin computes `htr` (FFI `Sha256`), so it is a
`native_decide` `example` (`Lean.ofReduceBool`), per the project's hash-tactic rule. -/

private def pinKey : Root := Vector.replicate 32 7
private def pinDummyRoot : Root := Vector.replicate 32 1
private def pinAltRoot : Root := Vector.replicate 32 2

/-- A transaction holding the single byte `b` (enough to make two transactions compare
unequal for the dedup pins). -/
private def pinTx (b : UInt8) : Transaction := sszOfArray #[b]

/-- An inclusion list from validator `v` over committee `pinKey`, carrying `txs`. The `letI`
fixes the preset so the anonymous constructor can synthesize it (a return-type annotation alone
does not flow into instance resolution for `{ … }`). -/
private def pinIL (v : ValidatorIndex) (txs : Array Transaction) : @InclusionList minimal :=
  letI : Preset := minimal
  { slot := 0, validatorIndex := v, inclusionListCommitteeRoot := pinKey, transactions := sszOfArray txs }

/-- Number of inclusion lists stored under `pinKey`. The `letI`s supply the store's preset /
hasher for the field projection (Lean re-synthesizes them rather than reading the argument's
fixed type). -/
private def pinNumStored (s : @InclusionListStore minimal treeMap fastHasherTag) : Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  ((FcMap.lookup s.inclusionLists pinKey).getD FcMap.empty |> FcMap.keys).length
/-- The equivocator set recorded under `pinKey`. -/
private def pinEquivs (s : @InclusionListStore minimal treeMap fastHasherTag) : Array ValidatorIndex :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  FcMap.lookupD s.equivocators pinKey

/-- A store already holding one inclusion list from validator 5, filed under an arbitrary root
(branch (B) never rehashes the stored list, so the key is free). Shared by the two branch-(B)
pins. -/
private def pinStoreB : @InclusionListStore minimal treeMap fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  { inclusionLists := FcMap.insert FcMap.empty pinKey (FcMap.insert FcMap.empty pinDummyRoot (pinIL 5 #[pinTx 0xAA])),
    inclusionListTimeliness := FcMap.insert FcMap.empty pinDummyRoot true,
    equivocators := FcMap.empty }

-- Branch (A): a list from a validator already in `equivocators[key]` is ignored; nothing is
-- stored and the equivocator set is untouched. Hash-free, so kernel `#guard`. Returns
-- (stored count, equivocator count); expected (0, 1).
private def pinResA : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store : InclusionListStore treeMap :=
    { InclusionListStore.empty with equivocators := FcMap.insert FcMap.empty pinKey #[5] }
  let after := processInclusionList store (pinIL 5 #[pinTx 0xAA]) true
  (pinNumStored after, (pinEquivs after).size)
#guard pinResA = (0, 1)

-- Branch (B), conflict: a second, differing list from validator 5 adds 5 to `equivocators[key]`
-- and stores nothing new. Returns (equivocators, stored count); expected (#[5], 1).
private def pinResBConflict : Array ValidatorIndex × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinIL 5 #[pinTx 0xBB]) true
  (pinEquivs after, pinNumStored after)
#guard pinResBConflict = (#[5], 1)

-- Branch (B), match: re-receiving the *same* list is a no-op. Returns (equivocator count,
-- stored count); expected (0, 1).
private def pinResBMatch : Nat × Nat :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let after := processInclusionList pinStoreB (pinIL 5 #[pinTx 0xAA]) true
  ((pinEquivs after).size, pinNumStored after)
#guard pinResBMatch = (0, 1)

-- Branch (C): the first list from a validator is stored (one entry under `key`) with its
-- timeliness recorded under `htr inclusion_list`. Reads the bit back at the actual `htr il` key
-- (not just its presence), so a flipped `insert … (!isTimely)` fails; the stored-count half pins
-- that branch (C) filed exactly one list. Computes `htr` (FFI `Sha256`), so `native_decide`
-- `example`s. Returns (stored count, timeliness at `htr il`); expected (1, some isTimely).
private def pinResC (isTimely : Bool) : Nat × Option Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let store : InclusionListStore treeMap := InclusionListStore.empty
  let il := pinIL 5 #[pinTx 0xAA]
  let after := processInclusionList store il isTimely
  (pinNumStored after, FcMap.lookup after.inclusionListTimeliness (htr il))
example : pinResC true = (1, some true) := by native_decide
example : pinResC false = (1, some false) := by native_decide

-- `collectInclusionListTransactions` (the `get_inclusion_list_transactions` comprehension).
-- Two stored lists: validator 5 → [0xAA], validator 6 → [0xAA, 0xBB], timeliness 5=true /
-- 6=false. Pins worked out by hand from the comprehension. All hash-free, kernel `#guard`.
private def pinLists : treeMap Root (@InclusionList minimal) :=
  FcMap.insert (FcMap.insert FcMap.empty pinDummyRoot (pinIL 5 #[pinTx 0xAA]))
    pinAltRoot (pinIL 6 #[pinTx 0xAA, pinTx 0xBB])
private def pinTimeliness : treeMap Root Bool :=
  FcMap.insert (FcMap.insert FcMap.empty pinDummyRoot true) pinAltRoot false

/-- Run the comprehension over `pinLists` / `pinTimeliness` under the minimal preset, so the
hash-free `#guard`s below need no ambient instance. -/
private def pinCollect (equiv : Array ValidatorIndex) (onlyTimely : Bool) : Array Transaction :=
  letI : Preset := minimal
  collectInclusionListTransactions pinLists equiv pinTimeliness onlyTimely

-- No equivocators, timeliness ignored: union of {0xAA} and {0xAA, 0xBB}, deduped to two.
#guard (pinCollect #[] false).size = 2
#guard (pinCollect #[] false).contains (pinTx 0xAA)
#guard (pinCollect #[] false).contains (pinTx 0xBB)
-- only_timely drops validator 6's untimely list, leaving just {0xAA}.
#guard (pinCollect #[] true).size = 1
#guard (pinCollect #[] true).contains (pinTx 0xAA)
-- Equivocator 6 is filtered out regardless of timeliness, leaving just {0xAA}.
#guard (pinCollect #[6] false).size = 1
#guard (pinCollect #[6] false).contains (pinTx 0xAA)

end EthCLSpecs.Heze
