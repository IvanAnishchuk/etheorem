#!/usr/bin/env python3
"""Generate the LeanEthCS CLI dispatch table + per-fork `Inherited.lean`
re-export modules.

## What this script writes

1. **Per-fork `Inherited.lean`** (Altair through Fulu) — explicit
   `abbrev` declarations that re-bind names from earlier forks into the
   current fork's namespace. After these files are in place,
   `LeanEthCS.Forks.<Fork>.<Container>` resolves uniformly for every
   container the fork supports — no caller needs to know whether the
   type was originally defined in Phase 0, Altair, Bellatrix, ... or in
   the fork itself. Each Inherited.lean groups its abbrevs under
   `/-! ### Inherited from <SourceFork> -/` headings so the file is
   self-describing about exactly what the fork pulls in and from where.

2. **The dispatch block** in `packages/LeanEthCS/LeanEthCS/Cli/Main.lean`,
   spliced between the markers

       -- BEGIN AUTO-GENERATED DISPATCH --
       -- END AUTO-GENERATED DISPATCH --

   Every dispatch arm uses `LeanEthCS.Forks.<thisFork>.<Suffix>` — fully
   qualified, no `open` needed, no per-arm awareness of inheritance.
   The single source of truth for inheritance is the `*_OWN` lists
   below + the `compute_table` walk.

## Source-of-truth lists

For each fork, two ordered lists declare what that fork *itself*
defines (or redefines, shadowing an earlier fork's same-named type):

* `<FORK>_INV_OWN` — preset-invariant containers (one dispatch arm).
* `<FORK>_VAR_OWN` — preset-variant containers (two arms,
  `.Minimal` / `.Mainnet`).

Inheritance is then computed by `compute_table(fork)`:
predecessor's table minus any name this fork redefines, plus this
fork's own. Phase 0 starts the chain with no predecessor.

Regenerate via:

    just gen-cli-dispatch
"""

import sys
from collections import OrderedDict
from pathlib import Path

# ─────────────────────────────────────────────────────────────────────
# Source of truth — what each fork defines / redefines
# ─────────────────────────────────────────────────────────────────────

PHASE0_INV_OWN = [
    "BeaconBlockHeader", "Validator", "Fork", "Checkpoint", "AttestationData",
    "DepositMessage", "DepositData", "VoluntaryExit", "SignedVoluntaryExit",
    "SignedBeaconBlockHeader", "ProposerSlashing", "Eth1Data", "ForkData",
    "SigningData", "Eth1Block", "IndexedAttestation", "PendingAttestation",
    "Attestation", "AttesterSlashing", "Deposit", "AggregateAndProof",
    "SignedAggregateAndProof",
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock",
]
PHASE0_VAR_OWN = ["HistoricalBatch", "BeaconState"]

ALTAIR_INV_OWN = [
    "SyncCommitteeMessage", "SyncAggregatorSelectionData", "LightClientHeader",
]
ALTAIR_VAR_OWN = [
    "SyncAggregate", "SyncCommittee", "SyncCommitteeContribution",
    "ContributionAndProof", "SignedContributionAndProof",
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock", "BeaconState",
    "LightClientBootstrap", "LightClientUpdate",
    "LightClientFinalityUpdate", "LightClientOptimisticUpdate",
]

BELLATRIX_INV_OWN = ["ExecutionPayload", "ExecutionPayloadHeader", "PowBlock"]
BELLATRIX_VAR_OWN = [
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock", "BeaconState",
]

CAPELLA_INV_OWN = [
    "Withdrawal", "BLSToExecutionChange", "SignedBLSToExecutionChange",
    "HistoricalSummary", "ExecutionPayloadHeader", "LightClientHeader",
]
CAPELLA_VAR_OWN = [
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock", "BeaconState",
    "ExecutionPayload",
    "LightClientBootstrap", "LightClientUpdate",
    "LightClientFinalityUpdate", "LightClientOptimisticUpdate",
]

DENEB_INV_OWN = ["BlobIdentifier", "ExecutionPayloadHeader", "LightClientHeader"]
DENEB_VAR_OWN = [
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock", "BeaconState",
    "ExecutionPayload", "BlobSidecar",
    "LightClientBootstrap", "LightClientUpdate",
    "LightClientFinalityUpdate", "LightClientOptimisticUpdate",
]

ELECTRA_INV_OWN = [
    "PendingDeposit", "PendingPartialWithdrawal", "PendingConsolidation",
    "DepositRequest", "WithdrawalRequest", "ConsolidationRequest",
    "ExecutionRequests", "SingleAttestation",
    "LightClientHeader",
]
ELECTRA_VAR_OWN = [
    "Attestation", "IndexedAttestation", "AttesterSlashing",
    "AggregateAndProof", "SignedAggregateAndProof",
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock", "BeaconState",
    "LightClientBootstrap", "LightClientUpdate",
    "LightClientFinalityUpdate", "LightClientOptimisticUpdate",
]

FULU_INV_OWN = [
    "MatrixEntry", "DataColumnsByRootIdentifier", "LightClientHeader",
]
FULU_VAR_OWN = [
    "DataColumnSidecar",
    "BeaconBlockBody", "BeaconBlock", "SignedBeaconBlock", "BeaconState",
    "LightClientBootstrap", "LightClientUpdate",
    "LightClientFinalityUpdate", "LightClientOptimisticUpdate",
]

FORKS_IN_ORDER = [
    "phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu",
]

OWN = {
    "phase0":    {"inv": PHASE0_INV_OWN,    "var": PHASE0_VAR_OWN},
    "altair":    {"inv": ALTAIR_INV_OWN,    "var": ALTAIR_VAR_OWN},
    "bellatrix": {"inv": BELLATRIX_INV_OWN, "var": BELLATRIX_VAR_OWN},
    "capella":   {"inv": CAPELLA_INV_OWN,   "var": CAPELLA_VAR_OWN},
    "deneb":     {"inv": DENEB_INV_OWN,     "var": DENEB_VAR_OWN},
    "electra":   {"inv": ELECTRA_INV_OWN,   "var": ELECTRA_VAR_OWN},
    "fulu":      {"inv": FULU_INV_OWN,      "var": FULU_VAR_OWN},
}

FORK_CAPS = {f: f[0].upper() + f[1:] for f in FORKS_IN_ORDER}

# Files inside each fork's directory that *define* its own containers.
# Used by `Inherited.lean` for the next fork (which imports them) and
# by Cli/Main.lean. Order: as currently imported by Cli/Main.lean.
FORK_OWN_FILES = {
    "phase0": [
        "LeanEthCS.Forks.Phase0.BeaconBlockHeader",
        "LeanEthCS.Forks.Phase0.Containers",
        "LeanEthCS.Forks.Phase0.Attestations",
        "LeanEthCS.Forks.Phase0.Block",
        "LeanEthCS.Forks.Phase0.State",
    ],
    "altair": [
        "LeanEthCS.Forks.Altair.Sync",
        "LeanEthCS.Forks.Altair.LightClient",
        "LeanEthCS.Forks.Altair.Block",
        "LeanEthCS.Forks.Altair.State",
    ],
    "bellatrix": [
        "LeanEthCS.Forks.Bellatrix.Execution",
        "LeanEthCS.Forks.Bellatrix.Block",
        "LeanEthCS.Forks.Bellatrix.State",
    ],
    "capella": [
        "LeanEthCS.Forks.Capella.Withdrawal",
        "LeanEthCS.Forks.Capella.Execution",
        "LeanEthCS.Forks.Capella.LightClient",
        "LeanEthCS.Forks.Capella.Block",
        "LeanEthCS.Forks.Capella.State",
    ],
    "deneb": [
        "LeanEthCS.Forks.Deneb.Primitives",
        "LeanEthCS.Forks.Deneb.Execution",
        "LeanEthCS.Forks.Deneb.Block",
        "LeanEthCS.Forks.Deneb.State",
        "LeanEthCS.Forks.Deneb.Blob",
        "LeanEthCS.Forks.Deneb.LightClient",
    ],
    "electra": [
        "LeanEthCS.Forks.Electra.PendingOperations",
        "LeanEthCS.Forks.Electra.Requests",
        "LeanEthCS.Forks.Electra.Attestation",
        "LeanEthCS.Forks.Electra.Block",
        "LeanEthCS.Forks.Electra.State",
        "LeanEthCS.Forks.Electra.LightClient",
    ],
    "fulu": [
        "LeanEthCS.Forks.Fulu.Primitives",
        "LeanEthCS.Forks.Fulu.DataColumn",
        "LeanEthCS.Forks.Fulu.Block",
        "LeanEthCS.Forks.Fulu.State",
        "LeanEthCS.Forks.Fulu.LightClient",
    ],
}

# ─────────────────────────────────────────────────────────────────────
# Inheritance computation
# ─────────────────────────────────────────────────────────────────────


def compute_table(fork):
    """Ordered list of `(suffix, kind, source_fork)` for `fork`'s dispatch.

    `source_fork` records the fork that *defines* the concrete type for
    this entry — for own types it equals `fork`; for inherited types it
    points back to the originating fork.
    """
    own_names = set(OWN[fork]["inv"]) | set(OWN[fork]["var"])
    own_entries = (
        [(s, "inv", fork) for s in OWN[fork]["inv"]] +
        [(s, "var", fork) for s in OWN[fork]["var"]]
    )
    if fork == "phase0":
        return own_entries

    prev = FORKS_IN_ORDER[FORKS_IN_ORDER.index(fork) - 1]
    prev_table = compute_table(prev)
    inherited = [
        (s, k, src) for (s, k, src) in prev_table if s not in own_names
    ]
    return inherited + own_entries


def compute_inherited_by_source(fork):
    """Group `fork`'s inherited entries by originating source fork.

    Returns an OrderedDict keyed by source fork in `FORKS_IN_ORDER`
    order; each value is the list of `(suffix, kind)` originating
    there. Own entries (where `src == fork`) are excluded.
    """
    by_source = OrderedDict((f, []) for f in FORKS_IN_ORDER if f != fork)
    for (suffix, kind, src) in compute_table(fork):
        if src == fork:
            continue
        by_source[src].append((suffix, kind))
    # Drop empty buckets so emission iterates non-empty only
    return OrderedDict((k, v) for k, v in by_source.items() if v)


# ─────────────────────────────────────────────────────────────────────
# `Inherited.lean` emission
# ─────────────────────────────────────────────────────────────────────


def emit_inherited(fork):
    """Return Lean source for `LeanEthCS/Forks/<Fork>/Inherited.lean`."""
    assert fork != "phase0", "Phase 0 has no inheritance"
    cap = FORK_CAPS[fork]
    idx = FORKS_IN_ORDER.index(fork)
    prev = FORKS_IN_ORDER[idx - 1]
    by_source = compute_inherited_by_source(fork)

    lines = []

    # Imports: predecessor's Inherited (transitively brings earlier
    # forks) + predecessor's own definition files (which are not in
    # an Inherited).
    imports = []
    if prev != "phase0":
        imports.append(f"import LeanEthCS.Forks.{FORK_CAPS[prev]}.Inherited")
    imports.extend(f"import {m}" for m in FORK_OWN_FILES[prev])
    lines.extend(imports)
    lines.append("")

    # Module docstring
    lines.append("/-!")
    lines.append(
        f"# `LeanEthCS.Forks.{cap}.Inherited` — explicit consensus-spec "
        f"container inheritance"
    )
    lines.append("")
    sources = list(by_source.keys())
    if sources:
        src_names = ", ".join(FORK_CAPS[s] for s in sources)
        lines.append(
            f"Re-binds every container that {cap} inherits unchanged from "
            f"earlier forks ({src_names}) into the `LeanEthCS.Forks.{cap}` "
            f"namespace via `abbrev`. With these aliases in place every "
            f"`LeanEthCS.Forks.{cap}.<Container>` reference resolves "
            f"uniformly — the dispatcher in `Cli/Main.lean` (and any other "
            f"caller) is freed from having to know which earlier fork "
            f"originally defined the type."
        )
        lines.append("")
        lines.append(
            "The `abbrev` form is `@[reducible]` by default, so SSZRepr "
            "instance synthesis transparently sees through every alias to "
            "the underlying `deriving SSZRepr` instance attached to the "
            "originating fork's definition. No new instances are minted, "
            "no extra trust commitments."
        )
        lines.append("")
        lines.append(
            "Grouping is by *original* source fork (the fork that actually "
            "defines the type), so this file doubles as a hand-readable "
            "ledger of `{cap}`'s consensus-spec lineage."
            .replace("{cap}", cap)
        )
    lines.append("")
    lines.append("AUTO-GENERATED by `scripts/gen_cli_dispatch.py` — do not edit.")
    lines.append("Regenerate via `just gen-cli-dispatch`.")
    lines.append("-/")
    lines.append("")

    lines.append("set_option autoImplicit false")
    lines.append("")
    lines.append(f"namespace LeanEthCS.Forks.{cap}")
    lines.append("")

    # Per-source-fork sections
    for source in sources:
        src_cap = FORK_CAPS[source]
        entries = by_source[source]
        inv_names = [s for (s, k) in entries if k == "inv"]
        var_names = [s for (s, k) in entries if k == "var"]

        lines.append(f"/-! ### Inherited from {src_cap} -/")
        lines.append("")

        # Preset-invariant aliases — one `abbrev` per name.
        for name in inv_names:
            lines.append(
                f"abbrev {name} := LeanEthCS.Forks.{src_cap}.{name}"
            )
        if inv_names:
            lines.append("")

        # Preset-variant aliases — wrap Minimal/Mainnet in a sub-namespace
        # so the dotted path mirrors the source.
        for name in var_names:
            lines.append(f"namespace {name}")
            lines.append(
                f"  abbrev Minimal := LeanEthCS.Forks.{src_cap}.{name}.Minimal"
            )
            lines.append(
                f"  abbrev Mainnet := LeanEthCS.Forks.{src_cap}.{name}.Mainnet"
            )
            lines.append(f"end {name}")
            lines.append("")

    lines.append(f"end LeanEthCS.Forks.{cap}")
    return "\n".join(lines) + "\n"


# ─────────────────────────────────────────────────────────────────────
# Dispatcher emission — uniform `LeanEthCS.Forks.<thisFork>.<Suffix>`
# ─────────────────────────────────────────────────────────────────────


def gen_fork_arms(fork, helper_call):
    """Emit match-arms for one fork's dispatcher. Every arm references
    `LeanEthCS.Forks.<fork>.<Suffix>` directly — inheritance lives in
    `Inherited.lean`, not here.
    """
    cap = FORK_CAPS[fork]
    out = []
    seen = set()
    for (suffix, kind, _) in compute_table(fork):
        if suffix in seen:
            continue
        seen.add(suffix)
        if kind == "inv":
            T = f"LeanEthCS.Forks.{cap}.{suffix}"
            out.append(f'  | "{suffix}" => some ({helper_call(T)})')
        else:
            T_min = f"LeanEthCS.Forks.{cap}.{suffix}.Minimal"
            T_man = f"LeanEthCS.Forks.{cap}.{suffix}.Mainnet"
            out.append(f'  | "{suffix}" => some (match preset with')
            out.append(f'      | .Minimal => {helper_call(T_min)}')
            out.append(f'      | .Mainnet => {helper_call(T_man)})')
    return "\n".join(out)


def gen_per_fork_funcs(name, retty, helper_call):
    parts = []
    for fork in FORKS_IN_ORDER:
        body = gen_fork_arms(fork, helper_call)
        sig = (
            f"private def dispatch{name}_{fork} (preset : Preset) (suffix : String) "
            f"(raw : ByteArray)"
        )
        if name == "Check":
            sig += " (expected : ByteArray)"
        sig += f" : Option ({retty}) :=\n"
        parts.append(f"{sig}  match suffix with\n{body}\n  | _ => none")
    return "\n\n".join(parts)


def gen_top_dispatch(name, retty, errExpr):
    extra_arg = " expected" if name == "Check" else ""
    arms = []
    for fork in FORKS_IN_ORDER:
        arms.append(
            f'    | "{fork}" =>\n'
            f"        (dispatch{name}_{fork} preset suffix raw{extra_arg}).getD\n"
            f"          ({errExpr})"
        )
    arms_str = "\n".join(arms)
    expected_param = "(expected : ByteArray) " if name == "Check" else ""
    return (
        f"private def dispatch{name} (typeId : String) (raw : ByteArray)\n"
        f"    {expected_param}: {retty} :=\n"
        f"  let (preset, key) := parseTypeId typeId\n"
        f'  match key.splitOn ":" with\n'
        f"  | [fork, suffix] =>\n"
        f"    match fork with\n"
        f"{arms_str}\n"
        f"    | _ => {errExpr}\n"
        f"  | _ => {errExpr}"
    )


def emit_dispatcher_block():
    err = '.error s!"unknown type identifier: {typeId}"'
    parts = [
        "/-- Preset selector parsed from the `<preset>/<fork>:<type>` identifier. -/",
        "private inductive Preset where",
        "  | Minimal",
        "  | Mainnet",
        "  deriving Repr, DecidableEq",
        "",
        "private def parseTypeId (typeId : String) : Preset × String :=",
        '  if typeId.startsWith "minimal/" then',
        '    (.Minimal, (typeId.drop "minimal/".length).toString)',
        '  else if typeId.startsWith "mainnet/" then',
        '    (.Mainnet, (typeId.drop "mainnet/".length).toString)',
        "  else",
        "    (.Minimal, typeId)",
        "",
        "private def runRoot (T : Type) [SSZRepr T] (raw : ByteArray) :",
        "    Except String String :=",
        "  match SSZ.deserialize (T := T) raw with",
        "  | .ok v   => .ok (toHex (SSZ.hashTreeRoot Sha256 v))",
        '  | .error e => .error s!"deserialize failed: {repr e}"',
        "",
        "private def runCheck (T : Type) [SSZRepr T] (raw : ByteArray)",
        "    (expectedRoot : ByteArray) : Except String Unit :=",
        "  match SSZ.deserialize (T := T) raw with",
        '  | .error e => .error s!"deserialize failed: {repr e}"',
        "  | .ok v =>",
        "      let reSerialized := SSZ.serialize v",
        "      if reSerialized ≠ raw then",
        '        .error s!"re-serialize mismatch: serialized {reSerialized.size} bytes, input was {raw.size}"',
        "      else",
        "        let root := SSZ.hashTreeRoot Sha256 v",
        "        if root ≠ expectedRoot then",
        '          .error s!"root mismatch: got {toHex root}, expected {toHex expectedRoot}"',
        "        else .ok ()",
        "",
        gen_per_fork_funcs("Root", "Except String String",
                           lambda T: f"runRoot (T := {T}) raw"),
        "",
        gen_top_dispatch("Root", "Except String String", err),
        "",
        gen_per_fork_funcs("Check", "Except String Unit",
                           lambda T: f"runCheck (T := {T}) raw expected"),
        "",
        gen_top_dispatch("Check", "Except String Unit", err),
    ]
    return "\n".join(parts) + "\n"


# ─────────────────────────────────────────────────────────────────────
# Splice into Cli/Main.lean
# ─────────────────────────────────────────────────────────────────────

BEGIN_MARKER = "-- BEGIN AUTO-GENERATED DISPATCH (regenerate via `just gen-cli-dispatch`) --"
END_MARKER = "-- END AUTO-GENERATED DISPATCH --"


def splice_dispatcher(main_lean_path: Path, dispatcher_text: str) -> None:
    content = main_lean_path.read_text()
    begin = content.find(BEGIN_MARKER)
    end = content.find(END_MARKER)
    if begin < 0 or end < 0:
        sys.exit(
            f"missing splice markers in {main_lean_path}; expected\n"
            f"  {BEGIN_MARKER}\nand\n  {END_MARKER}"
        )
    new = (
        content[: begin + len(BEGIN_MARKER)]
        + "\n\n"
        + dispatcher_text
        + "\n"
        + content[end:]
    )
    main_lean_path.write_text(new)


# ─────────────────────────────────────────────────────────────────────
# Driver
# ─────────────────────────────────────────────────────────────────────


def main():
    repo = Path(__file__).resolve().parent.parent
    forks_dir = repo / "packages" / "LeanEthCS" / "LeanEthCS" / "Forks"

    # 1. Per-fork Inherited.lean (Altair .. Fulu)
    for fork in FORKS_IN_ORDER:
        if fork == "phase0":
            continue
        cap = FORK_CAPS[fork]
        out_path = forks_dir / cap / "Inherited.lean"
        out_path.write_text(emit_inherited(fork))
        print(f"wrote {out_path.relative_to(repo)}", file=sys.stderr)

    # 2. Dispatcher block spliced into Cli/Main.lean
    main_lean = repo / "packages" / "LeanEthCS" / "LeanEthCS" / "Cli" / "Main.lean"
    splice_dispatcher(main_lean, emit_dispatcher_block())
    print(f"spliced dispatcher into {main_lean.relative_to(repo)}", file=sys.stderr)


if __name__ == "__main__":
    main()
