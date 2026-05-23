![Etheorem](etheorem_owl.png)

# Etheorem

A Lean 4 monorepo for Ethereum consensus-spec types and SSZ
([Simple Serialize](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md))
with machine-checked correctness on the verified core.

Upstream repository: <https://github.com/etheorem/etheorem>.

## Layout

```
LeanSha256  ←  SizzLean  ←  LeanEthCS
   (pure)      (SSZ +        (consensus
               cache +       containers,
               FFI hash)     Phase0…Gloas)
```

Three Lake subpackages under `packages/`, each with its own
lakefile and independent build target:

- **[`packages/LeanSha256/`](packages/LeanSha256/README.md)** — pure-Lean
  SHA-256 reference. NIST CAVP-validated, kernel-reducible.
  No FFI dependency.
- **[`packages/SizzLean/`](packages/SizzLean/README.md)** — SSZ
  library: spec types, serialization, deserialization,
  Merkleization, the `SSZRepr` deriving handler, the cache layer,
  the `sszUpdate` macro, plus the FFI-backed `Hasher Sha256`
  instance (procedural Lake target builds `csrc/sha256_shim.c`).
- **[`packages/LeanEthCS/`](packages/LeanEthCS/README.md)** —
  Ethereum consensus-spec containers from Phase 0 through Gloas,
  the preset-struct macro, and the `ssz_static` CLI runner
  (`eth_ssz_vector_runner`, driven by `scripts/run_conformance.py`).

The umbrella `lakefile.toml` declares no Lean libraries of its
own — it just coordinates the three subpackages via
`[[require]]` blocks. Per-package publication repos will exist
later; this is a development monorepo.

**Status: conformance-validated.** The Layer 1 spec
(total serialize / deserialize / hashTreeRoot), the `SSZRepr`
typeclass + deriving handler, the FFI SHA-256 backend, the
pure-Lean `Sha256Spec` reference, and the cache layer
(persistent `Node`, `Node.ofShape`, cached merkle walker,
gindex-driven `setManyAt`, fused commit `Node.commitAndHash`,
closure-based pending overlay, `sszUpdate` macro,
`SSZ.Box` user surface) are all landed. Consensus containers
cover Phase 0 through Gloas, including Fulu's `proposer_lookahead`
and the full Gloas ePBS `BeaconState` (nine EIP-7732 fields plus
the supporting `Builder` / `ExecutionPayloadBid` types).
Conformance pinned at consensus-spec-tests
[v1.6.0-beta.0](https://github.com/ethereum/consensus-spec-tests/releases/tag/v1.6.0-beta.0)
in `scripts/run_conformance.py`. The universal proof set
(`decode_encode`, `serialize_injective`, `encode_size_le_max`
over `SSZType.Supported`) and the AVX-512 SIMD inner loop for
`sha256BatchCombine` remain as planned follow-ups; see
[`packages/SizzLean/docs/PLAN.md`](packages/SizzLean/docs/PLAN.md)
for the staged roadmap.

## Documents

Per-subpackage design docs live next to the code they describe:

- [`packages/SizzLean/docs/ARCHITECTURE.md`](packages/SizzLean/docs/ARCHITECTURE.md) —
  the SSZ library's binding design (`SSZType` universe, `SSZRepr`
  typeclass + deriving, cached Merkle tree, FFI SHA-256, trust
  boundary, module layout).
- [`packages/SizzLean/docs/PLAN.md`](packages/SizzLean/docs/PLAN.md) —
  SizzLean's stage-by-stage deliverables and acceptance.
- [`packages/SizzLean/docs/OPTIMISATION.md`](packages/SizzLean/docs/OPTIMISATION.md) —
  implementation-level companion to ARCHITECTURE.md §6: the cache
  layer's data structures, how each Phase 17 sub-stage is wired,
  and the bench-gating story.
- [`packages/SizzLean/docs/research/`](packages/SizzLean/docs/research/) —
  background research (`pre-research.md`, `cache-research.md`).
- [`packages/<Pkg>/README.md`](packages/) — per-subpackage READMEs.

Repo-wide docs at the root:

- [`CLAUDE.md`](CLAUDE.md) — style and discipline conventions, project-wide.
- [`monorepo-arch.md`](monorepo-arch.md) — how the monorepo is laid out:
  the three-subpackage shape, which lakefiles are TOML vs procedural,
  where the FFI C shim lives, and the naming / dep / build conventions.
- [`CONTRIBUTING.md`](CONTRIBUTING.md) — PR / issue workflow,
  toolchain setup, code-style pointers.
- [`SECURITY.md`](SECURITY.md) — vulnerability-disclosure policy.
- [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md) — community guidelines.

## Build

Toolchain pinned in [`lean-toolchain`](lean-toolchain) (elan picks it up).

```bash
# From the repo root — common targets by name:
lake build LeanSha256
lake build SizzLean
lake build LeanEthCS

# Test suites (per package, run on demand):
lake build LeanSha256Tests
lake build SizzLeanTests
lake build LeanEthCSTests

# Bench + profile executables:
lake build ssz_bench       # microbench grid, S1–S7 (see SizzLeanBench.lean)
lake build ssz_profile     # phase-by-phase profile of one workload

# ssz_static / ssz_generic CLI driver (consumed by scripts/run_conformance.py):
lake build eth_ssz_vector_runner

# Or build a single subpackage in isolation:
cd packages/SizzLean && lake build
```

The repo's [`Justfile`](Justfile) wraps the common workflows
(`just build`, `just test`, `just bench`,
`just official-ssz-vector-tests-static`, …) — see `just --list`
for the full set.

CI runs `lake build` for each named library on the pinned
toolchain via `leanprover/lean-action`.

### Native dependencies

The FFI SHA-256 shim (`packages/SizzLean/csrc/sha256_shim.c`)
links against OpenSSL's `libcrypto`. The Lake build expects:

- **Linux (Debian/Ubuntu, including CI):** `libssl-dev` for the
  headers (`/usr/include/openssl/evp.h`) and the versioned
  `libcrypto.so.3` shared library. The Ubuntu CI runners
  preinstall this package; on a fresh local checkout install via:

  ```bash
  sudo apt-get install libssl-dev
  ```

- **macOS:** `openssl@3` via Homebrew, plus the standard build
  toolchain. (`packages/SizzLean/lakefile.lean` hardcodes the Linux
  library path today; macOS support will land when the library
  is in place.)

The C compiler is invoked through the Lean toolchain's `cc`
wrapper — no separate configuration required.

## Conformance harness

`scripts/run_conformance.py` drives the Lean `eth_ssz_vector_runner` CLI against
`ethereum/consensus-spec-tests` release archives. Default mode runs
the **`ssz_generic`** suite (type-agnostic SSZ tests for `uints`,
`basic_vector`, `bitvector`, `bitlist`, `boolean`, `containers`),
with a `--limit N` subset cap by default.

```bash
# One-time: create a Python venv with the needed deps (cramjam + PyYAML)
uv venv
uv pip install -r scripts/requirements.txt

# Default: ssz_generic subset (5 cases per handler/suite)
.venv/bin/python scripts/run_conformance.py

# Full ssz_generic sweep
.venv/bin/python scripts/run_conformance.py --all

# Switch to ssz_static (per-fork consensus types)
.venv/bin/python scripts/run_conformance.py --suite static

# Single-shape focus
.venv/bin/python scripts/run_conformance.py --include 'generic:uints/*'
```

### Current dispatch coverage

The numbers below were last measured against consensus-spec-tests
**v1.5.0**. With the pin now at **v1.6.0-beta.0**, a re-validation
sweep needs to land before the counts can be quoted at the new
tag; the LeanEthCS dispatch surface itself already covers the
Fulu `proposer_lookahead` and the Gloas ePBS field set.

- **`ssz_generic`**: **1865 / 1865 cases pass** across all handlers
  (uints, basic_vector, bitvector, bitlist, boolean, containers).
  The test-only structs (`SingleFieldTestStruct`, `SmallTestStruct`,
  `FixedTestStruct`, `VarTestStruct`, `ComplexTestStruct`,
  `BitsStruct`) have their SSZ shapes hardcoded in
  `packages/LeanEthCS/LeanEthCS/Cli/Main.lean`.
- **`ssz_static`** (`--suite static`): **38991 / 38991 cases pass**
  at v1.5.0 on the minimal preset, every fork from Phase 0
  through Fulu — including variable-size composites
  (`Attestation`, `BeaconBlockBody`, `BeaconState`) and all fork
  deltas (Altair / Bellatrix / Capella / Deneb / Electra / Fulu).
  Mainnet preset validated at `--limit 2` (1641 / 1641); the full
  mainnet `--all` sweep is available as a `workflow_dispatch`
  button in CI. Gloas vectors land with the v1.6.0-beta.0 sweep;
  EIP-7441 (Whisk) deferred per scope.
