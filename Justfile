# Etheorem — task runner.
#
# Run `just` (no args) to list every available recipe.
# Each recipe's comment line is its description in `just --list`.
#
# Layers, in order of how heavy they are to run:
#   1. `build`              — compile every library
#   2. `test`               — local property tests (in-Lean `native_decide`)
#   3. `official-ssz-vector-tests*` — drive the Lean CLI against
#      `ethereum/consensus-spec-tests` release archives
#
# The official-vector-tests recipes need a Python venv. Run
# `just setup-python` once before invoking them.


# List every recipe with its description
default:
    @just --list --unsorted


# ─────────────────────────────────────────────────────────────────────────
# Build
# ─────────────────────────────────────────────────────────────────────────

# Compile all three libraries (LeanSha256 → SizzLean → LeanEthCS)
build:
    lake build LeanSha256
    lake build SizzLean
    lake build LeanEthCS

# Compile the `eth_ssz_vector_runner` CLI driver used by the official-vector-test recipes
build-cli:
    lake build eth_ssz_vector_runner

# Wipe Lake build artefacts (`.lake/` everywhere)
clean:
    lake clean


# ─────────────────────────────────────────────────────────────────────────
# Local property tests (build-time `native_decide` gates)
#
# These compile a library; the gates fire automatically. If any gate
# fails, the build fails. Recipes are roughly ordered cheapest first.
# ─────────────────────────────────────────────────────────────────────────

# All local tests — SHA-256 NIST CAVP + SSZ library gates + LeanEthCS compile-time validation
test: test-sha256 test-ssz test-eth

# Full NIST CAVP byte-oriented SHA-256 vectors — 129 cases via native_decide, ~108s (the 3 anchor FIPS 180-4 §B gates already fire on `lake build LeanSha256` itself; this adds the full upstream suite)
test-sha256:
    lake build LeanSha256Tests

# In-Lean SSZ-library property tests (hasher equivalence, Merkle PRNG, cache machinery on example containers)
test-ssz:
    lake build SizzLeanTests

# LeanEthCS validation — building the library *is* the test: every `deriving SSZRepr` is a compile-time gate. No in-Lean property tests of its own; upstream-vector conformance lives under `official-ssz-vector-tests*`.
test-eth:
    lake build LeanEthCS


# ─────────────────────────────────────────────────────────────────────────
# Microbenchmarks — measure-then-optimise gates for Stage 17
# ─────────────────────────────────────────────────────────────────────────

# Build + run all SizzLean microbenchmarks; emit one TSV row per
# measurement column to `packages/SizzLean/bench/<timestamp>.tsv`.
# Output also prints to stdout so you can pipe / inspect inline.
#
# The bench is run from the compiled native binary at
# `packages/SizzLean/.lake/build/bin/ssz_bench` — `lake build`
# produces it, then we exec it directly (rather than via `lake exe`)
# so there's no ambiguity that we're measuring the compiled binary,
# not any wrapper. The library `SizzLeanBench` is built with
# `precompileModules := true` (see `packages/SizzLean/lakefile.lean`)
# so every imported function is native code; the C shims are built
# with `-O3 -march=native`.
bench:
    @mkdir -p packages/SizzLean/bench
    @ts=$(date -u +%Y%m%dT%H%M%SZ); \
      lake build ssz_bench && \
      packages/SizzLean/.lake/build/bin/ssz_bench \
        | tee "packages/SizzLean/bench/$ts.tsv"

# Diff two bench TSVs. Usage: `just bench-diff before.tsv after.tsv`.
# Aligned column output for readability; falls back to plain diff if
# `column` is unavailable.
bench-diff before after:
    @diff -u {{before}} {{after}} | column -t -s $'\t' || diff -u {{before}} {{after}}


# ─────────────────────────────────────────────────────────────────────────
# Official Ethereum consensus-spec-tests vector suites
#
# Driven by `scripts/run_conformance.py` against
# `ethereum/consensus-spec-tests` release archives. Requires the
# Python venv set up via `just setup-python`.
#
# Two suites:
#   • `ssz_generic` — wire-format tests, type-agnostic (uints,
#     basic_vector, bitvector, bitlist, boolean, containers).
#   • `ssz_static`  — per-fork consensus-container tests
#     (BeaconState, Attestation, BeaconBlockBody, …).
# ─────────────────────────────────────────────────────────────────────────

# Default sample: `ssz_generic`, 5 cases per handler — quick gate
official-ssz-vector-tests:
    .venv/bin/python scripts/run_conformance.py

# Full `ssz_generic` sweep (1865 cases)
official-ssz-vector-tests-generic-full:
    .venv/bin/python scripts/run_conformance.py --all

# Quick `ssz_static` sample (2 cases per handler per fork)
official-ssz-vector-tests-static:
    .venv/bin/python scripts/run_conformance.py --suite static --limit 2

# Full `ssz_static` sweep on minimal preset (38991 cases — every fork Phase 0…Fulu)
official-ssz-vector-tests-static-full:
    .venv/bin/python scripts/run_conformance.py --suite static --all

# Full `ssz_static` sweep on mainnet preset — heavy! (run before a release)
official-ssz-vector-tests-static-mainnet:
    .venv/bin/python scripts/run_conformance.py --suite static --preset mainnet --all

# Focused subset by shape-glob (e.g. `just official-ssz-vector-tests-include 'generic:uints/*'`)
official-ssz-vector-tests-include PATTERN:
    .venv/bin/python scripts/run_conformance.py --include "{{PATTERN}}"

# Everything from the upstream test corpus: full generic + full static on minimal
official-ssz-vector-tests-all: official-ssz-vector-tests-generic-full official-ssz-vector-tests-static-full


# ─────────────────────────────────────────────────────────────────────────
# Code generation (maintenance — re-run when upstream sources change)
# ─────────────────────────────────────────────────────────────────────────

# Re-generate the NIST CAVP vector table from `packages/LeanSha256/cavp/*.rsp`
gen-cavp:
    .venv/bin/python scripts/gen_sha256_cavp.py

# Re-generate the CLI dispatch table (writes to LeanEthCS Cli/Main.lean)
gen-cli-dispatch:
    .venv/bin/python scripts/gen_cli_dispatch.py


# ─────────────────────────────────────────────────────────────────────────
# Python venv (one-time setup, required for official-vector-test recipes)
# ─────────────────────────────────────────────────────────────────────────

# Create `.venv/` and install Python dependencies (uses `uv`)
setup-python:
    uv venv
    uv pip install -r scripts/requirements.txt

# Wipe Lake artefacts *and* the Python venv
clean-all: clean
    rm -rf .venv
