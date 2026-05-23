![SizzLean](sizzlean_cartoon.jpeg)

# SizzLean - Serialization, well-done.

A Lean 4 implementation of Ethereum's
[SSZ](https://github.com/ethereum/consensus-specs/blob/dev/ssz/simple-serialize.md)
(Simple Serialize): serialization, deserialization, Merkleization,
cached-tree machinery, and the `sszUpdate` macro surface — all of
it sharing one library between production code and machine-checked
theorems.

## Why SizzLean

- **Write once, pick your backend.** Code written against this
  library runs on either of two implementations under the hood — a
  heavily optimised cached Merkle tree for production speed, or a
  simple uncached version that's friendly to Lean proofs. You
  choose at the call site; the spec or state-transition function
  you wrote doesn't change. No duplicated source between the
  runtime path and the verification path.

- **Validated against Ethereum's test corpus.** Passes both
  upstream SSZ suites from `ethereum/consensus-spec-tests`
  end-to-end: `ssz_generic` (1865 / 1865 cases — the wire-format
  tests) and `ssz_static` (38991 / 38991 cases on the minimal
  preset, every fork from Phase 0 through Fulu — the per-fork
  consensus-container tests). SHA-256 passes the NIST CAVP
  vectors on every hasher the library ships.

- **Fast hash-tree-root.** Updates are incremental: only the
  path from a changed field to the root rehashes. Multi-field
  updates batch the work across overlapping paths.

- **Zero boilerplate per type.** Add `deriving SSZRepr` to your
  Lean structure and you get serialization, deserialization,
  hash-tree-root, and the central correctness theorems — for
  free, per type, with no hand-written proofs.

- **Trust assumptions you can grep for.** Every reliance on the
  C SHA-256 implementation is named and audit-listed — it shows
  up in any proof's trust footprint, and is replaceable later
  by a proof without touching a single theorem statement.

- **Pluggable hash function.** Today it's SHA-256. Tomorrow it
  can be Poseidon2 — or whatever the Beam Chain redesign settles
  on — without rewriting your containers, your proofs, or your
  cache logic.

- **Literate by default.** SizzLean sits at the intersection of
  two specialist worlds — SSZ and Lean 4 — and most readers only
  know one. The library is written with comments that teach the
  reader what the code does *and* the Lean idioms it uses, so a
  Lean-fluent reader can pick up the SSZ semantics and an
  SSZ-fluent reader can pick up the Lean. The cost is paid once
  when the code is written; the dividend compounds with every new
  contributor.

- **Every Ethereum consensus fork covered.** Phase 0 through
  Gloas, including the new ePBS containers.

## Scope

Provides the SSZ *library* — types and primitives. Consensus-spec
container definitions (Phase0 → Gloas) live in the sibling
`LeanEthCS` package.

## Status

**Experimental, conformance-validated.** Every SSZ type used by
the Ethereum consensus spec from Phase 0 through Gloas is
implemented. Both upstream test suites
(`ethereum/consensus-spec-tests`) pass end-to-end:
**1865 / 1865** `ssz_generic` cases and **38991 / 38991** `ssz_static`
cases (minimal preset, every fork Phase 0 → Fulu). Mainnet preset
validated at `--limit 2` (1641 / 1641); full mainnet `--all` sweep
is a `workflow_dispatch` button in CI.

### SSZ types implemented

| Type | Notes |
|---|---|
| `uintN` for `N ∈ {8, 16, 32, 64, 128, 256}` | Per spec; covers all currently-used widths |
| `boolean` | Single-byte `0x00` / `0x01` |
| `Vector[T, N]` | Fixed-length list |
| `List[T, N]` | Variable-length list with cap `N` and mix-in-length root |
| `Bitvector[N]` | Fixed-length bit array |
| `Bitlist[N]` | Variable-length bit array with trailing-`1` delimiter |
| `Container` | Heterogeneous record / struct — every consensus container is one of these |

### SSZ types deliberately *not* implemented

These forms appear in the SSZ spec but are not used by any
consensus-spec fork through Gloas, so the library omits them
to keep the core proof obligation small:

| Type | Source | Status here |
|---|---|---|
| `Union[T₁, …, Tₙ]` | core SSZ spec | unimplemented — no fork uses it |
| `ProgressiveContainer(active_fields=[…])` | EIP-7495 | unimplemented — no fork adopted EIP-7495 |
| `StableContainer[N]` + `Profile` | EIP-7495 (legacy form) | unimplemented |
| `ProgressiveList[T]` / `ProgressiveBitlist` | EIP-7916 | unimplemented |
| `CompatibleUnion({sel: type, …})` | EIP-8016 | unimplemented |

ARCHITECTURE.md §8 carries the recipe for reintroducing any of
these the day a fork adopts them — they slot back into `SSZType`
as new constructors without disrupting the existing layers.

### Track in progress

**Phase 5 formal-verification widening** — the three central
theorems (roundtrip, non-malleability, size bound) are landed on
the narrow `BasicSupported` cut; widening to a universal statement
over `Supported` is the open work. The library itself is
complete; this track only closes the proof obligation.

See [`docs/PLAN.md`](docs/PLAN.md) for the staged roadmap and
[`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for the design
contract.

## Dependencies

* `LeanSha256` — pure-Lean SHA-256 reference (used by the kernel-
  reducible `Hasher.Sha256Spec` instance).
* OpenSSL `libcrypto.so.3` — system library, linked via FFI for the
  production `Hasher.Sha256` instance.

The FFI shim (`csrc/sha256_shim.c`) is built procedurally by Lake;
`lakefile.lean` (not `lakefile.toml`) is required for this.

## Module overview

* `Spec/` — `SSZType` universe, `interp`, `serialize`,
  `deserialize`, `hashTreeRoot`. The verified core.
* `Repr/` — the `SSZRepr` typeclass + deriving handler.
* `Hasher/` — abstract `Hasher` typeclass; `Sha256` (FFI) +
  `Sha256Spec` (pure-Lean) instances; `Sha256Equiv` (the named
  equivalence axiom).
* `Cache/` — `TreeBacked` / `UncachedSSZ` / `SSZ.Box` types,
  `sszUpdate` macro, Merkle-tree machinery.
* `Proofs/` — central proof artefacts and `@[ssz_simp]` set.
* `Conformance/` — SSZ-library property-test gates (Sha256
  vectors, hasher equivalence, `setAt` randomised tests, cache
  machinery on example containers).

## Build / test

```bash
lake build SizzLean         # compile the library
```

Three test surfaces, all driven from the umbrella `just` interface
at the repo root. The first two are quick; the third runs against
the downloaded upstream archive.

```bash
# SizzLean-internal property tests (Sha256 vectors, hasher
# equivalence, randomised setAt, cache coherence, sszUpdate cases —
# all fire as native_decide examples at build time)
just test-ssz

# Full NIST CAVP SHA-256 vectors — 129 byte-oriented cases
# (lives in the sibling LeanSha256 package, ~108s of native_decide)
just test-sha256

# Upstream `ethereum/consensus-spec-tests` — drives the Lean CLI
# against the official archives. A tqdm progress bar shows live
# per-case throughput. Quick sample:
just official-ssz-vector-tests
# Full generic sweep (1865 cases, a couple of minutes):
just official-ssz-vector-tests-generic-full
# Full static sweep (38991 cases, minimal preset, all forks Phase 0 → Fulu):
just official-ssz-vector-tests-static-full
```

For the full menu, the protocol the harness uses, and how to
write code that targets `SSZ.FastBox` (production cache) or
`SSZ.PureBox` (proof-friendly uncached) on a *single* spec body,
see [`MANUAL.md`](MANUAL.md).

## Requiring this package

TODO: publication URL.
