import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving

/-!
# `SizzLeanTests.ReprExamples` — typechecker-honest gates for `SSZRepr`

Per CLAUDE.md's *literate by default* discipline, every
user-facing API gets an `example` block the typechecker keeps
honest. This file holds the acceptance examples for `SSZRepr`: a
hand-written instance on a two-field `Pair` structure and its
`deriving`-generated counterpart. Each compiles only if the
corresponding piece of library machinery is correct, so a green
build is a passed gate.

Lives in `SizzLeanTests/` rather than `SizzLean/Repr/` so the
fixture structures (`Pair`, `DPair`) don't ride along on every
`import SizzLean` — they're acceptance tests, not part of the
user-facing surface.

## Why `Pair {a b : Bool}` as the example

`SSZ.roundtrip` is gated by `SSZType.BasicSupported r.shape`
(`Repr/Class.lean`), and `BasicSupported` currently covers
`.bool` and `.container [.bool, .bool]` (see
`Spec/BasicSupported.lean`). The smallest non-trivial user
structure that lives in `BasicSupported` is therefore a
two-`Bool` container — exactly the `Pair` defined below. Larger
structures and structures with non-`Bool` fields ride on the
general `containerFixed` widening planned for `BasicSupported`.
-/

set_option autoImplicit false

namespace SizzLeanTests.ReprExamples

open SizzLean

/-- Two-`Bool` container — the canonical example. -/
structure Pair where
  a : Bool
  b : Bool
  deriving DecidableEq, Repr

/-- Hand-written `SSZRepr` instance for `Pair`.

* `shape` is `.container [.bool, .bool]` — what the
  `deriving SSZRepr` handler synthesises mechanically.
* `toRepr` projects the two booleans into the right-nested `Prod`
  chain `interpFields [.bool, .bool] = Bool × Bool × PUnit`.
* `fromRepr` destructures the chain back into a `Pair`.
* Both iso laws close by `rfl`: `fromRepr ∘ toRepr` builds
  `{ a := p.a, b := p.b }` (structurally `p`); `toRepr ∘ fromRepr`
  builds `(r.1, r.2.1, PUnit.unit)` and matches `r` because `PUnit`
  has a single inhabitant. -/
instance instSSZReprPair : SSZRepr Pair where
  shape    := .container [.bool, .bool]
  toRepr   := fun p => (p.a, p.b, PUnit.unit)
  fromRepr := fun ⟨a, b, _⟩ => { a := a, b := b }
  to_from  := fun _ => rfl
  from_to  := fun ⟨_, _, u⟩ => by cases u; rfl

/-- Acceptance check: roundtrip closes via `SSZ.roundtrip`, which
dispatches on `Spec.SSZType.BasicSupported.containerBoolBool`.
The Lean typechecker rejects this `example` if either the iso
laws fail or the shape sits outside `BasicSupported`. -/
example (p : Pair) : SSZ.deserialize (SSZ.serialize p) = .ok p :=
  SSZ.roundtrip .containerBoolBool p

/-! ### `deriving SSZRepr` example

Same shape as `Pair` (two `Bool` fields), but the `SSZRepr`
instance is synthesised by the `deriving` handler in
`Repr/Deriving.lean` instead of being written out by hand.
Acceptance is twofold: the declaration compiles (the handler ran
successfully) and the roundtrip example closes via `SSZ.roundtrip`
(the synthesised instance is correct end-to-end). -/

/-- Two-`Bool` container, `SSZRepr` synthesised. -/
structure DPair where
  a : Bool
  b : Bool
  deriving SSZRepr

/-- Acceptance check: roundtrip on the `deriving`-generated
instance. Closes through the same `containerBoolBool` predicate
arm as the hand-written `Pair` example — the synthesised `shape`
must definitionally equal `.container [.bool, .bool]`. -/
example (p : DPair) : SSZ.deserialize (SSZ.serialize p) = .ok p :=
  SSZ.roundtrip .containerBoolBool p

end SizzLeanTests.ReprExamples
