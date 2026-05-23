import SizzLean.Spec.Supported
import SizzLean.Spec.BasicSupported
import SizzLean.Proofs.SimpAttrs

/-!
# `SizzLean.Proofs.Roundtrip` — `decode_encode` over `BasicSupported`

The `decode_encode` theorem gated on `BasicSupported` (in
`Spec/BasicSupported.lean`), which currently covers `.bool` and
the concrete `.container [.bool, .bool]` shape. The
universally-quantified form `∀ s, Supported s → …` is the
planned generalisation.

The `.container [.bool, .bool]` arm exists so the `Pair
{a b : Bool}` example structures (hand-written and
`deriving`-generated) close via `SSZ.roundtrip` end-to-end rather
than via `native_decide` — keeping the verified path lit at the
user surface and treating native evaluation as a
conformance-suite tool only (per ARCHITECTURE.md §4's tactic
vocabulary).

The proof closes by exhaustive case analysis on the 4 inhabitants
of `Bool × Bool × PUnit`: the kernel can fully evaluate each
closed `serialize` / `deserialize` term, so `rfl` discharges each
branch after a single `unfold` of the mutual block's top-level
dispatch.

## Why concrete instead of universally-quantified

The general `containerFixed : SupportedFieldsFixed fs → …` form
requires mutual induction across `BasicSupported` / a companion
`BasicSupportedFieldsFixed` predicate, with size-decomposition and
`ByteArray.extract`/`append` rewriting — several hundred lines of
proof in full. The concrete approach keeps this file at ~80 lines
while letting the universally-quantified version supersede the
constructor cleanly when the proof set widens.
-/

set_option autoImplicit false
-- See `Spec/Deserialize.lean` and `Spec/HashTreeRoot.lean`: each
-- `unfold` of the mutual block in a proof requires the same
-- elaboration budget as defining the block itself.
set_option maxHeartbeats 10000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-! ### Per-shape roundtrip lemmas

One lemma per constructor of `BasicSupported`. Each is closed by
`cases` on the concrete `s.interp` value (`Bool` for `.bool`,
`Bool × Bool × PUnit` for `.container [.bool, .bool]`), followed by
`unfold` of the mutual block and `rfl` for kernel reduction. -/

/-- Roundtrip for `.bool`.

Two ground cases (`true`, `false`); each reduces to `.ok (·, 1)` by
unfolding the dispatch and letting the kernel evaluate the LE-byte
write and read. -/
theorem decode_encode_bool : ∀ (x : Bool),
    SSZType.deserialize .bool (SSZType.serialize .bool x) =
      .ok (x, (SSZType.serialize .bool x).size) := by
  intro x
  cases x <;> (unfold SSZType.deserialize SSZType.serialize; rfl)

/-- Roundtrip for `.container [.bool, .bool]`.

The interpretation `interpFields [.bool, .bool] = Bool × (Bool × PUnit)`
has 4 inhabitants (`PUnit` has a single value); destructure with
`obtain` then `cases` each `Bool`. Each closed case reduces by
`unfold` + `rfl`: the encoder writes two consecutive 1-byte payloads
(no offset table because both fields are fixed-size), and the decoder
reads them back via `deserializeFixedFields` which steps through one
byte at a time. -/
theorem decode_encode_container_bool_bool :
    ∀ (vs : SSZType.interpFields [.bool, .bool]),
      SSZType.deserialize (.container [.bool, .bool])
          (SSZType.serialize (.container [.bool, .bool]) vs) =
        .ok (vs, (SSZType.serialize (.container [.bool, .bool]) vs).size) := by
  intro vs
  -- `vs : Bool × Bool × PUnit` by `interp` reduction at `.container [.bool, .bool]`.
  obtain ⟨a, b, u⟩ := vs
  -- `u : PUnit` has a single value; eliminate it.
  cases u
  -- 4 closed ground cases. The kernel doesn't auto-reduce mutual
  -- block definitions, so we explicitly `simp` the spec-side mutual
  -- members via the `ssz_simp` set (Proofs/SimpAttrs.lean tags them);
  -- the closed-form evaluation lands at `Except.ok ...` on both
  -- sides and `rfl` closes.
  cases a <;> cases b <;>
    (simp [SSZType.deserialize, SSZType.serialize,
           SSZType.deserializeFixedFields, SSZType.serializeFieldsAux,
           SSZType.fixedByteSize, SSZType.fixedSectionSizeFields,
           SSZType.fixedSectionSize,
           SSZType.allFixedSize, SSZType.isFixedSize];
     rfl)

/-! ### Dispatch theorem

Roundtrip for any `BasicSupported` shape. With two constructors in
scope, the dispatch is two delegations — each new shape added to
`BasicSupported` extends this `cases` with one more arm. -/

/-- Roundtrip over `BasicSupported`. Covers `.bool` and the
`Pair`-shaped container; parameterised over the predicate so that
extending coverage means extending the predicate (no signature
change at the call site). -/
theorem decode_encode : ∀ {s : SSZType}, SSZType.BasicSupported s →
    ∀ (x : s.interp),
      SSZType.deserialize s (SSZType.serialize s x) =
        .ok (x, (SSZType.serialize s x).size) := by
  intro s h_sup x
  cases h_sup with
  | bool =>
      -- `x : (.bool).interp` is definitionally `Bool`. The annotated
      -- `let` forces the kernel to perform that reduction so the call
      -- to `decode_encode_bool` typechecks against the explicit `Bool`
      -- argument.
      let b' : Bool := x
      exact decode_encode_bool b'
  | containerBoolBool =>
      -- Same idiom: coerce through `let` so `decode_encode_container_bool_bool`'s
      -- explicit `interpFields [.bool, .bool]` argument typechecks.
      let vs : SSZType.interpFields [.bool, .bool] := x
      exact decode_encode_container_bool_bool vs

end SizzLean.Proofs
