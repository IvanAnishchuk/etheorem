import SizzLean.Spec.Type

/-!
# `SizzLean.Spec.BasicSupported` — the narrow predicate the proof set grows over

A *strict subset* of `SSZType.Supported` (in `Spec/Supported.lean`)
that the three central theorems (`decode_encode`,
`serialize_injective`, `encode_size_le_max`) are currently proved
for. Each constructor here names an `SSZType` shape on which the
proofs close exhaustively; adding a constructor obliges the
proofs to extend. The predicate can be retired entirely once the
proofs cover all of `Supported`.

The predicate lives in `Spec/` (not `Proofs/`) because the
user-facing `SSZ.roundtrip` corollary in `Repr/Class.lean`
mentions it — a layering concern that follows ARCHITECTURE.md §2's
library-then-surface flow (Spec layer below, Repr layer above;
Proofs/ reaches over to discharge the theorems).

## Current coverage

* `.bool` — booleans.
* `.container [.bool, .bool]` — two-field Bool containers. The
  `Pair {a b : Bool}` example in `Repr/Class.lean` and the
  `deriving SSZRepr` example in `Repr/Deriving.lean` close via
  `SSZ.roundtrip` end-to-end through this constructor.

The `.container [.bool, .bool]` arm is intentionally *concrete*
rather than a quantified `containerFixed` over a general
field-list predicate: the corresponding `decode_encode` proof
closes by exhaustive `cases` on the 4 inhabitants of
`Bool × Bool × PUnit`, no mutual induction required. The wider
proof — a general `containerFixed : SupportedFieldsFixed fs → …`
constructor whose proof inducts over the field list — is the
planned generalisation.

Adding a concrete shape (e.g. `.container [.bool, .uintN 8]`) is
a one-constructor-plus-one-lemma extension following the same
pattern.
-/

set_option autoImplicit false

namespace SizzLean.Spec

/-- Narrow correctness-coverage predicate. Each constructor names
an `SSZType` shape for which all three central theorems
(`decode_encode`, `serialize_injective`, `encode_size_le_max`) are
proved in `Proofs/{Roundtrip,Injective,SizeBound}.lean`. Adding a
constructor obliges the proofs to extend; the planned
generalisation widens this to cover all of `SSZType.Supported`. -/
inductive SSZType.BasicSupported : SSZType → Prop
  | bool : SSZType.BasicSupported .bool
  /-- The concrete `Pair`-shaped container — two consecutive `Bool`
  fields. Selected so the small `Pair {a b : Bool}` examples
  (hand-written and `deriving`-generated) close via `SSZ.roundtrip`
  end-to-end. The wider proof generalises this to `containerFixed`
  over an arbitrary fixed-size field list. -/
  | containerBoolBool : SSZType.BasicSupported (.container [.bool, .bool])

end SizzLean.Spec
