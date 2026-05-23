import SizzLean.Spec.Supported
import SizzLean.Spec.MaxByteLength
import SizzLean.Proofs.Roundtrip  -- for SSZType.BasicSupported

/-!
# `SizzLean.Proofs.SizeBound` — encoded-size upper bound

The third central theorem:

```
theorem encode_size_le_max :
    ∀ (s : SSZType) (x : s.interp),
      (serialize s x).size ≤ s.maxByteLength
```

The "static upper bound on serialized size" guarantee: every
value encodes to at most `s.maxByteLength` bytes, where
`maxByteLength` is purely schema-derived (no value input). Useful
for pre-flight buffer sizing and Merkleization-tree depth bounds
downstream.

## Scope (mirrors `Proofs/Roundtrip.lean` / `Proofs/Injective.lean`)

The theorem ships under a narrow predicate covering only the
`.bool` constructor — the same narrow predicate
`decode_encode` and `serialize_injective` live on.

The predicate reused here is `SSZType.BasicSupported` (defined in
`Spec/BasicSupported.lean`). Future work widens it constructor by
constructor in lockstep with `decode_encode`'s coverage.

## What's deferred

Same list as Roundtrip — when each constructor's `decode_encode`
arm closes, the corresponding `encode_size_le_max` arm follows
mechanically because the latter is an *independent* induction (no
cross-stage decode dependency); the gating constraint is the
`ByteArray.size_push` / `size_append` / `size_empty` lemmas, plus
the `(n + 7) / 8`-style ceiling-divison arithmetic `omega` solves.

## Lean idioms used here

* `cases b` on a `Bool` value — produces the two literal sub-goals
  with no free variables, allowing kernel `rfl` / `decide` to close.
* The `decide` tactic on `Nat`-shaped inequalities — `1 ≤ 1` (etc.)
  is decidable via the `Decidable (a ≤ b)` instance on `Nat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace SizzLean.Proofs

open SizzLean.Spec

/-- Per-bool case of the size bound. Both `true` and `false`
serialize to a 1-byte `ByteArray`, and `maxByteLength .bool = 1`,
so `1 ≤ 1` closes each case. -/
theorem encode_size_le_max_bool : ∀ (x : Bool),
    (SSZType.serialize .bool x).size ≤ SSZType.maxByteLength .bool := by
  intro x
  cases x <;> (unfold SSZType.serialize SSZType.maxByteLength; decide)

/-- Per-`Pair`-container case of the size bound. Two consecutive
`Bool` fields encode to exactly 2 bytes; `maxByteLength
(.container [.bool, .bool]) = 2`, so the inequality is `2 ≤ 2`.

Like `decode_encode_container_bool_bool`, the kernel reduces each
of the 4 closed ground cases end-to-end via `simp` + `decide`. -/
theorem encode_size_le_max_container_bool_bool :
    ∀ (vs : SSZType.interpFields [.bool, .bool]),
      (SSZType.serialize (.container [.bool, .bool]) vs).size ≤
        SSZType.maxByteLength (.container [.bool, .bool]) := by
  intro vs
  obtain ⟨a, b, u⟩ := vs
  cases u
  cases a <;> cases b <;>
    (simp [SSZType.serialize, SSZType.serializeFieldsAux,
           SSZType.fixedByteSize, SSZType.fixedSectionSizeFields,
           SSZType.fixedSectionSize, SSZType.isFixedSize,
           SSZType.maxByteLength, SSZType.maxByteLengthFields])

/-- *Encoded-size upper bound* (ARCHITECTURE.md §4): every
`BasicSupported`-shape value's serialized form fits within the
schema-derived `maxByteLength` upper bound. Each new arm closes
by reducing both sides to `Nat` constants and discharging via
`decide` (or `omega` once arithmetic on `+ 7 / 8` enters). -/
theorem encode_size_le_max : ∀ (s : SSZType), SSZType.BasicSupported s →
    ∀ (x : s.interp),
      (SSZType.serialize s x).size ≤ SSZType.maxByteLength s := by
  intro s h_sup x
  cases h_sup with
  | bool =>
      let b' : Bool := x
      exact encode_size_le_max_bool b'
  | containerBoolBool =>
      let vs : SSZType.interpFields [.bool, .bool] := x
      exact encode_size_le_max_container_bool_bool vs

end SizzLean.Proofs
