import SizzLean.Hasher.Sha256
import SizzLean.Repr.Class
import SizzLean.Repr.Instances
import SizzLean.Repr.Deriving
import SizzLean.Cache.TreeBacked
import SizzLean.Cache.Uncached
import SizzLean.Cache.Box
import SizzLean.Cache.Update

/-!
# `SizzLeanTests.InfallibleIndex`: the `sszUpdate t with f[i]! := v` form

Acceptance gates for the infallible index segment `[i]!`. Unlike the checked
`[i]` (which makes the whole `sszUpdate` return `Except IndexError _` and
rejects an out-of-range index), `[i]!` mirrors `Array.set!`:

* an `sszUpdate` whose index clauses are all `[i]!` returns the **bare** cache
  value, no `Except` to thread;
* an in-range `[i]!` write behaves exactly like the checked form;
* an out-of-range `[i]!` write is a silent **no-op** (the view's `set!`
  no-ops, and the cached pending closure drops the write at commit, so the
  root is unchanged);
* `sszGet b f[i]!` reads the bare element, yielding the element's `default`
  on a miss.

A clause mixing a bang and a checked index still returns `Except`: the checked
index governs accept/reject, while the bang index just no-ops on a miss.

## Expected panic lines

The out-of-range `[i]!` cases below drive `Array.set!` / `Array.get!` past the
end, which print an `Error: index out of bounds` line to stderr before
returning the collection unchanged (or `default`). Those lines are expected;
the authoritative signal is `Build completed successfully`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace SizzLeanTests.InfallibleIndex

open SizzLean
open SizzLean.Hasher
open SizzLean.Cache
open SizzLean.Repr

/-- A container with a basic-element list field. Three elements, so any index
`≥ 3` is out of range. -/
structure S where
  xs     : SSZList UInt64 8
  marker : UInt64
deriving DecidableEq, Inhabited, SSZRepr

private def s0 : S := { xs := ⟨#[10, 20, 30], by decide⟩, marker := 0 }

/-- Project the error out of an `Except IndexError _`, for the mixed cases. -/
private def errOf {α : Type} : Except IndexError α → Option IndexError
  | .ok _    => none
  | .error e => some e

/-! ## An all-`[i]!` update returns the bare cache value (no `Except`)

These ascriptions fail to typecheck if the result were wrapped in `Except`. -/

example : UncachedSSZ Sha256 S :=
  sszUpdate (UncachedSSZ.ofValue Sha256 s0) with xs[1]! := 99
example : TreeBacked Sha256 S :=
  sszUpdate (TreeBacked.ofValue Sha256 s0) with xs[1]! := 99
example : SSZ.Box Sha256 S :=
  sszUpdate (SSZ.FastBox s0) with xs[1]! := 99

/-! ## In-range `[i]!` writes match the directly-updated value -/

/-- Uncached, bare result read directly (no `.toOption`). -/
example :
    (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with xs[1]! := 99).hashTreeRoot
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 99 } : S) := by
  native_decide

/-- Cached. -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with xs[1]! := 99).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 99 } : S) := by
  native_decide

/-- Box (`FastBox`). -/
example :
    ((sszUpdate (SSZ.FastBox s0) with xs[1]! := 99).hashTreeRoot).1
      = SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 99 } : S) := by
  native_decide

/-! ## Out-of-range `[i]!` writes are a no-op (root unchanged)

The uncached path's `set!` no-ops; the cached path's pending closure re-checks
at commit and drops the write, so the tree stays coherent with the view. -/

/-- Uncached: `xs[7]!` past the end leaves the value unchanged. -/
example :
    (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with xs[7]! := 99).hashTreeRoot
      = SSZ.hashTreeRoot Sha256 s0 := by
  native_decide

/-- Cached: same no-op through the Merkle spine (the dropped pending write). -/
example :
    (sszUpdate (TreeBacked.ofValue Sha256 s0) with xs[7]! := 99).hashTreeRootCached.1
      = SSZ.hashTreeRoot Sha256 s0 := by
  native_decide

/-! ## Mixing `[i]!` with a checked `[i]`

The presence of a checked index makes the result `Except`; the checked index
governs accept/reject, the bang index just no-ops on a miss. -/

/-- Bang index out of range (no-op) alongside an in-range checked index: the
update succeeds, with only the checked write applied. -/
example :
    (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with
      xs[7]! := 7, xs[1] := 9).toOption.map (·.hashTreeRoot)
      = some (SSZ.hashTreeRoot Sha256 ({ s0 with xs := s0.xs.set! 1 9 } : S)) := by
  native_decide

/-- In-range bang index alongside an out-of-range checked index: the checked
index rejects with its real index and bound, so nothing is written. -/
example :
    errOf (sszUpdate (UncachedSSZ.ofValue Sha256 s0) with
      xs[1]! := 7, xs[5] := 9) = some (IndexError.indexError 5 3) := by
  decide

/-! ## `sszGet b f[i]!`: bare read, `default` on a miss -/

/-- In range: the bare element. -/
example : sszGet (UncachedSSZ.ofValue Sha256 s0) xs[2]! = 30 := by decide

/-- Out of range: the element type's `default` (`0` for `UInt64`). -/
example : sszGet (UncachedSSZ.ofValue Sha256 s0) xs[7]! = (0 : UInt64) := by
  native_decide

end SizzLeanTests.InfallibleIndex
