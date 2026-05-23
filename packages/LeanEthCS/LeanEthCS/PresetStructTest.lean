import LeanEthCS.PresetStruct
import SizzLean.Repr.Deriving
import SizzLean.Spec.Type

/-! Smoke tests for `ssz_struct_for_presets`. -/

set_option autoImplicit false

namespace LeanEthCS.Macros.Test

open SizzLean

-- Tiny single-field container exercising `SLOTS_PER_HISTORICAL_ROOT`.
ssz_struct_for_presets Tiny in LeanEthCS.Macros.Test
    for [minimal, mainnet] where
  blockRoots : Vector UInt8 @@SLOTS_PER_HISTORICAL_ROOT

example : SSZRepr Tiny.Minimal := inferInstance
example : SSZRepr Tiny.Mainnet := inferInstance

-- Per-preset shapes (each is a container with one field).
example :
    @SSZRepr.shape Tiny.Minimal _ =
      .container [.vector (.uintN 8) 64] := rfl

example :
    @SSZRepr.shape Tiny.Mainnet _ =
      .container [.vector (.uintN 8) 8192] := rfl

-- Multi-placeholder + arithmetic + multi-field.
ssz_struct_for_presets Wide in LeanEthCS.Macros.Test
    for [minimal, mainnet] where
  votes  : Vector UInt8 (@@EPOCHS_PER_ETH1_VOTING_PERIOD * @@SLOTS_PER_EPOCH),
  bits   : Vector UInt8 @@SLOTS_PER_HISTORICAL_ROOT,
  marker : UInt64

example :
    @SSZRepr.shape Wide.Minimal _ =
      .container [.vector (.uintN 8) 32,
                  .vector (.uintN 8) 64,
                  .uintN 64] := rfl

example :
    @SSZRepr.shape Wide.Mainnet _ =
      .container [.vector (.uintN 8) 2048,
                  .vector (.uintN 8) 8192,
                  .uintN 64] := rfl

-- Preset-variant type reference via `@%`.
ssz_struct_for_presets Inner in LeanEthCS.Macros.Test
    for [minimal, mainnet] where
  marker : Vector UInt8 @@SYNC_COMMITTEE_SIZE

ssz_struct_for_presets Outer in LeanEthCS.Macros.Test
    for [minimal, mainnet] where
  inner : @%Inner

example :
    @SSZRepr.shape Outer.Minimal _ =
      .container [.container [.vector (.uintN 8) 32]] := rfl

example :
    @SSZRepr.shape Outer.Mainnet _ =
      .container [.container [.vector (.uintN 8) 512]] := rfl

end LeanEthCS.Macros.Test
