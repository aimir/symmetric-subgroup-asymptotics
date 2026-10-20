import SymmetricSubgroupAsymptotics.BinaryFourAugmentationMiddleChart
import SymmetricSubgroupAsymptotics.BinaryFourSymmetricBlockActions

/-! The retained fullS reflection on the exact middle layer. These are
the original eight-coordinate formulas used by the symmetric block model. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourFullBlockCoordinates BinaryFourSymmetricBlockActions

def canonicalChartReflection (x : Middle) : Middle :=
  ![x 1, x 0, x 2 + x 3, x 3]

theorem middleChart_fullS (x : Coordinates) :
    middleChart (middleProjection (head (fullS (includeAugmentation x)))) =
      canonicalChartReflection (middleChart (middleProjection x)) := by
  revert x
  decide +kernel

theorem canonical_trivial_middle_fixed (a b : Scalar) :
    canonicalChartReflection ![a, b, 0, 0] = ![a, b, 0, 0] ↔ a = b := by
  revert a b
  decide +kernel

theorem canonical_trivial_middle_difference (a b : Scalar) :
    canonicalChartReflection ![a, b, 0, 0] - ![a, b, 0, 0] =
      ![a + b, a + b, 0, 0] := by
  revert a b
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
