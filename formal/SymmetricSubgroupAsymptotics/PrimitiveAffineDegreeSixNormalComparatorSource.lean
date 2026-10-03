import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixSmallComparators
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-!
# Degree-six normal-comparator sources

Three surviving `3 × 2` affine cells have the same counting shape: the
bottom quotient is paid by one derived-head tail, while every nonbottom
normal quotient is a quotient of a fixed comparator of degree at most five.
This file completes all common numerical plumbing.  A concrete model only
has to provide `PreE7NormalComparatorModel` and a fixed bound for its one
tail coefficient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace DegreeSixNormalComparatorSource

variable {U : PreE7NonPairActionClass 6}
  (M : PreE7NormalComparatorModel 6 U)

/-- A fixed degree-six tail coefficient fits the common logarithmic menu
allowance once it is at most `2^(36·6)`. -/
theorem tail_menu
    (htail : M.tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ))) (b : ℕ) :
    M.tailConstant ≤
      (2 : ℝ) ^
        (16 * (6 : ℝ) * Real.log ((6 + b + 2 : ℕ) : ℝ) ^ 2) :=
  htail.trans
    (two_rpow_thirtySix_width_le_menuMass (w := 6) (by norm_num) b)

/-- The completed ordinary numerical package for a concrete degree-six
normal-comparator model. -/
noncomputable def numericalData
    (htail : M.tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ))) :
    PreE7SmallAdditiveNumericalData .acert 6 U :=
  M.numericalData .acert
    (DegreeSixSelfComparatorSource.normal_menu U)
    (tail_menu M htail)

/-- Final affine exceptional-cell source. -/
noncomputable def source
    (htail : M.tailConstant ≤ (2 : ℝ) ^ (36 * (6 : ℝ))) :
    PreE7RankTailSourceOrYonedaTopData 6 U :=
  .inl (.ordinary .acert (.small (numericalData M htail)))

end DegreeSixNormalComparatorSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
