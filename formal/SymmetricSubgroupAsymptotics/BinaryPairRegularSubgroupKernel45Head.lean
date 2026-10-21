import SymmetricSubgroupAsymptotics.BinaryPairSubgroupRestriction
import SymmetricSubgroupAsymptotics.BinaryPairLayerHead8T3Kernel45
import SymmetricSubgroupAsymptotics.BinaryEightTop31RegularSparse

/-! A literal regular-eight subgroup is enough for the kernel45
three-head bound. The larger original top and all its actual lift
offsets remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (E : BinaryPairFrame U (Fin 8))

theorem naturalModuleHead_le_three_of_regular_subgroup_kernel45
    (hregular : BinaryRegularEightNaturalRegistry.H ≤ E.top.range)
    (hK : E.kernelSpace = BinaryRegularEightNaturalRegistry.chart45.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 3 := by
  exact E.naturalModuleHead_le_of_subgroup_pair_layer_bound
    BinaryRegularEightNaturalRegistry.H hregular _ hK 3
    BinaryPairLayerHead8T3Kernel45.pair_bound W

theorem naturalModuleHead_le_three_of_top_thirty_one_kernel45
    (hH : E.top.range = BinaryEightTop31CoordinateAction.H)
    (hK : E.kernelSpace = BinaryRegularEightNaturalRegistry.chart45.space)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Module.finrank (ZMod 2) W.toRepresentation.Coinvariants ≤ 3 := by
  apply E.naturalModuleHead_le_three_of_regular_subgroup_kernel45 _ hK W
  rw [hH]
  exact BinaryEightTop31RegularSparse.regular_le

end SymmetricSubgroupAsymptotics.BinaryPairFrame
