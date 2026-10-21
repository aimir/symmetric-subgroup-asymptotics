import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryNormalIndex
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryCarryConclusion

/-! Actual normal-intersection saturation feeds the elementary carry
consumer on the same original source. No normal subgroup is enlarged. -/
set_option autoImplicit false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance binaryDegreeThirtyTwoElementaryNormalCarryConclusionFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16)) (E : BinaryPairFrame F.top.range (Fin 8))

theorem elementary_phi_zero_normal_nine_genRank_ten
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (hzero : F.top.range = E.splitAffineAction)
    (hH : E.top.range = BinaryEightOriginalRowActions.regularH)
    (hK : E.kernelSpace = (BinaryRegularEightNaturalRegistry.charts 23).2.space)
    (N : Subgroup U) [N.Normal]
    (hS : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation (N ⊓ F.top.ker))).toSubmodule =
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space)
    (hB : MarkedC4.normalGen (N ⊓ F.top.ker) = 6)
    (hindex : (N.map F.top.rangeRestrict).index = 2)
    (hcomm : ⁅F.top.ker,N⁆ ≤ primeRelativeRadical 2 (N ⊓ F.top.ker))
    (hN : 9 ≤ MarkedC4.normalGen N) : 10 ≤ MarkedC4.genRank U := by
  have hkN := (F.elementary_phi_zero_normal_contains_kernel_and_index_two E hU
    hzero hH hK N hS hB hindex hcomm).1
  have hwhole : (E.originalCoordinateSubrepresentation
      (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule =
        (BinaryElementary16GraphHeadRigidity.stateChart 0).space := by
    simpa only [inf_eq_right.mpr hkN] using hS
  have hAb := F.elementary_phi_zero_normal_abelianization_card E hU hzero hH hK N
    hS hB hindex hcomm hN
  exact F.elementary_phi_zero_genRank_ten_of_abelianization_card E hU hel hzero hH hK hwhole hAb

end SymmetricSubgroupAsymptotics.BinaryPairFrame
