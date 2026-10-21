import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryNormalTemplate
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryNormalCarryConclusion

/-! The complete elementary-top proper-normal branch of degree32.
All literal intermediate model and index premises are supplied internally
from the same original source and original normal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem ten_le_genRank_of_proper_normal_nine_elementary_top
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hel : BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
    10 ≤ MarkedC4.genRank U := by
  by_contra hsmall
  have hgen : MarkedC4.genRank U ≤ 9 := by omega
  obtain ⟨_,hB,_,hindex,_,hcomm⟩ :=
    F.elementary_proper_normal_nine_saturation hU hgen hel N hproper hN
  obtain ⟨E,hzero,hH,hK,hS⟩ :=
    F.elementary_rank_nine_normal_actual_zero_template hU hgen hel N hproper hN
  exact hsmall (F.elementary_phi_zero_normal_nine_genRank_ten E hU hel hzero hH hK
    N hS hB hindex hcomm hN)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
