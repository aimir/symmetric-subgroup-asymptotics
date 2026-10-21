import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoElementaryProperSaving
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoNonelementaryNormalTemplates
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRegularParityNormalCarryConclusion
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoFullConstantCarryConclusion
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoHeisenbergNormalCarryConclusion

/-! All original degree32 proper-normal branches are assembled without
an added classification or capacity premise. The actual intersection,
actual top image, original normal and original point action are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

include F

theorem ten_le_genRank_of_proper_normal_nine
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
    10 ≤ MarkedC4.genRank U := by
  by_cases hel : BinarySquareActionStructure.SquaresActTrivially
      (G := F.top.range) (X := Fin 16)
  · exact F.ten_le_genRank_of_proper_normal_nine_elementary_top hU hel N hproper hN
  · by_contra hsmall
    have hgen : MarkedC4.genRank U ≤ 9 := by omega
    obtain ⟨_,hB,_,hTopRank,hindex,_,hcomm⟩ :=
      F.nonelementary_proper_normal_nine_saturation hU hgen hel N hproper hN
    obtain ⟨E,hzero,hmodels⟩ :=
      F.nonelementary_rank_nine_normal_actual_zero_templates hU hgen hel N hproper hN
    rcases hmodels with ⟨hH,hK,hS⟩ | ⟨hH,hK,hS⟩
    · rcases hS with hS | hS
      · exact hsmall (F.regular_parity_zero_normal_nine_genRank_ten E hU hel hzero hH hK
          hTopRank N hS hB hindex hcomm hN)
      · exact hsmall (F.fullconstant_case_genRank_ten E hU hzero hH hK
          hTopRank N hS hB hindex hcomm hN)
    · exact hsmall (F.heisenberg_phi_zero_normal_nine_genRank_ten E hU hel hzero hH hK
        hTopRank N hS hB hindex hcomm hN)

end BinaryPairFrame

theorem twoGroup_degree_thirty_two_ten_le_genRank_of_proper_normal_nine
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 32) (N : Subgroup U) [N.Normal]
    (hproper : N ≠ ⊤) (hN : 9 ≤ MarkedC4.normalGen N) :
    10 ≤ MarkedC4.genRank U := by
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 4 U hU hdegree
  exact F.ten_le_genRank_of_proper_normal_nine hU N hproper hN

end SymmetricSubgroupAsymptotics
