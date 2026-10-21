import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoProperSaving
import SymmetricSubgroupAsymptotics.BinaryDegreeSixtyFourFromThirtyTwoProperSaving
import SymmetricSubgroupAsymptotics.BinarySharpTailFromDegreeSixtyFour

/-! The unconditional degree64 step and all larger degrees use the
proved actual degree32 proper-normal saving. No h53 premise is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem twoGroup_degree_sixty_four_normalGen_le_sixteen
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hdegree : Nat.card X = 64) (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ 16 := by
  obtain ⟨F⟩ := transitiveBinaryPairFrame_nonempty 5 U hU hdegree
  letI : MulAction.IsPretransitive F.top.range (Fin 32) := F.top_pretransitive
  apply F.normalGen_le_sixteen_of_actual_top_proper_saving hU _ N
  intro D hD hproper hhigh
  letI := hD
  exact twoGroup_degree_thirty_two_ten_le_genRank_of_proper_normal_nine
    F.top.range (F.top_isPGroup hU) (by norm_num only [Nat.card_fin]) D hproper hhigh

theorem twoGroup_transitive_normalGen_le_quarter_of_large_degree
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (hlarge : 64 ≤ Nat.card X) (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N ≤ Nat.card X / 4 := by
  apply twoGroup_transitive_normalGen_le_quarter_of_degree_sixtyfour _ U hU hlarge N
  intro Y _ V _ hV hdegree M hM
  letI := hM
  exact twoGroup_degree_sixty_four_normalGen_le_sixteen V hV hdegree M

end SymmetricSubgroupAsymptotics
