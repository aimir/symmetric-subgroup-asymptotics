import SymmetricSubgroupAsymptotics.SolubleSocleSemisimple
import SymmetricSubgroupAsymptotics.CoprimeCyclicQuotientSocles
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-! The actual socle of a finite Z-group is cyclic: the group is soluble,
its socle is abelian, and an abelian Z-group is cyclic. In particular every
group of squarefree order, including6 and10, has one socle normal generator.
No dihedral or cyclic model classification is needed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem socleNormalGeneratorBound_one_of_isZGroup
    {G : Type} [Group G] [Finite G] [IsZGroup G] : SocleNormalGeneratorBound G 1 := by
  letI : IsMulCommutative (finiteGroupSocle G) :=
    SolubleSocleConjugationModule.socle_isMulCommutative
  letI : IsCyclic (finiteGroupSocle G) := inferInstance
  exact (socleNormalGeneratorBound_iff_normalGen_le G 1).2
    (CoprimeCyclicQuotientSocles.normalGen_le_one_of_isCyclic (finiteGroupSocle G))

theorem socleNormalGeneratorBound_one_of_squarefree_card
    {G : Type} [Group G] [Finite G] (hG : Squarefree (Nat.card G)) :
    SocleNormalGeneratorBound G 1 := by
  letI : IsZGroup G := IsZGroup.of_squarefree hG
  exact socleNormalGeneratorBound_one_of_isZGroup

theorem socleNormalGeneratorBound_one_of_card_six_or_ten
    {G : Type} [Group G] [Finite G] (hG : Nat.card G=6 ∨ Nat.card G=10) :
    SocleNormalGeneratorBound G 1 := by
  apply socleNormalGeneratorBound_one_of_squarefree_card
  rcases hG with h|h <;> rw [h] <;> decide +kernel

end SymmetricSubgroupAsymptotics
