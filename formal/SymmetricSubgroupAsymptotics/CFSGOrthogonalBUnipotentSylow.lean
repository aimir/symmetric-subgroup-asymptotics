import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentNormalizer
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBorelPSubgroups
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBorelSoluble

/-! The literal odd-characteristic B-unipotent group is a Sylow subgroup over every finite
field of its defining characteristic. Its actual normalizer is soluble;
no group-order formula or abstract recognition hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices

def unipotentSylow (K : Type) [Field K] [Finite K] (p r : ℕ)
    [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) :
    Sylow p (elementaryRootGroup K (r + 1)) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (unipotent K (r + 1))
    (unipotent_isPGroup K (r + 1) p)
    (fun P hP hPN => pSubgroup_le_unipotent P hP
      (hPN.trans (normalizer_unipotent_le_borel K h2 r)))

@[simp] theorem unipotentSylow_coe (K : Type) [Field K] [Finite K] (p r : ℕ)
    [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) :
    (unipotentSylow K p r h2 : Subgroup (elementaryRootGroup K (r + 1))) =
      unipotent K (r + 1) := rfl

theorem normalizer_unipotent_soluble (K : Type) [Field K] (r : ℕ) (h2 : (2 : K) ≠ 0) :
    IsSolvable (Subgroup.normalizer
      (unipotent K (r + 1) : Set (elementaryRootGroup K (r + 1)))) := by
  letI : IsSolvable (borel K (r + 1)) := borel_soluble K (r + 1)
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion (normalizer_unipotent_le_borel K h2 r))
    (Subgroup.inclusion_injective _)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
