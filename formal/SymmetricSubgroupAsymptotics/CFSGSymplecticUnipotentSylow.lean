import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentNormalizer
import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelPSubgroups
import SymmetricSubgroupAsymptotics.CFSGSylowNormalizerMaximality
import SymmetricSubgroupAsymptotics.CFSGSymplecticBorelSoluble

/-! The literal C-unipotent group is a Sylow subgroup over every finite
field of its defining characteristic. Its actual normalizer is soluble;
no group-order formula or abstract recognition hypothesis is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices

def unipotentSylow (K : Type) [Field K] [Finite K] (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) :
    Sylow p (elementaryRootGroup K (r + 1)) :=
  CFSGSylowNormalizerMaximality.sylowOfNormalizer (unipotent K (r + 1))
    (unipotent_isPGroup K (r + 1) p)
    (fun P hP hPN => pSubgroup_le_unipotent P hP
      (hPN.trans (normalizer_unipotent_le_borel K r hr)))

@[simp] theorem unipotentSylow_coe (K : Type) [Field K] [Finite K] (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) :
    (unipotentSylow K p r hr : Subgroup (elementaryRootGroup K (r + 1))) =
      unipotent K (r + 1) := rfl

theorem normalizer_unipotent_soluble (K : Type) [Field K] (r : ℕ) (hr : 0 < r) :
    IsSolvable (Subgroup.normalizer
      (unipotent K (r + 1) : Set (elementaryRootGroup K (r + 1)))) := by
  letI : IsSolvable (borel K (r + 1)) := borel_soluble K (r + 1)
  exact solvable_of_solvable_injective
    (f := Subgroup.inclusion (normalizer_unipotent_le_borel K r hr))
    (Subgroup.inclusion_injective _)

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
