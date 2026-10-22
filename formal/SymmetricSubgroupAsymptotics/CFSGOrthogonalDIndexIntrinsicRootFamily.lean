import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylowCenterFamily
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPlaneRootLine
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSylow

/-! Every abstract automorphism of the SAME actual D elementary group
preserves its whole conjugate highest-root subgroup family. The line is
identified with the centre of the proved literal Sylow subgroup, not
with an assumed natural-action recognition predicate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexIntrinsicRootFamily
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexUnipotent
open CFSGOrthogonalDIndexSylowCenterFamily CFSGOrthogonalDIndexPlaneRootLine
open CFSGOrthogonalDIndexSylow
variable (K : Type) [Field K] [Finite K]

theorem automorphism_maps_conjugateRootLine (p : ℕ) [Fact p.Prime] [CharP K p]
    (s : ℕ) (f : MulAut (elementaryRootGroup K (s + 4)))
    (g : elementaryRootGroup K (s + 4)) :
    ∃ h : elementaryRootGroup K (s + 4),
      (conjugateRootLine K s g).map f.toMonoidHom = conjugateRootLine K s h := by
  obtain ⟨h, hh⟩ := exists_inner_centerImage_map p (unipotentSylow K s p)
    (f * MulAut.conj g)
  change (highestRootLine K s).map (f * MulAut.conj g).toMonoidHom =
    (highestRootLine K s).map (MulAut.conj h).toMonoidHom at hh
  refine ⟨h, ?_⟩
  change ((highestRootLine K s).map (MulAut.conj g).toMonoidHom).map f.toMonoidHom = _
  rw [Subgroup.map_map]
  exact hh

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexIntrinsicRootFamily
