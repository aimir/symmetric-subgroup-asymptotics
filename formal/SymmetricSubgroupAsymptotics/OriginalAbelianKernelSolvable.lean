import SymmetricSubgroupAsymptotics.OriginalKernelCenter
import Mathlib.GroupTheory.Solvable

/-! Solvability for an actual abelian-kernel chart over a soluble base. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

theorem isSolvable_of_solvable_base {k G B : Type} [CommRing k]
    [Group G] [Group B] [IsSolvable B]
    (pi : G →* B) (A : Rep.{0} k B) (E : OriginalKernelModuleChart pi A) : IsSolvable G := by
  letI : IsSolvable pi.ker := isSolvable_of_comm (fun x y =>
    E.equiv.symm.injective (by rw [map_mul,map_mul,mul_comm]))
  exact solvable_of_ker_le_range pi.ker.subtype pi (by rw [Subgroup.range_subtype])

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
