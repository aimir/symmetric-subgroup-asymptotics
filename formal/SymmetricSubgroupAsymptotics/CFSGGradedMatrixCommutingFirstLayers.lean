import SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutatorSecondLayer

/-! Commuting actual positive units have commuting genuine first-layer
operators. This uses the exact height-two commutator identity. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutingFirstLayers
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixSubgroups
open CFSGGradedMatrixCommutatorSecondLayer
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem firstLayers_lie_eq_zero (weight : I→ℤ) (u v : (Matrix I I K)ˣ)
    (hu : u∈strictUnits weight) (hv : v∈strictUnits weight) (hc : Commute u v) :
    ⁅firstLayer weight u,firstLayer weight v⁆=0 := by
  have he : u*v*u⁻¹*v⁻¹=1 := by
    rw [hc.eq]
    group
  have hh := commutator_secondLayer weight u v hu hv
  rw [he,Units.val_one,sub_self,map_zero] at hh
  exact hh.symm

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixCommutingFirstLayers
