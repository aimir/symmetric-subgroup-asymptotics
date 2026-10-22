import SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups

/-! Strict units for opposite literal integer gradings have trivial
intersection, including when coefficient eigenvalues would coincide. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem strict_inf_opposite (weight : I→ℤ) :
    strictUnits (K:=K) weight⊓strictUnits (fun i=> -weight i)=⊥ := by
  apply le_antisymm _ bot_le
  intro u hu
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply Matrix.ext
  intro i j
  by_cases hij : weight i≤weight j
  · exact hu.1 i j hij
  · have hrev : -weight i≤ -weight j := by omega
    exact hu.2 i j hrev

end SymmetricSubgroupAsymptotics.CFSGGradedMatrixSubgroups
