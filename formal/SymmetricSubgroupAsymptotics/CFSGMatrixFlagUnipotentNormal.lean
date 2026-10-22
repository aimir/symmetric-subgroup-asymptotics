import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups

/-! A literal unitriangular group is normalized by the same literal
upper-triangular group, in any explicitly indexed complete flag. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K] {m : ℕ}

theorem borelUnits_le_normalizer_unipotentUnits (e : I ≃ Fin m) :
    borelUnits (K := K) e ≤ Subgroup.normalizer
      (unipotentUnits (K := K) e : Set ((Matrix I I K)ˣ)) := by
  apply Subgroup.le_normalizer_iff.mpr
  intro g hg u hu
  have hginv := (borelUnits (K := K) e).inv_mem hg
  change (((g : Matrix I I K) * (u : Matrix I I K)) * (↑(g⁻¹) : Matrix I I K)).BlockTriangular e ∧ _
  refine ⟨(hg.mul hu.1).mul hginv, ?_⟩
  intro i
  change (((g : Matrix I I K) * (u : Matrix I I K)) * (↑(g⁻¹) : Matrix I I K)) i i = 1
  rw [upper_diag_mul e (hg.mul hu.1) hginv, upper_diag_mul e hg hu.1,
    hu.2 i, mul_one]
  have he := congrArg (fun A : Matrix I I K => A i i) (Units.mul_inv g)
  dsimp only at he
  rwa [upper_diag_mul e hg hginv, Matrix.one_apply_eq] at he

end SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
