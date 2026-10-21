import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction

/-! Full parameter root lines witnessed inside the same literal matrix
unit subgroup. A conjugation coefficient is paid by rescaling the
parameter, never by changing the original subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGActualMatrixRootLines
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]

def HasRootLine (H : Subgroup ((Matrix I I K)ˣ)) (X : Matrix I I K) : Prop :=
  ∀ a : K, ∃ u : (Matrix I I K)ˣ, u ∈ H ∧ (u : Matrix I I K) = 1 + a • X

theorem hasRootLine_smul (H : Subgroup ((Matrix I I K)ˣ)) (X : Matrix I I K)
    (c : K) (hc : c ≠ 0) (hX : HasRootLine H (c • X)) : HasRootLine H X := by
  intro a
  obtain ⟨u, hu, he⟩ := hX (a / c)
  refine ⟨u, hu, ?_⟩
  rw [he, smul_smul, div_mul_cancel₀ a hc]

theorem hasRootLine_conjugate (H : Subgroup ((Matrix I I K)ˣ))
    (W : (Matrix I I K)ˣ) (hW : W ∈ H) (X Y : Matrix I I K) (c : K) (hc : c ≠ 0)
    (hXY : (W : Matrix I I K) * X * (↑(W⁻¹) : Matrix I I K) = c • Y)
    (hX : HasRootLine H X) : HasRootLine H Y := by
  intro a
  obtain ⟨u, hu, he⟩ := hX (a / c)
  refine ⟨W * u * W⁻¹, H.mul_mem (H.mul_mem hW hu) (H.inv_mem hW), ?_⟩
  change (W : Matrix I I K) * (u : Matrix I I K) * (↑(W⁻¹) : Matrix I I K) = _
  rw [he, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    show (W : Matrix I I K) * (↑(W⁻¹) : Matrix I I K) = 1 from W.val_inv,
    Matrix.mul_smul, Matrix.smul_mul, hXY, smul_smul, div_mul_cancel₀ a hc]

end SymmetricSubgroupAsymptotics.CFSGActualMatrixRootLines
