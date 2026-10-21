import SymmetricSubgroupAsymptotics.CFSGMonomialUnitRootAction

/-! Exact monomial transport of sparse two-entry root matrices. This
generic matrix lemma retains both coefficient ratios; applications to D
prove their equality from the actual natural coordinate weights. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction
open Matrix CFSGTypeAMonomialMatrices CFSGTypeAMonomialRootAction
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem conjugation_single (W : (Matrix I I K)ˣ) (σ : Equiv.Perm I) (d : I → K)
    (hW : (W : Matrix I I K) = monomial σ d) (a b : I) (t : K)
    (hb : d (σ.symm b) ≠ 0) :
    (W : Matrix I I K) * Matrix.single a b t * (↑W⁻¹ : Matrix I I K) =
      Matrix.single (σ.symm a) (σ.symm b) (d (σ.symm a) * t / d (σ.symm b)) := by
  have hm := monomial_mul_transvection σ d a b t hb
  rw [← hW] at hm
  have hc := congrArg (fun A : Matrix I I K => A * (↑W⁻¹ : Matrix I I K)) hm
  have hh : (1 : Matrix I I K) +
      (W : Matrix I I K) * Matrix.single a b t * (↑W⁻¹ : Matrix I I K) =
      1 + Matrix.single (σ.symm a) (σ.symm b) (d (σ.symm a) * t / d (σ.symm b)) := by
    simpa only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul,
      mul_assoc, Units.mul_inv] using hc
  exact add_left_cancel hh

theorem conjugation_two_entry (W : (Matrix I I K)ˣ) (σ : Equiv.Perm I) (d : I → K)
    (hW : (W : Matrix I I K) = monomial σ d) (a b c e : I) (t : K)
    (hb : d (σ.symm b) ≠ 0) (he : d (σ.symm e) ≠ 0) :
    (W : Matrix I I K) * (1 + Matrix.single a b t - Matrix.single c e t) *
      (↑W⁻¹ : Matrix I I K) =
      1 + Matrix.single (σ.symm a) (σ.symm b) (d (σ.symm a) * t / d (σ.symm b)) -
        Matrix.single (σ.symm c) (σ.symm e) (d (σ.symm c) * t / d (σ.symm e)) := by
  simp only [mul_sub, sub_mul, mul_add, add_mul, mul_one, Units.mul_inv,
    conjugation_single W σ d hW a b t hb, conjugation_single W σ d hW c e t he]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction
