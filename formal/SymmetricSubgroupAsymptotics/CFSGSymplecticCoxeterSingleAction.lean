import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterMonomial
import SymmetricSubgroupAsymptotics.CFSGTypeAMonomialRootAction

/-! Signed conjugation of every literal matrix coordinate by the actual
Coxeter word. This applies in odd characteristic too; no signs are
silently replaced by one. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGTypeAMonomialRootAction

theorem coxeter_single_conjugation (K : Type) [Field K] (r : ℕ) (i j : Index (r + 1)) :
    ((coxeterWeyl K r).val : Mat K (r + 1)) * Matrix.single i j 1 *
      (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) =
      (coxeterSign K r i / coxeterSign K r j) •
        Matrix.single (coxeterCycle r i) (coxeterCycle r j) 1 := by
  have hm := monomial_mul_transvection (F := K) (coxeterCycle r).symm
    (coxeterSign K r ∘ (coxeterCycle r).symm) i j 1
    (by simpa only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply]
      using coxeterSign_ne_zero K r j)
  rw [← coxeterWeyl_monomial K r] at hm
  simp only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply, mul_one] at hm
  have hc := congrArg (fun A : Mat K (r + 1) =>
    A * (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1))) hm
  have hh : (1 : Mat K (r + 1)) +
      ((coxeterWeyl K r).val : Mat K (r + 1)) * Matrix.single i j 1 *
        (↑((coxeterWeyl K r).val⁻¹) : Mat K (r + 1)) =
      1 + Matrix.single (coxeterCycle r i) (coxeterCycle r j)
        (coxeterSign K r i / coxeterSign K r j) := by
    simpa only [Matrix.transvection, mul_add, add_mul, mul_one, one_mul,
      mul_assoc, Units.mul_inv] using hc
  have he := add_left_cancel hh
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using he

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
