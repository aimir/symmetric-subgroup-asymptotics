import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointTriple

/-! Every actual rational quadratic root exponential preserves any Lie
subalgebra containing its root operator. The FULL degree-four polynomial
is used, so no unproved global adjoint truncation is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticLieInvariance
open CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem root_conjugate_mem (L : LieSubalgebra ℚ (Matrix I I ℚ))
    (neg : Bool) (i : Fin r) (he : fieldRoot D ℚ neg i∈L)
    (X : Matrix I I ℚ) (hx : X∈L) (t : ℚ) :
    (canonicalRoot D ℚ neg i t : Matrix I I ℚ)*X*
      (((canonicalRoot D ℚ neg i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)∈L := by
  let E := fieldRoot D ℚ neg i
  let d := fieldSecond D ℚ neg i
  have hpow (k : ℕ) : ((LieAlgebra.ad ℚ (Matrix I I ℚ) E)^k) X∈L := by
    induction k with
    | zero=>simpa only [pow_zero,Module.End.one_apply] using hx
    | succ k ih=>
      rw [pow_succ',Module.End.mul_apply]
      exact L.lie_mem he ih
  have hop (k : ℕ) : CFSGIntegralQuadraticRootOperators.operator ℚ E d k X∈L := by
    rw [←CFSGQuadraticRootDividedPowers.rational_operator E d
      (fieldRoot_square D ℚ neg i) (fieldRoot_mul_second D ℚ neg i)
      (fieldSecond_mul_root D ℚ neg i)]
    change (k.factorial:ℚ)⁻¹ • (((LieAlgebra.ad ℚ (Matrix I I ℚ) E)^k) X)∈L
    exact L.smul_mem _ (hpow k)
  have hsum : (∑k∈Finset.range 5,t^k •
      CFSGIntegralQuadraticRootOperators.operator ℚ E d k X)∈L := by
    apply L.toSubmodule.sum_mem
    intro k _
    exact L.smul_mem _ (hop k)
  have hh := CFSGIntegralQuadraticRootOperators.operator_sum_eq_conjugation ℚ t E d X
  have hu : CFSGIntegralQuadraticRootOperators.exponential ℚ E d t=
      (canonicalRoot D ℚ neg i t : Matrix I I ℚ) := rfl
  have hi : CFSGIntegralQuadraticRootOperators.exponential ℚ E d (-t)=
      (((canonicalRoot D ℚ neg i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ) := by
    rw [canonicalRoot_inverse]
    rfl
  rw [hu,hi] at hh
  rw [←hh]
  exact hsum

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticLieInvariance
