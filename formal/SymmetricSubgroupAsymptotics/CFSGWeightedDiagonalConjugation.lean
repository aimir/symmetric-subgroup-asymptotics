import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

/-! Literal diagonal scaling of homogeneous matrix coefficients. The
support condition is an integer weight equality on the same basis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGWeightedDiagonalConjugation
variable {I K : Type*} [Fintype I] [DecidableEq I] [Field K]

theorem diagonal_mul_of_degree (w : I→ℤ) (q : Kˣ) (c : ℤ) (E : Matrix I I K)
    (hE : ∀i j,w i≠w j+c→E i j=0) :
    Matrix.diagonal (fun i=>(q:K)^(w i))*E=
      ((q:K)^c • E)*Matrix.diagonal (fun i=>(q:K)^(w i)) := by
  ext i j
  rw [Matrix.diagonal_mul,Matrix.mul_diagonal,Matrix.smul_apply,smul_eq_mul]
  by_cases hij : w i=w j+c
  · rw [hij,zpow_add₀ (Units.ne_zero q)]
    ring
  · rw [hE i j hij]
    ring

theorem quadratic_mul_scaled (w : I→ℤ) (q : Kˣ) (c : ℤ) (E D : Matrix I I K)
    (hE : ∀i j,w i≠w j+c→E i j=0)
    (hD : ∀i j,w i≠w j+2*c→D i j=0) (a : K) :
    Matrix.diagonal (fun i=>(q:K)^(w i))*(1+a • E+a^2 • D)=
      (1+(a*(q:K)^c) • E+(a*(q:K)^c)^2 • D)*
        Matrix.diagonal (fun i=>(q:K)^(w i)) := by
  have hE' := diagonal_mul_of_degree w q c E hE
  have hD' := diagonal_mul_of_degree w q (2*c) D hD
  have hc : (q:K)^(2*c)=((q:K)^c)^2 := by
    rw [two_mul,zpow_add₀ (Units.ne_zero q),pow_two]
  simp only [mul_add,mul_one,mul_smul_comm,hE',hD',add_mul,one_mul,smul_mul_assoc,
    smul_smul,hc]
  congr 1 <;> congr 1 <;> ring

end SymmetricSubgroupAsymptotics.CFSGWeightedDiagonalConjugation
