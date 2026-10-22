import SymmetricSubgroupAsymptotics.CFSGCubicRootConjugation
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots

/-! Rational adjoint-string conjugation by the ACTUAL canonical root
unit of integral quadratic data. Cubic nilpotence and the half-square
coefficient are discharged by the data's checked integral identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem canonicalRoot_conjugation_of_double_lie (neg : Bool) (i : Fin r)
    (X : Matrix I I ℚ) (hx : ⁅fieldRoot D ℚ neg i,⁅fieldRoot D ℚ neg i,X⁆⁆=0) (t : ℚ) :
    (canonicalRoot D ℚ neg i t : Matrix I I ℚ)*X*
      (((canonicalRoot D ℚ neg i t)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=
      X+t • ⁅fieldRoot D ℚ neg i,X⁆ := by
  let E := fieldRoot D ℚ neg i
  let d := fieldSecond D ℚ neg i
  have hE : E*E=d+d := fieldRoot_square D ℚ neg i
  have hdE : d*E=0 := fieldSecond_mul_root D ℚ neg i
  have hcube : E^3=0 := by
    rw [pow_succ,pow_two,hE,add_mul,hdE,add_zero]
  have hd : (1/2:ℚ) • E^2=d := by
    rw [pow_two,hE,smul_add]
    module
  apply CFSGCubicRootConjugation.conjugate_on_length_two E X hcube hx t
  rw [canonicalRoot_val,show (t^2/2:ℚ)=t^2*(1/2) by ring,←smul_smul,hd]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
