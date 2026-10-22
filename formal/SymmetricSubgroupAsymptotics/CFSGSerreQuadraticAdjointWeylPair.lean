import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString

/-! The second column of the same abstract rational adjoint string.
Together with weyl_on_pair this gives an exact signed interchange,
without recognizing any matrix from its homogeneous degree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylPair
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticAdjointWeylString
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem weyl_on_second (i : Fin r) (X Y : Matrix I I ℚ)
    (hEX : ⁅fieldRoot D ℚ false i,X⁆=Y)
    (hEY : ⁅fieldRoot D ℚ false i,Y⁆=0)
    (hFX : ⁅fieldRoot D ℚ true i,X⁆=0)
    (hFY : ⁅fieldRoot D ℚ true i,Y⁆=X) :
    (canonicalWeyl D ℚ i : Matrix I I ℚ)*Y*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)= -X := by
  have hUx (a : ℚ) : operator D false i a X=X+a • Y := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D false i X
      (by rw [hEX,hEY]) a
    simpa only [hEX] using hh
  have hUy (a : ℚ) : operator D false i a Y=Y := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D false i Y
      (by rw [hEY,lie_zero]) a
    simpa only [hEY,smul_zero,add_zero] using hh
  have hVy (a : ℚ) : operator D true i a Y=Y+a • X := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D true i Y
      (by rw [hFY,hFX]) a
    simpa only [hFY] using hh
  change CFSGAlgebraConjugationAction.action ℚ (Matrix I I ℚ)
    (canonicalWeyl D ℚ i) Y= -X
  rw [canonicalWeyl,map_mul,map_mul]
  change operator D false i 1 (operator D true i (-1) (operator D false i 1 Y))= -X
  rw [hUy,hVy]
  simp only [map_add,map_smul,hUy,hUx]
  module

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylPair
