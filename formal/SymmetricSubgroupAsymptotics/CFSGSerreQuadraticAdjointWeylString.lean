import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootConjugation
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalWeyl
import SymmetricSubgroupAsymptotics.CFSGQuadraticWeylParameterStrings
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction

/-! An opaque adjoint-string calculation on ABSTRACT integral quadratic
data. Actual root-system consumers discharge these four small Lie
identities independently, without unfolding their full coordinate base
through every conjugation operator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString
open CFSGSerreQuadraticMatrix
variable {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

def operator (neg : Bool) (i : Fin r) (a : ℚ) : Module.End ℚ (Matrix I I ℚ) :=
  (CFSGAlgebraConjugationAction.action ℚ (Matrix I I ℚ)
    (canonicalRoot D ℚ neg i a)).toLinearMap

theorem operator_apply (neg : Bool) (i : Fin r) (a : ℚ) (X : Matrix I I ℚ) :
    operator D neg i a X=(canonicalRoot D ℚ neg i a : Matrix I I ℚ)*X*
      (((canonicalRoot D ℚ neg i a)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ) := rfl

theorem weyl_on_pair (i : Fin r) (X Y : Matrix I I ℚ)
    (hEX : ⁅fieldRoot D ℚ false i,X⁆=Y)
    (hEY : ⁅fieldRoot D ℚ false i,Y⁆=0)
    (hFX : ⁅fieldRoot D ℚ true i,X⁆=0)
    (hFY : ⁅fieldRoot D ℚ true i,Y⁆=X) :
    (canonicalWeyl D ℚ i : Matrix I I ℚ)*X*
      (((canonicalWeyl D ℚ i)⁻¹ : (Matrix I I ℚ)ˣ) : Matrix I I ℚ)=Y := by
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
  have hVx (a : ℚ) : operator D true i a X=X := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D true i X
      (by rw [hFX,lie_zero]) a
    simpa only [hFX,smul_zero,add_zero] using hh
  have hVy (a : ℚ) : operator D true i a Y=Y+a • X := by
    rw [operator_apply]
    have hh := canonicalRoot_conjugation_of_double_lie D true i Y
      (by rw [hFY,hFX]) a
    simpa only [hFY] using hh
  have hh := (CFSGQuadraticWeylParameterStrings.word_pair (operator D false i)
    (operator D true i) (1:ℚˣ) X Y hUx hUy hVx hVy).1
  change CFSGAlgebraConjugationAction.action ℚ (Matrix I I ℚ) (canonicalWeyl D ℚ i) X=Y
  rw [canonicalWeyl,map_mul,map_mul]
  change operator D false i 1 (operator D true i (-1) (operator D false i 1 X))=Y
  simpa only [CFSGQuadraticWeylParameterStrings.word,Module.End.mul_apply,
    Units.val_one,inv_one,one_smul] using hh

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString
