import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticSelectedImageConstraint
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticCanonicalRoots

/-! A selected original root acts by literal quadratic conjugation on its
SAME tensor image once that root's fourth coefficient has been proved zero.
Other root actions remain the original divided-power actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I) (K : Type) [Field K]
    (neg : Bool) (i : Fin n)
    (hfour : ∀x : Space A K,fieldSecond D K neg i*baseChange D K x*fieldSecond D K neg i=0)
include hfour

theorem baseChange_rootOperator_selected (t : K) (x : Space A K) :
    baseChange D K (rootOperator A K neg i t x)=
      (canonicalRoot D K neg i t : Matrix I I K)*baseChange D K x*
        (↑((canonicalRoot D K neg i t)⁻¹) : Matrix I I K) := by
  rw [canonicalRoot_val,canonicalRoot_inv_val,rootOperator]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,baseChange_operator]
  simpa only [CFSGIntegralQuadraticRootOperators.exponential,neg_smul,neg_sq,sub_eq_add_neg] using
    CFSGIntegralQuadraticRootOperators.truncated_sum_eq_conjugation K t
      (fieldRoot D K neg i) (fieldSecond D K neg i) (baseChange D K x) (hfour x)

theorem imageRepresentation_root_selected (t : K) (y : (baseChange D K).range) :
    (imageRepresentation D K (modelRoot A K neg i t) y).val=
      (canonicalRoot D K neg i t : Matrix I I K)*y.val*
        (↑((canonicalRoot D K neg i t)⁻¹) : Matrix I I K) := by
  obtain ⟨x,hx⟩ := y.property
  have hy : y=(baseChange D K).rangeRestrict x := Subtype.ext hx.symm
  rw [hy,imageRepresentation_intertwines]
  change baseChange D K (rootOperator A K neg i t x)=_
  exact baseChange_rootOperator_selected D K neg i hfour t x

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
