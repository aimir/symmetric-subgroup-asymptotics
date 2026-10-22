import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckBasedForm
import SymmetricSubgroupAsymptotics.CFSGGeckSerreImage
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticImageConstraint

/-! Abstract-base staging of the SAME original Serre image constraint.
The actual coordinate bases discharge the simple-root sign using their
proved height formula; no invariant-form or truncation input remains. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageFourthCoefficient
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckBasedForm CFSGNormTwoGeckHeightData
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)
    (hsimple : ∀ i : b.support,rootSign A i= -1)
include hsimple

theorem rational_image_fourth_coefficient_zero (neg : Bool) (i : Fin r)
    (x : CFSG.Models.Chevalley.RationalLie (cartan b s)) :
    CFSGSerreQuadraticMatrix.fieldSecond (realizationData A hs hp b s) ℚ neg i*
      (realizationData A hs hp b s).rational x*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData A hs hp b s) ℚ neg i=0 := by
  have hx := CFSGGeckSerreImage.rationalRepresentation_mem_lieAlgebra b s x
  cases neg
  · rw [rationalSecond_false]
    exact positive_fourth_coefficient_zero A hs hp b hsimple _ hx (s i)
  · rw [rationalSecond_true]
    exact negative_fourth_coefficient_zero A hs hp b hsimple _ hx (s i)

theorem baseChange_image_fourth_coefficient_zero (K : Type*) [CommRing K]
    (neg : Bool) (i : Fin r)
    (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice (cartan b s)) :
    CFSGSerreQuadraticMatrix.fieldSecond (realizationData A hs hp b s) K neg i*
      CFSGSerreQuadraticMatrix.baseChange (realizationData A hs hp b s) K x*
      CFSGSerreQuadraticMatrix.fieldSecond (realizationData A hs hp b s) K neg i=0 :=
  CFSGSerreQuadraticMatrix.baseChange_image_fourth_coefficient_zero
    (realizationData A hs hp b s)
    (rational_image_fourth_coefficient_zero A hs hp b s hsimple) K neg i x

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckImageFourthCoefficient
