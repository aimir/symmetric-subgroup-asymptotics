import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! Transport of a complete quadratic realization along an equality of
the literal source Cartan matrices. All target matrices are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
variable {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I]

def transportSource (h : A=B) (D : Data A I) : Data B I := by
  cases h
  exact D

theorem transportSource_fourth (h : A=B) (D : Data A I) (K : Type) [CommRing K]
    (hfour : ∀neg i (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice A),
      fieldSecond D K neg i*baseChange D K x*fieldSecond D K neg i=0)
    (neg : Bool) (i : Fin n) (x : K⊗[ℤ]CFSG.Models.Chevalley.integralLattice B) :
    fieldSecond (transportSource h D) K neg i*baseChange (transportSource h D) K x*
      fieldSecond (transportSource h D) K neg i=0 := by
  cases h
  exact hfour neg i x

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
