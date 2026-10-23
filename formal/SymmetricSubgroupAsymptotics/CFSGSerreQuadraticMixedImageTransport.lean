import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! Mixed original divided-power compositions descend through the SAME
integral representation and every tensor base change. The rational
hypothesis is an adjoint-word identity, subsequently discharged by the
actual generated Geck Lie algebra. No factorial is inverted after
integral transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
open CFSG.Models.Chevalley
variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℤ}
    {I : Type*} [Fintype I] [DecidableEq I] (D : Data A I)

theorem rational_mixed_dividedPower_zero (neg neg' : Bool) (i j : Fin n) (k l : ℕ)
    (hzero : ∀x : RationalLie A,
      (LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg i)^k)
        ((LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg' j)^l) (D.rational x))=0)
    (x : RationalLie A) :
    D.rational (dividedPower A neg i k (dividedPower A neg' j l x))=0 := by
  rw [CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector,
    CFSGSerreIntegralRepresentation.dividedPower_intertwines,rational_rootVector]
  simp only [CFSGSquareZeroDividedPowers.operator,LinearMap.smul_apply,map_smul,
    hzero,smul_zero]

theorem integral_mixed_operator_zero (neg neg' : Bool) (i j : Fin n) (k l : ℕ)
    (hzero : ∀x : RationalLie A,
      (LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg i)^k)
        ((LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg' j)^l) (D.rational x))=0)
    (x : integralLattice A) :
    integralRepresentation D (integralOperator A neg i k (integralOperator A neg' j l x))=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective I
  rw [integralRepresentation_cast,map_zero]
  change D.rational (dividedPower A neg i k (dividedPower A neg' j l x.val))=0
  exact rational_mixed_dividedPower_zero D neg neg' i j k l hzero x.val

theorem baseChange_mixed_operator_zero (K : Type*) [CommRing K]
    (neg neg' : Bool) (i j : Fin n) (k l : ℕ)
    (hzero : ∀x : RationalLie A,
      (LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg i)^k)
        ((LieAlgebra.ad ℚ (Matrix I I ℚ) (fieldRoot D ℚ neg' j)^l) (D.rational x))=0)
    (x : K⊗[ℤ]integralLattice A) :
    baseChange D K ((integralOperator A neg i k).baseChange K
      ((integralOperator A neg' j l).baseChange K x))=0 := by
  induction x using TensorProduct.induction_on with
  | zero=>simp only [map_zero]
  | tmul a x=>
    rw [LinearMap.baseChange_tmul,LinearMap.baseChange_tmul,baseChange_tmul,
      integral_mixed_operator_zero D neg neg' i j k l hzero,map_zero,smul_zero]
  | add x y hx hy=>simp only [map_add,hx,hy,add_zero]

end SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrix
