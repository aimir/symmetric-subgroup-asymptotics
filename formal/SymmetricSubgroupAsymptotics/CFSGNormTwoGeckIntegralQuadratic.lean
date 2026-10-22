import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckNegative
import SymmetricSubgroupAsymptotics.CFSGGeckIntegralOpposition
import SymmetricSubgroupAsymptotics.CFSGSerreSquareZeroMatrixData

/-! Actual integral halves and polynomial identities for both signs of a
norm-two Geck root. Rational casting is injective; no division is performed
in the integral lattice or in a later characteristic-two field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralQuadratic
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckQuadratic CFSGNormTwoGeckTruncation CFSGNormTwoGeckNegative
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def positiveSecond (i : b.support) : CFSGGeckIntegralMatrices.IntegralTarget b :=
  Matrix.single (Sum.inr (i:Roots A)) (Sum.inr (negativeIndex A hs hp i)) 1

def negativeSecond (i : b.support) : CFSGGeckIntegralMatrices.IntegralTarget b :=
  CFSGGeckIntegralMatrices.Omega b*positiveSecond A hs hp b i*CFSGGeckIntegralMatrices.Omega b

theorem map_positiveSecond (i : b.support) :
    (Int.castRingHom ℚ).mapMatrix (positiveSecond A hs hp b i)=secondMatrix A hs hp b i := by
  ext j k
  simp [positiveSecond,secondMatrix,Matrix.single_apply]

theorem map_negativeSecond (i : b.support) :
    (Int.castRingHom ℚ).mapMatrix (negativeSecond A hs hp b i)=negativeSecondMatrix A hs hp b i := by
  rw [negativeSecond,CFSGGeckIntegralMatrices.map_opposition,map_positiveSecond]
  rfl

theorem positive_square (i : b.support) :
    CFSGGeckIntegralMatrices.E b i*CFSGGeckIntegralMatrices.E b i=
      positiveSecond A hs hp b i+positiveSecond A hs hp b i := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix (_+_)
  rw [map_mul,map_add,CFSGGeckIntegralMatrices.map_E,map_positiveSecond]
  simpa only [pow_two,two_smul] using E_square A hs hp b i

theorem positive_mul_second (i : b.support) :
    CFSGGeckIntegralMatrices.E b i*positiveSecond A hs hp b i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
  rw [map_mul,map_zero,CFSGGeckIntegralMatrices.map_E,map_positiveSecond]
  exact E_mul_second A hs hp b i

theorem second_mul_positive (i : b.support) :
    positiveSecond A hs hp b i*CFSGGeckIntegralMatrices.E b i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
  rw [map_mul,map_zero,CFSGGeckIntegralMatrices.map_E,map_positiveSecond]
  exact second_mul_E A hs hp b i

theorem positiveSecond_square (i : b.support) :
    positiveSecond A hs hp b i*positiveSecond A hs hp b i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
  rw [map_mul,map_zero,map_positiveSecond]
  simpa only [pow_two] using second_square A hs hp b i

theorem negative_square (i : b.support) :
    CFSGGeckIntegralMatrices.F b i*CFSGGeckIntegralMatrices.F b i=
      negativeSecond A hs hp b i+negativeSecond A hs hp b i := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix (_+_)
  rw [map_mul,map_add,CFSGGeckIntegralMatrices.map_F,map_negativeSecond]
  simpa only [pow_two,two_smul] using F_square A hs hp b i

theorem negative_mul_second (i : b.support) :
    CFSGGeckIntegralMatrices.F b i*negativeSecond A hs hp b i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
  rw [map_mul,map_zero,CFSGGeckIntegralMatrices.map_F,map_negativeSecond]
  exact F_mul_second A hs hp b i

theorem second_mul_negative (i : b.support) :
    negativeSecond A hs hp b i*CFSGGeckIntegralMatrices.F b i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
  rw [map_mul,map_zero,CFSGGeckIntegralMatrices.map_F,map_negativeSecond]
  exact second_mul_F A hs hp b i

theorem negativeSecond_square (i : b.support) :
    negativeSecond A hs hp b i*negativeSecond A hs hp b i=0 := by
  apply CFSGSerreSquareZeroMatrix.integerCast_injective (b.support⊕Roots A)
  change (Int.castRingHom ℚ).mapMatrix (_*_)=(Int.castRingHom ℚ).mapMatrix 0
  rw [map_mul,map_zero,map_negativeSecond]
  simpa only [pow_two] using CFSGNormTwoGeckNegative.negativeSecond_square A hs hp b i

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralQuadratic
