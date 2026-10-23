import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralCoefficients
import SymmetricSubgroupAsymptotics.CFSGSerreCubicMatrixOperators

/-! The ORIGINAL G2 rational map and the literal integral cubic
coefficients form genuine cubic realization data. This gives a map of
the least original integral lattice and every tensor base change;
faithfulness and a projective group comparison are separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralRealization
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckSerreRepresentation
open CFSGGTwoD4GeckIntegralCoefficients CFSGTrialityD4NormTwo
open CFSGTrialityGeckDiagramCovariance CFSGTrialityFixedWeylWords
open CFSGNormTwoGeckTripleRootPolynomial
open CFSGSerreQuadraticMatrix (fieldRoot map_fieldRoot)

private theorem rational_fieldRoot (neg : Bool) (i : Fin 4) :
    fieldRoot rawData ℚ neg i=if neg then d4F i else d4E i := by
  cases neg
  · exact CFSGGeckIntegralMatrices.map_E Base (Index i)
  · exact CFSGGeckIntegralMatrices.map_F Base (Index i)

theorem map_integerRoot (neg : Bool) (i : Fin 2) :
    (Int.castRingHom ℚ).mapMatrix (integerRoot neg i)=if neg then negative i else positive i := by
  have hcast (e : Bool) (j : Fin 4) :
      (Int.castRingHom ℚ).mapMatrix (fieldRoot rawData ℤ e j)=if e then d4F j else d4E j :=
    (map_fieldRoot rawData (Int.castRingHom ℚ) e j).trans (rational_fieldRoot e j)
  cases neg
  · fin_cases i
    · change (Int.castRingHom ℚ).mapMatrix
        (fieldRoot rawData ℤ false 0+fieldRoot rawData ℤ false 2+fieldRoot rawData ℤ false 3)=
          d4E 0+d4E 2+d4E 3
      simp only [map_add,hcast,Bool.false_eq_true,if_false]
    · change (Int.castRingHom ℚ).mapMatrix (fieldRoot rawData ℤ false 1)=d4E 1
      exact hcast false 1
  · fin_cases i
    · change (Int.castRingHom ℚ).mapMatrix
        (fieldRoot rawData ℤ true 0+fieldRoot rawData ℤ true 2+fieldRoot rawData ℤ true 3)=
          d4F 0+d4F 2+d4F 3
      simp only [map_add,hcast,if_true]
    · change (Int.castRingHom ℚ).mapMatrix (fieldRoot rawData ℤ true 1)=d4F 1
      exact hcast true 1

def integerH (i : Fin 2) : IntMat :=
  ![CFSGGeckIntegralMatrices.H Base (Index 0)+CFSGGeckIntegralMatrices.H Base (Index 2)+
    CFSGGeckIntegralMatrices.H Base (Index 3),CFSGGeckIntegralMatrices.H Base (Index 1)] i

theorem map_integerH (i : Fin 2) : (Int.castRingHom ℚ).mapMatrix (integerH i)=cartan i := by
  fin_cases i
  · change (Int.castRingHom ℚ).mapMatrix
      (CFSGGeckIntegralMatrices.H Base (Index 0)+CFSGGeckIntegralMatrices.H Base (Index 2)+
        CFSGGeckIntegralMatrices.H Base (Index 3))=d4H 0+d4H 2+d4H 3
    simp only [map_add,CFSGGeckIntegralMatrices.map_H,d4H,CFSGGeckSerreRepresentation.H]
  · exact CFSGGeckIntegralMatrices.map_H Base (Index 1)

def integerGenerator : CartanMatrix.Generators (Fin 2)→IntMat
  | .H i=>integerH i
  | .E i=>integerRoot false i
  | .F i=>integerRoot true i

theorem integerGenerator_root (neg : Bool) (i : Fin 2) :
    integerGenerator (CFSGSerreSquareZeroMatrix.rootGenerator neg i)=integerRoot neg i := by
  cases neg <;> rfl

def realizationData : CFSGSerreCubicMatrix.Data CartanMatrix.G₂ CFSGGTwoD4GeckGenerators.GeckIndex where
  rational := rationalRepresentation
  integerGenerator := integerGenerator
  integerSecond := integerSecond
  integerThird := integerThird
  generator_cast := by
    intro g
    cases g with
    | H i=>simpa only [integerGenerator,rationalRepresentation_H] using map_integerH i
    | E i=>simpa only [integerGenerator,rationalRepresentation_E,Bool.false_eq_true,if_false] using map_integerRoot false i
    | F i=>simpa only [integerGenerator,rationalRepresentation_F,if_true] using map_integerRoot true i
  root_square neg i := by
    simpa only [integerGenerator_root] using (integer_cubic neg i).1
  root_mul_second neg i := by
    simpa only [integerGenerator_root] using (integer_cubic neg i).2.1
  second_mul_root neg i := by
    simpa only [integerGenerator_root] using (integer_cubic neg i).2.2.1
  root_mul_third neg i := by
    simpa only [integerGenerator_root] using (integer_cubic neg i).2.2.2.1
  third_mul_root neg i := by
    simpa only [integerGenerator_root] using (integer_cubic neg i).2.2.2.2

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckIntegralRealization
