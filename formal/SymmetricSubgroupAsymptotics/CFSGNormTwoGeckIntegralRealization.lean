import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralQuadratic
import SymmetricSubgroupAsymptotics.CFSGGeckSerreRepresentation
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticMatrixOperators

/-! Installs the actual norm-two Geck matrices into the shared integral
quadratic realization. Every integral polynomial identity is discharged
by the proved single-entry halves, for both signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralQuadratic
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def integerGenerator : CartanMatrix.Generators (Fin r)→CFSGGeckIntegralMatrices.IntegralTarget b
  | .H i=>CFSGGeckIntegralMatrices.H b (s i)
  | .E i=>CFSGGeckIntegralMatrices.E b (s i)
  | .F i=>CFSGGeckIntegralMatrices.F b (s i)

def integerSecond (neg : Bool) (i : Fin r) : CFSGGeckIntegralMatrices.IntegralTarget b :=
  if neg then negativeSecond A hs hp b (s i) else positiveSecond A hs hp b (s i)

def realizationData : CFSGSerreQuadraticMatrix.Data (cartan b s) (b.support⊕Roots A) where
  rational := rationalRepresentation b s
  integerGenerator := integerGenerator A hs hp b s
  integerSecond := integerSecond A hs hp b s
  generator_cast := by
    intro g
    cases g with
    | H i=>
      simpa only [integerGenerator,rationalRepresentation_H,CFSGGeckSerreRepresentation.H]
        using CFSGGeckIntegralMatrices.map_H b (s i)
    | E i=>
      simpa only [integerGenerator,rationalRepresentation_E,CFSGGeckSerreRepresentation.E]
        using CFSGGeckIntegralMatrices.map_E b (s i)
    | F i=>
      simpa only [integerGenerator,rationalRepresentation_F,CFSGGeckSerreRepresentation.F]
        using CFSGGeckIntegralMatrices.map_F b (s i)
  root_square := by
    intro neg i
    cases neg
    · exact positive_square A hs hp b (s i)
    · exact negative_square A hs hp b (s i)
  root_mul_second := by
    intro neg i
    cases neg
    · exact positive_mul_second A hs hp b (s i)
    · exact negative_mul_second A hs hp b (s i)
  second_mul_root := by
    intro neg i
    cases neg
    · exact second_mul_positive A hs hp b (s i)
    · exact second_mul_negative A hs hp b (s i)
  second_square := by
    intro neg i
    cases neg
    · exact positiveSecond_square A hs hp b (s i)
    · exact negativeSecond_square A hs hp b (s i)

theorem rationalSecond_false (i : Fin r) :
    CFSGSerreQuadraticMatrix.fieldSecond (realizationData A hs hp b s) ℚ false i=
      CFSGNormTwoGeckQuadratic.secondMatrix A hs hp b (s i) :=
  map_positiveSecond A hs hp b (s i)

theorem rationalSecond_true (i : Fin r) :
    CFSGSerreQuadraticMatrix.fieldSecond (realizationData A hs hp b s) ℚ true i=
      CFSGNormTwoGeckNegative.negativeSecondMatrix A hs hp b (s i) :=
  map_negativeSecond A hs hp b (s i)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization
