import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveFamilies
import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveMatrixWordValues

/-! A genuine exceptional-fixed positive element with all six ambient
E6 simple leading coordinates equal to one. The higher middle factors
have zero leading coordinates. This includes m=0 and does not identify
the whole fixed positive group or pass to a derived central quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRegularFixedPositive
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourOuterFixedRoot CFSGReeFFourMiddleFixedWords
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourMiddleWordInjective
open CFSGReeFFourPositiveMatrixWordValues CFSGFFourOriginalMiddleWords
open CFSGE6GeckMiddleHigherLeading CFSGE6GeckMiddleFactorInjective
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckWeylWordDegree
open CFSGTwistedE6GeckPositiveTwist CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

private abbrev simplePositive (m : ℕ) (i : Fin 6) (a : Field m) : Positive (Field m) :=
  positiveRoot A hd hs hp ho (Field m) i a

private def outerMatrixWord (m : ℕ) (a : Field m) : Positive (Field m) :=
  simplePositive m 0 a*simplePositive m 5 a*simplePositive m 1 (alpha m a)

private theorem rawHom_outerWord_matrix (m : ℕ) (a : Field m) :
    rawHom (Field m) (outerWord m a)=(outerMatrixWord m a).val := by
  rw [rawHom_outerWord_eq_coordinate]
  simp only [coordinateOuterWord,rootWord,wordUnit,one_mul,inv_one,mul_one]
  rfl

private theorem simple_leading (m : ℕ) (i : Fin 6) (a : Field m) :
    ambientLeading (Field m) (simplePositive m i a)=
      Multiplicative.ofAdd (Pi.single i a : Fin 6→Field m) :=
  leadingHom_positiveRoot A hd hs hp ho (Field m) i a

private theorem outer_leading (m : ℕ) (a : Field m) :
    ambientLeading (Field m) (outerMatrixWord m a)=
      Multiplicative.ofAdd ((Pi.single 0 a : Fin 6→Field m)+Pi.single 5 a+
        Pi.single 1 (alpha m a)) := by
  simp only [outerMatrixWord,map_mul,simple_leading,←_root_.ofAdd_add]

private theorem middle_leading (m : ℕ) (a b c d : Field m) :
    ambientLeading (Field m) (matrixMiddleWord (Field m) a b c d)=
      Multiplicative.ofAdd (((Pi.single 2 a : Fin 6→Field m)+Pi.single 4 a)+Pi.single 3 b) := by
  simp only [matrixMiddleWord,map_mul,higherPositive_leading_one,
    pairedHigherPositive_leading_one,mul_one]
  change leadingHom A hd hs hp ho (Field m)
    (positiveRoot A hd hs hp ho (Field m) 2 a*positiveRoot A hd hs hp ho (Field m) 4 a)*
      leadingHom A hd hs hp ho (Field m) (positiveRoot A hd hs hp ho (Field m) 3 b)=_
  simp only [map_mul,leadingHom_positiveRoot,←_root_.ofAdd_add]

def regularFixed (m : ℕ) : originalModelFixed m :=
  fixedOuterHom m (Multiplicative.ofAdd 1)*fixedMiddleParameter m (1,0)

def regularPositive (m : ℕ) : Positive (Field m) :=
  outerMatrixWord m 1*matrixMiddleWord (Field m) 1 (alpha m 1) 0
    (alpha m 0+1^2*alpha m 1)

theorem rawHom_regularFixed (m : ℕ) :
    rawHom (Field m) (regularFixed m).val=(regularPositive m).val := by
  change rawHom (Field m) (outerWord m 1*fixedMiddleWord m 1 0)=
    (outerMatrixWord m 1).val*(matrixMiddleWord (Field m) 1 (alpha m 1) 0
      (alpha m 0+1^2*alpha m 1)).val
  rw [map_mul,rawHom_outerWord_matrix]
  change (outerMatrixWord m 1).val*
    rawHom (Field m) (middleWord m 1 (alpha m 1) 0 (alpha m 0+1^2*alpha m 1))=_
  rw [rawHom_middleWord]

theorem regularFixed_mem_fixedPositive (m : ℕ) : regularFixed m∈fixedPositive m := by
  change rawHom (Field m) (regularFixed m).val∈Positive (Field m)
  rw [rawHom_regularFixed]
  exact (regularPositive m).property

theorem regularFixed_leading (m : ℕ) (i : Fin 6) :
    leadingCoordinates A hd hs hp ho (Field m) (rawHom (Field m) (regularFixed m).val) i=1 := by
  rw [rawHom_regularFixed]
  change (ambientLeading (Field m) (regularPositive m)).toAdd i=1
  simp only [regularPositive,map_mul,outer_leading,middle_leading]
  change (((Pi.single 0 (1:Field m)+Pi.single 5 1+Pi.single 1 (alpha m 1))+
    (Pi.single 2 1+Pi.single 4 1+Pi.single 3 (alpha m 1)) : Fin 6→Field m) i)=1
  rw [map_one]
  fin_cases i <;> simp

end SymmetricSubgroupAsymptotics.CFSGReeFFourRegularFixedPositive
