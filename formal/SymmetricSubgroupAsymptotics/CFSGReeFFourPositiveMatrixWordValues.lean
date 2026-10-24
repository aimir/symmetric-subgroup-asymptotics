import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordInjective
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterFixedRoot

/-! Opaque source-value bridges into one coordinate realization. The
factor expressions contain no cross-owner highestMiddle or middlePair
arguments when used in later conjugation statements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveMatrixWordValues
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGReeFFourFieldParameters CFSGFFourOriginalMiddleWords
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWordInjective
open CFSGReeFFourOuterFixedRoot CFSGE6GeckMiddleHigherLeading
open CFSGE6GeckMiddleFactorInjective CFSGE6GeckMiddleAThreeCollecting
open CFSGNormTwoCoordinateWeylRootMembership CFSGNormTwoGeckWeylWordDegree
open CFSGTwistedE6GeckDiagramCovariance CFSGSerreQuadraticMatrix
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def coordinateMiddleWord (m : ℕ) (a b c d : Field m) :=
  (rootWord A hd hs hp ho (Field m) [] 2 a*rootWord A hd hs hp ho (Field m) [] 4 a)*
    rootWord A hd hs hp ho (Field m) [] 3 b*
      rootWord A hd hs hp ho (Field m) [2,4] 3 d*
        (rootWord A hd hs hp ho (Field m) [3] 2 c*
          rootWord A hd hs hp ho (Field m) [3] 4 c)

def coordinateOuterWord (m : ℕ) (a : Field m) :=
  rootWord A hd hs hp ho (Field m) [] 0 a*rootWord A hd hs hp ho (Field m) [] 5 a*
    rootWord A hd hs hp ho (Field m) [] 1 (alpha m a)

theorem rawHom_middleWord_eq_coordinate (m : ℕ) (a b c d : Field m) :
    rawHom (Field m) (middleWord m a b c d)=coordinateMiddleWord m a b c d := by
  rw [rawHom_middleWord]
  simp only [matrixMiddleWord,Subgroup.coe_mul,higherPositive_val,pairedHigherPositive_val,
    coordinateMiddleWord,rootWord,wordUnit,mul_one,one_mul,inv_one]
  change (canonicalRoot rawData (Field m) false 2 a*canonicalRoot rawData (Field m) false 4 a)*
    canonicalRoot rawData (Field m) false 3 b*
      ((canonicalWeyl rawData (Field m) 2*canonicalWeyl rawData (Field m) 4)*
        canonicalRoot rawData (Field m) false 3 d*
          (canonicalWeyl rawData (Field m) 2*canonicalWeyl rawData (Field m) 4)⁻¹)*
      (canonicalWeyl rawData (Field m) 3*
        (canonicalRoot rawData (Field m) false 2 c*canonicalRoot rawData (Field m) false 4 c)*
          (canonicalWeyl rawData (Field m) 3)⁻¹)=_
  group
  rfl

theorem rawHom_outerWord_eq_coordinate (m : ℕ) (a : Field m) :
    rawHom (Field m) (outerWord m a)=coordinateOuterWord m a := by
  simp only [outerWord,map_mul,rawHom_root,
    CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter,
    coordinateOuterWord,rootWord,wordUnit,mul_one,one_mul,inv_one]
  rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveMatrixWordValues
