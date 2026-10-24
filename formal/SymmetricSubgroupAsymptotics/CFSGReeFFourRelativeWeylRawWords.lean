import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeSimpleWeyl
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordDegree

/-! Literal E6 word values of the two exceptional-fixed original F4
relative Weyl elements. These equalities use the faithful original map,
without a claim about the size of a relative Weyl group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
open CFSGFFourOriginalMiddleWords CFSGReeFFourRelativeSimpleWeyl
open CFSGFFourE6RelativeWords CFSGTwistedE6GeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGNormTwoGeckWeylWordDegree CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGReeFFourFieldParameters
local notation "F" => CFSGFFourSerreMatrices.realizationData
local notation "R" => CFSGTwistedE6GeckDiagramCovariance.rawData
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem rawHom_outerRelativeWeyl (m : ℕ) :
    rawHom (Field m) (outerRelativeWeyl m)=
      wordUnit A hs hp E6Base E6Index (Field m) [0,5,1] := by
  have h0 := foldedWeyl_eq_orbitWord (Field m) 0
  have h3 := foldedWeyl_eq_orbitWord (Field m) 3
  change canonicalWeyl F (Field m) 0=canonicalWord R (Field m) [0,5] at h0
  change canonicalWeyl F (Field m) 3=canonicalWord R (Field m) [1] at h3
  simp only [outerRelativeWeyl,map_mul,rawHom_weyl,h0,h3,canonicalWord,wordUnit,mul_one]
  group

theorem rawHom_middleRelativeWeyl (m : ℕ) :
    rawHom (Field m) (middleRelativeWeyl m)=
      wordUnit A hs hp E6Base E6Index (Field m) [2,4,3,2,4,3] := by
  have h1 := foldedWeyl_eq_orbitWord (Field m) 1
  have h2 := foldedWeyl_eq_orbitWord (Field m) 2
  change canonicalWeyl F (Field m) 1=canonicalWord R (Field m) [2,4] at h1
  change canonicalWeyl F (Field m) 2=canonicalWord R (Field m) [3] at h2
  simp only [middleRelativeWeyl,map_mul,rawHom_weyl,h1,h2,canonicalWord,wordUnit,mul_one]
  group

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
