import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOppositionLattice
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! The bounded opposition word is an actual exceptional-fixed element
of the original F4 Model. Its raw value is the same word certified on
the lattice, without a fixed-point quotient lift or a whole-U claim. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOpposition
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGFFourOriginalMiddleWords
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourRelativeOppositionLattice CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylWordAlgebra CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def relativeOpposition (m : ℕ) : Model CartanMatrix.F₄ (Field m) :=
  (outerRelativeWeyl m*middleRelativeWeyl m)^4

theorem relativeOpposition_fixed (m : ℕ) :
    reeAutomorphism m (relativeOpposition m)=relativeOpposition m := by
  simp only [relativeOpposition,map_pow,map_mul,outerRelativeWeyl_fixed,middleRelativeWeyl_fixed]

theorem rawHom_relativeOpposition (m : ℕ) :
    rawHom (Field m) (relativeOpposition m)=
      wordUnit A hs hp E6Base E6Index (Field m) relativeOppositionWord := by
  simp only [relativeOpposition,map_pow,map_mul,rawHom_outerRelativeWeyl,rawHom_middleRelativeWeyl]
  have hblock := wordUnit_append A hs hp E6Base E6Index (Field m)
    [0,5,1] [2,4,3,2,4,3]
  change wordUnit A hs hp E6Base E6Index (Field m) relativeCoxeterWord=
    wordUnit A hs hp E6Base E6Index (Field m) [0,5,1]*
      wordUnit A hs hp E6Base E6Index (Field m) [2,4,3,2,4,3] at hblock
  rw [←hblock,relativeOppositionWord]
  simp only [wordUnit_append,pow_succ,pow_zero,one_mul,mul_one,mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOpposition
