import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourCoordinatePositiveFamilies

/-! Thin transport of the selected positive products to the same
original Model, using only opaque source-value identities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveFamilies
open CFSGReeFFourFieldParameters CFSGFFourOriginalMiddleWords
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourPositiveMatrixWordValues CFSGReeFFourCoordinatePositiveFamilies
open CFSGReeFFourMiddleFixedWords CFSGReeFFourOuterFixedRoot
open CFSGTwistedE6GeckPositiveTwist

theorem rawHom_outer_conjugate_middleWord_mem_positive (m : ℕ)
    (a b c d : Field m) :
    rawHom (Field m) (outerRelativeWeyl m*middleWord m a b c d*
      (outerRelativeWeyl m)⁻¹)∈Positive (Field m) := by
  simp only [map_mul,map_inv,rawHom_outerRelativeWeyl,rawHom_middleWord_eq_coordinate]
  exact coordinateMiddleWord_outer_conjugate_mem m a b c d

theorem rawHom_middle_conjugate_outerWord_mem_positive (m : ℕ) (a : Field m) :
    rawHom (Field m) (middleRelativeWeyl m*outerWord m a*(middleRelativeWeyl m)⁻¹)∈
      Positive (Field m) := by
  simp only [map_mul,map_inv,rawHom_middleRelativeWeyl,rawHom_outerWord_eq_coordinate]
  exact coordinateOuterWord_middle_conjugate_mem m a

end SymmetricSubgroupAsymptotics.CFSGReeFFourRelativePositiveFamilies
