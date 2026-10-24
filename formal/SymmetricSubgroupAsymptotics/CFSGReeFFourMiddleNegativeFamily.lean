import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeCoordinateFamily
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositeGenerationAssembly

/-! The actual middle fixed subgroup is carried into the actual negative
preimage by the fixed middle Weyl element. This bounded statement uses
no membership of that Weyl element in the unipotent-generated subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeFamily
open CFSGReeFFourFieldParameters CFSGFFourOriginalMiddleWords
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourRelativeWeylRawWords
open CFSGReeFFourPositiveMatrixWordValues CFSGReeFFourMiddleNegativeCoordinateFamily
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleFixedSubgroup
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourOppositeGenerationAssembly
open CFSGTwistedE6GeckPositiveTwist

theorem rawHom_middle_conjugate_middleWord_mem_negative (m : ℕ)
    (a b c d : Field m) :
    rawHom (Field m) (middleRelativeWeyl m*middleWord m a b c d*
      (middleRelativeWeyl m)⁻¹)∈Negative (Field m) := by
  simp only [map_mul,map_inv,rawHom_middleRelativeWeyl,rawHom_middleWord_eq_coordinate]
  exact coordinateMiddleWord_middle_conjugate_mem_negative m a b c d

theorem middle_conjugate_middleFixedSubgroup_le (m : ℕ) :
    (middleFixedSubgroup m).map (MulAut.conj (fixedMiddleWeyl m)).toMonoidHom≤
      fixedNegative m := by
  rintro g ⟨x,hx,rfl⟩
  obtain ⟨a,b,c,d,hx⟩ := hx
  change rawHom (Field m) (middleRelativeWeyl m*x.val*(middleRelativeWeyl m)⁻¹)∈
    Negative (Field m)
  rw [←hx]
  exact rawHom_middle_conjugate_middleWord_mem_negative m a b c d

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleNegativeFamily
