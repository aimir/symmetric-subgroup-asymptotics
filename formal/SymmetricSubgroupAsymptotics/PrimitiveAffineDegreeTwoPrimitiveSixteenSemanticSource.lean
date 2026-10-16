import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationStructural
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenCanonicalCatalogue

/-! Every actual primitive degree-sixteen action has a complete semantic
mixed source. The fixed published catalogue selects one of the twenty-two
already checked original quotient-socle families; the uniform permutation
coefficient theorem handles its full original normal-state sum. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem primitiveSixteen_original_quotientSocle
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (i : PreE7NonPairActionClass 16)
    (hprimitive : MulAction.IsPreprimitive (preE7NonPairAction 16 i) (Fin 16))
    (N : {N : Subgroup (preE7NonPairAction 16 i) // N.Normal}) :
    SocleNormalGeneratorBound (preE7NonPairAction 16 i ⧸ N.1) 2 := by
  obtain ⟨j, g, hg⟩ := PrimitiveSixteenCanonicalCatalogue.originalClassification
    published (preE7NonPairAction 16 i) hprimitive
  let e := PermutationStabilizerTransport.groupEquiv (preE7NonPairAction 16 i)
    (PrimitiveAffineSixteenAllLiteralFrames.top j) (Equiv.refl (Fin 16)) g (by simpa using hg)
  exact PreE7FiniteMixedPermutationMenu.quotientSocles_of_equiv i e.symm
    (PrimitiveAffineSixteenAllLiteralFrames.quotientSocle j) N

/-- No finite row, group-order or menu-coefficient premise remains for
primitive original degree-sixteen actions. -/
def primitiveSixteen_semanticSource
    (published : PrimitiveSixteenCanonicalCatalogue.PublishedClassification)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (i : PreE7NonPairActionClass 16)
    (hprimitive : MulAction.IsPreprimitive (preE7NonPairAction 16 i) (Fin 16)) :
    DegreeTwoDegreeSixteenImportedRow i :=
  PreE7FiniteMixedPermutationMenu.censusFreeImportedRow hMN i (by decide : 2 ≤ 2)
    (primitiveSixteen_original_quotientSocle published i hprimitive) hZmud

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
