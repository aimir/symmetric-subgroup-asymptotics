import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationMenu
import SymmetricSubgroupAsymptotics.CyclicSocleQuotientTools

/-! Exact actual-group transport into the uniform permutation menu.
Every quotient retains the kernel of its actual original epimorphism. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace PreE7FiniteMixedPermutationMenu

theorem quotientSocles_of_equiv {G : Type} [Group G] [Finite G]
    (i : PreE7NonPairActionClass 16) (e : G ≃* preE7NonPairAction 16 i)
    {t : ℕ}
    (hgen : ∀ N : {N : Subgroup G // N.Normal}, SocleNormalGeneratorBound (G ⧸ N.1) t)
    (N : {N : Subgroup (preE7NonPairAction 16 i) // N.Normal}) :
    SocleNormalGeneratorBound (preE7NonPairAction 16 i ⧸ N.1) t := by
  letI := N.2
  let pi := (QuotientGroup.mk' N.1).comp e.toMonoidHom
  have hpi : Function.Surjective pi :=
    (QuotientGroup.mk'_surjective N.1).comp e.surjective
  exact CyclicSocleQuotientTools.socleBound_equiv
    (QuotientGroup.quotientKerEquivOfSurjective pi hpi)
    (hgen ⟨pi.ker, inferInstance⟩)

/-- The actual group chart and proved quotient-socle family are sufficient;
all normal-state and automorphism coefficients are bounded uniformly. -/
def importedRowOfEquiv
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G]
    (i : PreE7NonPairActionClass 16) (e : G ≃* preE7NonPairAction 16 i)
    {t : ℕ} (ht : t ≤ 2)
    (hgen : ∀ N : {N : Subgroup G // N.Normal}, SocleNormalGeneratorBound (G ⧸ N.1) t) :
    DegreeTwoDegreeSixteenImportedRow i :=
  censusFreeImportedRow hMN i ht (quotientSocles_of_equiv i e hgen) hZmud

end PreE7FiniteMixedPermutationMenu
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
