import SymmetricSubgroupAsymptotics.SixPairLocalWreathSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows201To250
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row202OriginalPairFrame
open SemidirectProduct
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SixPairLocalWreathSocles
abbrev points := PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily.pointChart

def codes : Fin 6 → Model :=
  ![1,1,inl (reflection,translation*reflection)*blockSwap,
    firstTranslation,inl (translation*reflection,reflection),firstReflection]
def tops : Fin 6 → Equiv.Perm (Fin 6) := fun i => literalAction (codes i)
private theorem preserves : ∀ i,BinaryPairFrame.Preserves points (row202Generators i) (tops i) := by
  unfold BinaryPairFrame.Preserves
  decide +kernel
def frame : BinaryPairFrame row202Interface.top (Fin 6) :=
  BinaryPairFrame.ofGenerators points row202Generators tops preserves
private theorem swap_word : literalAction blockSwap=tops 2*tops 4 := by decide +kernel

theorem image : frame.top.range=literalAction.range := by
  apply (BinaryPairFrame.ofGenerators_top_range points row202Generators tops preserves).trans
  apply generated_range codes
  · exact Subgroup.subset_closure ⟨3,rfl⟩
  · exact Subgroup.subset_closure ⟨5,rfl⟩
  · rw [swap_word]
    exact (Subgroup.closure (Set.range tops)).mul_mem
      (Subgroup.subset_closure ⟨2,rfl⟩) (Subgroup.subset_closure ⟨4,rfl⟩)
end SymmetricSubgroupAsymptotics.Row202OriginalPairFrame
