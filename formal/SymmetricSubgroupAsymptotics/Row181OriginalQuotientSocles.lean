import SymmetricSubgroupAsymptotics.Row181OriginalPrimitiveComponent
import SymmetricSubgroupAsymptotics.Row181OriginalGraphBinding
import SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtension
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Actual literal row181 all-original-quotient socle bound2. All quotient denominators are the
original normal subgroups of Row182Top. The only literature arguments are
the existing primitive socle and bounded catalogue published inputs. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle_two
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic (Equiv.Perm (Fin 2)) := isCyclic_of_prime_card (p := 2) (by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])
  exact PrimitiveSixKernelCyclicExtension.quotientSocle_two socle catalogue
    blockFrame.top top_surjective (blockFrame.kernelCoordinate 0) coordinate_zero_injective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence) :
    row181Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row181Interface.normalRegistry (fun N => by
      letI := N.2
      exact quotientSocle_two socle catalogue N.1)

end SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel
