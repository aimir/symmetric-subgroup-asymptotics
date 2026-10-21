import SymmetricSubgroupAsymptotics.Row181OriginalQuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveDegreeSixActualNormalConsumers
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtensionDirectConsumers

/-! Isolated direct six-point and coarse twelve-point consumer route. Original records,
finite index sets and all certificate declarations are imported unchanged. -/
set_option autoImplicit false

noncomputable section

namespace SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel

namespace DirectConsumers

open Non2UnipotentPrefixFiniteMenu

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open DegreeTwoTwelvePairFiniteCatalogue

theorem quotientSocle_two
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (N : Subgroup Original) [N.Normal] : SocleNormalGeneratorBound (Original ⧸ N) 2 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic (Equiv.Perm (Fin 2)) := isCyclic_of_prime_card (p := 2) (by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm])
  exact _root_.SymmetricSubgroupAsymptotics.PrimitiveSixKernelCyclicExtension.DirectConsumers.quotientSocle_two socle catalogue
    blockFrame.top top_surjective (blockFrame.kernelCoordinate 0) coordinate_zero_injective N

def quotientFamily
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds) :
    row181Interface.normalRegistry.QuotientSocleGeneratorFamily 2 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row181Interface.normalRegistry (fun N => by
      letI := N.2
      exact _root_.SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel.DirectConsumers.quotientSocle_two socle catalogue N.1)

end DirectConsumers

end SymmetricSubgroupAsymptotics.Row181OriginalBlockKernel

