import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenPhysical
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenMatchingClosure
import SymmetricSubgroupAsymptotics.ProductFourPointMatchingKernel
import SymmetricSubgroupAsymptotics.ProductBlockPrimitivePointTransport
import SymmetricSubgroupAsymptotics.ProductBlockKernelPointTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourPhysicalFourByFourSocles
import SymmetricSubgroupAsymptotics.OriginalSixteenPreE7Representative
import SymmetricSubgroupAsymptotics.PreE7FiniteMixedPermutationStructural

/-! Genuine preE7 sources for the original zero16 rows28/29 through their
chosen physical four-by-four systems. No group or normal census. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoZeroSixteenActualSources
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoZeroSixteenFourByFourCharts
open PrimitiveAffineDegreeTwoZeroSixteenMatchingClosure

namespace Row28
open PrimitiveAffineDegreeTwoZeroSixteenPhysical.Row28
local instance : MulAction Original (Fin 4) := chart.topMulAction

theorem original_nonbinary : ¬ IsPGroup 2 Original := by
  intro h
  have hH := h.to_subgroup (MulAction.stabilizer Original (0 : Fin 4))
  apply component_nonbinary
  exact hH.of_surjective
    (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant (0 : Fin 4)).rangeRestrict
    (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant (0 : Fin 4)).rangeRestrict_surjective

def representative : OriginalSixteenPreE7Representative.Chart Original :=
  OriginalSixteenPreE7Representative.choose Original original_nonbinary transitive

def index : PreE7NonPairActionClass 16 := representative.index

def originalEquiv : Original ≃* preE7NonPairAction 16 index :=
  actionConjugacyEquiv representative.conjugator representative.point_conjugacy

theorem point_intertwine (u : Original) (x : Fin 16) :
    representative.conjugator ((u : Equiv.Perm (Fin 16)) x) =
      (originalEquiv u : Equiv.Perm (Fin 16)) (representative.conjugator x) := by
  change representative.conjugator ((u : Equiv.Perm (Fin 16)) x) =
    (representative.conjugator * (u : Equiv.Perm (Fin 16)) *
      representative.conjugator⁻¹) (representative.conjugator x)
  simp [Equiv.Perm.mul_apply]

def actualFrame : ProductBlockFrame (preE7NonPairAction 16 index) (Fin 4) (Fin 4) :=
  chart.ofPointEquiv originalEquiv representative.conjugator point_intertwine

/-- Every quotient retains the actual original representative denominator. -/
theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (N : Subgroup (preE7NonPairAction 16 index)) [N.Normal] :
    SocleNormalGeneratorBound (preE7NonPairAction 16 index ⧸ N) 2 := by
  have hc := ProductBlockFrame.ofPointEquiv_component_preprimitive chart originalEquiv
    representative.conjugator point_intertwine (0 : Fin 4) component_primitive
  have hp := ProductBlockFrame.ofPointEquiv_stabilizer_proper chart originalEquiv
    representative.conjugator point_intertwine (0 : Fin 4) blockStabilizer_proper
  have hK := ProductFourPointMatchingKernel.kernel_binary chart row28MatchingLabel
    row28_matchingLabel_injective row28_matching
  have hk := ProductBlockFrame.ofPointEquiv_kernel_binary chart originalEquiv
    representative.conjugator point_intertwine hK
  exact physical_fourByFour_all_quotientSocle_two actualFrame hc hp socle hMN hk N

def importedRow (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : DegreeTwoDegreeSixteenImportedRow index :=
  PreE7FiniteMixedPermutationMenu.importedRowOfEquiv hMN hZmud index (MulEquiv.refl _)
    (by decide : 2 ≤ 2) (fun N => by
      letI := N.2
      exact quotientSocle socle hMN N.1)

def source (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : PreE7RankTailSourceOrYonedaTopData 16 index :=
  (importedRow socle hMN hZmud).source

end Row28

namespace Row29
open PrimitiveAffineDegreeTwoZeroSixteenPhysical.Row29
local instance : MulAction Original (Fin 4) := chart.topMulAction

theorem original_nonbinary : ¬ IsPGroup 2 Original := by
  intro h
  have hH := h.to_subgroup (MulAction.stabilizer Original (0 : Fin 4))
  apply component_nonbinary
  exact hH.of_surjective
    (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant (0 : Fin 4)).rangeRestrict
    (originalBlockFibreAction chart.blockMap chart.blockMap_equivariant (0 : Fin 4)).rangeRestrict_surjective

def representative : OriginalSixteenPreE7Representative.Chart Original :=
  OriginalSixteenPreE7Representative.choose Original original_nonbinary transitive

def index : PreE7NonPairActionClass 16 := representative.index

def originalEquiv : Original ≃* preE7NonPairAction 16 index :=
  actionConjugacyEquiv representative.conjugator representative.point_conjugacy

theorem point_intertwine (u : Original) (x : Fin 16) :
    representative.conjugator ((u : Equiv.Perm (Fin 16)) x) =
      (originalEquiv u : Equiv.Perm (Fin 16)) (representative.conjugator x) := by
  change representative.conjugator ((u : Equiv.Perm (Fin 16)) x) =
    (representative.conjugator * (u : Equiv.Perm (Fin 16)) *
      representative.conjugator⁻¹) (representative.conjugator x)
  simp [Equiv.Perm.mul_apply]

def actualFrame : ProductBlockFrame (preE7NonPairAction 16 index) (Fin 4) (Fin 4) :=
  chart.ofPointEquiv originalEquiv representative.conjugator point_intertwine

/-- Every quotient retains the actual original representative denominator. -/
theorem quotientSocle
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (N : Subgroup (preE7NonPairAction 16 index)) [N.Normal] :
    SocleNormalGeneratorBound (preE7NonPairAction 16 index ⧸ N) 2 := by
  have hc := ProductBlockFrame.ofPointEquiv_component_preprimitive chart originalEquiv
    representative.conjugator point_intertwine (0 : Fin 4) component_primitive
  have hp := ProductBlockFrame.ofPointEquiv_stabilizer_proper chart originalEquiv
    representative.conjugator point_intertwine (0 : Fin 4) blockStabilizer_proper
  have hK := ProductFourPointMatchingKernel.kernel_binary chart row29MatchingLabel
    row29_matchingLabel_injective row29_matching
  have hk := ProductBlockFrame.ofPointEquiv_kernel_binary chart originalEquiv
    representative.conjugator point_intertwine hK
  exact physical_fourByFour_all_quotientSocle_two actualFrame hc hp socle hMN hk N

def importedRow (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : DegreeTwoDegreeSixteenImportedRow index :=
  PreE7FiniteMixedPermutationMenu.importedRowOfEquiv hMN hZmud index (MulEquiv.refl _)
    (by decide : 2 ≤ 2) (fun N => by
      letI := N.2
      exact quotientSocle socle hMN N.1)

def source (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound)
    (hZmud : ZmudFaithfulCharacterTupleInput) : PreE7RankTailSourceOrYonedaTopData 16 index :=
  (importedRow socle hMN hZmud).source

end Row29
end PrimitiveAffineDegreeTwoZeroSixteenActualSources
end SymmetricSubgroupAsymptotics
end
