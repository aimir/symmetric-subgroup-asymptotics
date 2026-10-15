import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop3CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop4CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop5CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop6CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop7CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop8CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop9CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop11CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop12CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop13CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop14CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop15CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop16CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop17CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop18CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop19CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop20CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop21CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop22CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop23CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop24CatalogueBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightSharedTops
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLiteralBinding

/-!
The exact twenty-four canonical degree-eight actions, with independently
checked conjugacies to the original retained actions. The published
catalogue-completeness input is specialized to these displayed canonical
generators. The original-action correspondence below is proved; neither
local-frame bounds nor eligible-top filtering are assumed or concluded.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeEightCanonicalCatalogue

def canonical : Fin 24 → Subgroup (Equiv.Perm (Fin 8)) :=
  ![PrimitiveAffineEightTop1CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop2CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop3CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop4CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop5CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop6CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop7CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop8CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop9CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop10CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop11CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop12CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop13CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop14CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop15CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop16CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop17CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop18CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop19CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop20CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop21CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop22CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop23CatalogueBinding.catalogueAction,
    PrimitiveAffineEightTop24CatalogueBinding.catalogueAction]

def conjugator : Fin 24 → Equiv.Perm (Fin 8) :=
  ![PrimitiveAffineEightTop1CatalogueBinding.conjugator,
    PrimitiveAffineEightTop2CatalogueBinding.conjugator,
    PrimitiveAffineEightTop3CatalogueBinding.conjugator,
    PrimitiveAffineEightTop4CatalogueBinding.conjugator,
    PrimitiveAffineEightTop5CatalogueBinding.conjugator,
    PrimitiveAffineEightTop6CatalogueBinding.conjugator,
    PrimitiveAffineEightTop7CatalogueBinding.conjugator,
    PrimitiveAffineEightTop8CatalogueBinding.conjugator,
    PrimitiveAffineEightTop9CatalogueBinding.conjugator,
    PrimitiveAffineEightTop10CatalogueBinding.conjugator,
    PrimitiveAffineEightTop11CatalogueBinding.conjugator,
    PrimitiveAffineEightTop12CatalogueBinding.conjugator,
    PrimitiveAffineEightTop13CatalogueBinding.conjugator,
    PrimitiveAffineEightTop14CatalogueBinding.conjugator,
    PrimitiveAffineEightTop15CatalogueBinding.conjugator,
    PrimitiveAffineEightTop16CatalogueBinding.conjugator,
    PrimitiveAffineEightTop17CatalogueBinding.conjugator,
    PrimitiveAffineEightTop18CatalogueBinding.conjugator,
    PrimitiveAffineEightTop19CatalogueBinding.conjugator,
    PrimitiveAffineEightTop20CatalogueBinding.conjugator,
    PrimitiveAffineEightTop21CatalogueBinding.conjugator,
    PrimitiveAffineEightTop22CatalogueBinding.conjugator,
    PrimitiveAffineEightTop23CatalogueBinding.conjugator,
    PrimitiveAffineEightTop24CatalogueBinding.conjugator]

/-- Each original action is conjugate to its exact canonical representative. -/
theorem literal_conjugated_eq (j : Fin 24) :
    MulAut.conj (conjugator j) • (DegreeTwoPairedEightSharedTops.interface j).top =
      canonical j := by
  fin_cases j
  · exact PrimitiveAffineEightTop1CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop2CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop3CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop4CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop5CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop6CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop7CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop8CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop9CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop10CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop11CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop12CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop13CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop14CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop15CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop16CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop17CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop18CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop19CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop20CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop21CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop22CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop23CatalogueBinding.literal_conjugated_eq
  · exact PrimitiveAffineEightTop24CatalogueBinding.literal_conjugated_eq

/-- Canonical catalogue completeness is the sole classification input.
Its family is fixed, not an arbitrary project-defined list. -/
abbrev PublishedClassification : Prop :=
  PublishedDegreeEightNonbinaryTopClassification canonical

/-- Transfer canonical completeness through the checked original-action
conjugacies. This is the project-owned correspondence step. -/
theorem originalClassification (published : PublishedClassification) :
    PublishedDegreeEightNonbinaryTopClassification
      (fun j => (DegreeTwoPairedEightSharedTops.interface j).top) := by
  intro T htrans hnonbinary
  obtain ⟨j, g, hg⟩ := published T htrans hnonbinary
  refine ⟨j, (conjugator j)⁻¹ * g, ?_⟩
  rw [map_mul, mul_smul, hg, ← literal_conjugated_eq j, ← mul_smul, ← map_mul]
  simp

noncomputable def literalModels (j : Fin 24) : DegreeEightLiteralTopModel where
  ModelGroup := (DegreeTwoPairedEightSharedTops.interface j).top
  literalAction := (DegreeTwoPairedEightSharedTops.interface j).top
  actionModelEquiv := MulEquiv.refl _

/-- Retain the original block action, point chart and exact group
isomorphism when selecting a canonical degree-eight row. -/
noncomputable def originalTopMatch
    (published : PublishedClassification)
    {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    Σ j : Fin 24, DegreeFourZeroCoreEightLiteralTopMatch block
      (DegreeTwoPairedEightSharedTops.interface j).top :=
  degreeFourZeroCoreLiteralTopMatch_of_published block P literalModels
    (originalClassification published) hr hD hs

end DegreeEightCanonicalCatalogue
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
