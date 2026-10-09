import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow1InducedBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow1TopRegistry

/-!
# Degree-sixteen frame row 1 through the reusable table importer
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineSixteenFrameRow1GeneratedTable

open PrimitiveAffineSixteenFrameRow1InducedBinding

abbrev Source := PrimitiveAffineSixteenFrameRow1TopCertificate.Source
local instance sourceGroup : Group Source :=
  PrimitiveAffineSixteenFrameRow1TopCertificate.group

abbrev LiteralAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure
    (Set.range PrimitiveAffineSixteenFrameRow1TopCertificate.generators)

local instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable
    (PrimitiveAffineSixteenFrameRow1InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineSixteenFrameRow1InducedBinding.inStabilizer
  infer_instance

private theorem sourceStabilizer_fixes_zero : ∀ x : Source,
    x ∈ sourceStabilizer ↔
      ((((PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv x :
        LiteralAction) : Equiv.Perm (Fin 16))) (0 : Fin 16) = 0) := by
  intro x
  change PrimitiveAffineSixteenFrameRow1InducedBinding.inStabilizer x.index ↔ _
  simp only [PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv_apply]
  unfold PrimitiveAffineSixteenFrameRow1InducedBinding.inStabilizer
  native_decide +revert

def sourceStabilizerEquivLiteral :
    sourceStabilizer ≃* MulAction.stabilizer LiteralAction (0 : Fin 16) :=
  GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate
    LiteralAction PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv.symm
    sourceStabilizer sourceStabilizer_fixes_zero

noncomputable def topData : GeneratedSixteenTopData where
  ModelGroup := Source
  literalAction := LiteralAction
  actionModelEquiv :=
    PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral := sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model :=
    GeneratedSixteenTopData.sourceStabilizerEquivLiteralOfFixingPredicate_model
      LiteralAction
      PrimitiveAffineSixteenFrameRow1TopCertificate.originalEquiv.symm
      sourceStabilizer sourceStabilizer_fixes_zero
  GeneratorIndex := Fin 4
  ambient := PrimitiveAffineSixteenFrameRow1TopCertificate.ambient
  ambient_full := PrimitiveAffineSixteenFrameRow1TopCertificate.ambient_full
  representative := representative
  representative_factor := representative_factor
  next := next
  twist := twist
  representative_mul_generator := representative_mul_generator
  classCount := 8
  conjugacyRepresentative :=
    PrimitiveAffineSixteenFrameRow1TopCertificate.representative
  conjugacyCover :=
    PrimitiveAffineSixteenFrameRow1NormalCertificate.topConjugacy.toCardinalCover
  TopIndex := Fin 8
  NormalGeneratorIndex := Fin 4
  stateGenerators :=
    PrimitiveAffineSixteenFrameRow1NormalCertificate.stateGenerators
  topSlots := 0
  topRegistry := PrimitiveAffineSixteenFrameRow1TopRegistry.registry

noncomputable def rowData : GeneratedSixteenRowData topData where
  LocalTarget := LocalTarget
  sourceLocalMap := sourceLocalMap
  sourceLocalMap_surjective := sourceLocalMap_surjective
  local_card := Or.inl localTarget_card
  localRepresentation := localRepresentation
  localRepresentation_injective := localRepresentation_injective
  modelRepresentation :=
    PrimitiveAffineSixteenFrameRow1OddNormalizerModule.representation
  modelRepresentation_generator_formula := representation_generator_formula
  fixedWitness := by
    change FiniteFrameOddNormalizerWitness
      PrimitiveAffineSixteenFrameRow1OddNormalizerModule.representation
    exact PrimitiveAffineSixteenFrameRow1OddNormalizerModule.basisCertificate
      |>.toCoordinateCertificate |>.toOddNormalizerWitness
  slot_sum_le := by
    change 0 + 10 ≤ 10
    omega

noncomputable def table : GeneratedSixteenTopTable topData where
  Row := Unit
  data := fun _ ↦ rowData
  complete := by
    exact (DegreeSixteenLiteralLocalRowCatalogue.singletonOfSourceOrderThree
      topData.literalAction (rowData.literalLocalRow topData)
      (by
        calc
          Nat.card (MulAction.stabilizer topData.literalAction (0 : Fin 16)) =
              Nat.card sourceStabilizer :=
            Nat.card_congr sourceStabilizerEquivLiteral.symm.toEquiv
          _ = 3 := sourceStabilizer_card)
      localTarget_card).complete

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 16)
    (conjugator : Equiv.Perm (Fin 16))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        topData.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 :=
  GeneratedSixteenTopTable.bounds block P topData table pointEquiv conjugator
    hconjugated hr hD

end PrimitiveAffineSixteenFrameRow1GeneratedTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
