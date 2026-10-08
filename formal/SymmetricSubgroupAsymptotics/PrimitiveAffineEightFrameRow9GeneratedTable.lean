import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameGeneratedRowTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9LiteralLocalRow
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9TopRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ModuleRegistry

/-!
# Row 9 through the reusable generated top-table API

This is the regression instance for the grouped finite-frame importer.  It
contains only the checked row data.  The literal affine transport is supplied
entirely by `GeneratedTopTable.bounds`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightFrameRow9GeneratedTable

open PrimitiveAffineEightFrameRow9InducedBinding

local instance sourceGroup : Group Source :=
  PrimitiveAffineEightFrameRow9TopCertificate.group

local instance sourceStabilizerMembership (x : Source) :
    Decidable (x ∈ sourceStabilizer) := by
  change Decidable
    (PrimitiveAffineEightFrameRow9InducedBinding.inStabilizer x.index)
  unfold PrimitiveAffineEightFrameRow9InducedBinding.inStabilizer
  infer_instance

/-- All data shared above row 9's order-192 top. -/
noncomputable def topData : GeneratedTopData where
  ModelGroup := Source
  literalAction := PrimitiveAffineEightFrameRow9LiteralLocalRow.LiteralAction
  actionModelEquiv :=
    PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.symm
  sourceStabilizer := sourceStabilizer
  sourceStabilizerEquivLiteral :=
    PrimitiveAffineEightFrameRow9LiteralLocalRow.sourceStabilizerEquivLiteral
  sourceStabilizerEquivLiteral_model := by
    intro h
    exact PrimitiveAffineEightFrameRow9TopCertificate.originalEquiv.symm_apply_apply h.1
  GeneratorIndex := Fin 7
  ambient := PrimitiveAffineEightFrameRow9TopCertificate.ambient
  ambient_full := PrimitiveAffineEightFrameRow9TopCertificate.ambient_full
  representative := representative
  representative_factor := representative_factor
  next := next
  twist := twist
  representative_mul_generator := representative_mul_generator
  classCount := 14
  conjugacyRepresentative :=
    PrimitiveAffineEightFrameRow9TopCertificate.representative
  conjugacyCover :=
    PrimitiveAffineEightFrameRow9TopCertificate.conjugacy.toCardinalCover
  TopIndex := Fin 10
  NormalGeneratorIndex := Fin 6
  stateGenerators :=
    PrimitiveAffineEightFrameRow9NormalCertificate.stateGenerators
  topRegistry := PrimitiveAffineEightFrameRow9TopRegistry.registry

/-- The row-varying local and module certificate. -/
noncomputable def rowData : GeneratedRowData topData where
  LocalTarget := LocalTarget
  sourceLocalMap := sourceLocalMap
  sourceLocalMap_surjective := sourceLocalMap_surjective
  local_card := Or.inr localTarget_card
  localRepresentation := localRepresentation
  localRepresentation_injective := localRepresentation_injective
  modelRepresentation :=
    PrimitiveAffineEightFrameRow9ModuleRepresentation.representation
  modelRepresentation_generator_formula := representation_generator_formula
  moduleRegistry := PrimitiveAffineEightFrameRow9ModuleRegistry.registry

/-- The singleton row table; completeness is the reusable abstract-S4
catalogue already checked for the literal point stabilizer. -/
noncomputable def table : GeneratedTopTable topData where
  Row := Unit
  data := fun _ ↦ rowData
  complete := by
    intro L _ _ f hf hcard
    obtain ⟨_, e, he⟩ :=
      PrimitiveAffineEightFrameRow9LiteralLocalRow.literalLocalCatalogue.complete
        L f hf hcard
    exact ⟨(), e, he⟩

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

/-- Row 9's public capacity bound through the grouped importer. -/
noncomputable def bounds
    (pointEquiv : block.Points ≃ Fin 8)
    (conjugator : Equiv.Perm (Fin 8))
    (hconjugated :
      MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
        topData.literalAction)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 :=
  GeneratedTopTable.bounds block P topData table pointEquiv conjugator
    hconjugated hr hD hs

end PrimitiveAffineEightFrameRow9GeneratedTable
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
