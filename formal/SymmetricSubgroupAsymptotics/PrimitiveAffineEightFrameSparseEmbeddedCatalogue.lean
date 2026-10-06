import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameSparseMatchedCatalogue

/-!
# Sparse embedded catalogue for eight-block frames

The finite-frame consumer only needs an injective equivariant map from the
literal full translation frame to the checked row.  Surjectivity of that map
is mathematically true for the sixteen-dimensional emitted rows, but it is
not used by the capacity theorem.  This file records the exact weaker
boundary, so that the finite importer does not have to prove an unnecessary
representation equivalence.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance sparseEmbeddedCataloguePrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- One checked sparse row, with the literal full frame embedded in the
checked representation.  The exact group equivalence is retained, and the
embedding is required to be injective. -/
structure DegreeFourZeroCoreEightSparseEmbeddedRow : Type 1 where
  ModelGroup : Type
  [modelGroup : Group ModelGroup]
  [modelFinite : Finite ModelGroup]
  ModelModule : Type
  [modelAddCommGroup : AddCommGroup ModelModule]
  [modelModule : Module (ZMod P.p) ModelModule]
  [modelFiniteDimensional : FiniteDimensional
    (ZMod P.p) ModelModule]
  [modelModuleFinite : Finite ModelModule]
  representation : Representation
    (ZMod P.p) ModelGroup ModelModule
  groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup
  fullFrameEmbedding :
    (fullTranslationFrameRepresentation block P).IntertwiningMap
      (representation.comp groupEquiv.toMonoidHom)
  fullFrameEmbedding_injective : Function.Injective fullFrameEmbedding
  classCount : ℕ
  representative : Fin classCount → ModelGroup
  conjugacyCover : FiniteConjugacyCardinalCover representative
  TopIndex : Type
  [topIndexFinite : Finite TopIndex]
  AmbientIndex : Type
  GeneratorIndex : Type
  ambient : AmbientIndex → ModelGroup
  stateGenerators : TopIndex → GeneratorIndex → ModelGroup
  top : FiniteTopRelativeBinaryRankWordRegistry
    (rank := 2) conjugacyCover ambient stateGenerators
  moduleRegistry : FiniteFrameModuleCyclicOrbitDisplacementRegistry
    representation 2

attribute [instance]
  DegreeFourZeroCoreEightSparseEmbeddedRow.modelGroup
  DegreeFourZeroCoreEightSparseEmbeddedRow.modelFinite
  DegreeFourZeroCoreEightSparseEmbeddedRow.modelAddCommGroup
  DegreeFourZeroCoreEightSparseEmbeddedRow.modelModule
  DegreeFourZeroCoreEightSparseEmbeddedRow.modelFiniteDimensional
  DegreeFourZeroCoreEightSparseEmbeddedRow.modelModuleFinite
  DegreeFourZeroCoreEightSparseEmbeddedRow.topIndexFinite

namespace DegreeFourZeroCoreEightSparseEmbeddedRow

/-- Every previously matched row gives an embedded row by forgetting
surjectivity of the full-frame identification. -/
noncomputable def ofMatched
    (C : DegreeFourZeroCoreEightSparseMatchedRow block P) :
    DegreeFourZeroCoreEightSparseEmbeddedRow block P where
  ModelGroup := C.ModelGroup
  ModelModule := C.ModelModule
  representation := C.representation
  groupEquiv := C.groupEquiv
  fullFrameEmbedding := C.fullFrameEquiv.toIntertwiningMap
  fullFrameEmbedding_injective := C.fullFrameEquiv.injective
  classCount := C.classCount
  representative := C.representative
  conjugacyCover := C.conjugacyCover
  TopIndex := C.TopIndex
  AmbientIndex := C.AmbientIndex
  GeneratorIndex := C.GeneratorIndex
  ambient := C.ambient
  stateGenerators := C.stateGenerators
  top := C.top
  moduleRegistry := C.moduleRegistry

/-- The embedded boundary is already sufficient for the structural
`2+2≤5` fixed-frame certificate. -/
noncomputable def toBounds
    (C : DegreeFourZeroCoreEightSparseEmbeddedRow block P) :
    DegreeFourZeroCoreFiniteFrameBounds block P 5 := by
  letI : Finite (elementaryChart block P).V := Finite.of_injective
    (fun v : (elementaryChart block P).V ↦
      (elementaryChart block P).equiv.symm (Multiplicative.ofAdd v))
    (elementaryChart block P).equiv.symm.injective
  let moduleEmbedding :
      (show Representation (ZMod P.p)
          (DegreeFourComplementQuotient block P)
          (TranslationSubmodule block P) from
        (elementaryChart block P).quotientRepresentation.ρ).IntertwiningMap
        (C.representation.comp C.groupEquiv.toMonoidHom) :=
    C.fullFrameEmbedding.comp
      (translationSubmoduleFullFrameEmbedding block P)
  have moduleEmbedding_injective : Function.Injective moduleEmbedding :=
    C.fullFrameEmbedding_injective.comp
      (translationSubmoduleFullFrameEmbedding_injective block P)
  exact DegreeFourZeroCoreFiniteFrameBounds.ofMatchedWordCyclicOrbitRegistries
    block P C.conjugacyCover C.ambient C.stateGenerators C.representation
    C.groupEquiv moduleEmbedding moduleEmbedding_injective (by omega)
    C.top C.moduleRegistry.toHeadRegistry

end DegreeFourZeroCoreEightSparseEmbeddedRow

/-- Exact generated deliverable after the structural dispatcher has chosen
the checked row matching the literal eight-block zero-core action. -/
abbrev DegreeFourZeroCoreEightSparseEmbeddedCatalogue :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    Nat.card block.Fibre = 4 →
    degreeFourTernaryCore block P = ⊥ →
    Nat.card block.Points = 8 →
    DegreeFourZeroCoreEightSparseEmbeddedRow block P

/-- Thread the embedded catalogue into the frozen residual interface. -/
noncomputable def DegreeFourZeroCoreEightSparseEmbeddedCatalogue.toFrameBoundsInput
    (C : DegreeFourZeroCoreEightSparseEmbeddedCatalogue) :
    DegreeFourZeroCoreEightFrameBoundsInput := by
  intro w U basePoint block P _ hr hD hs
  exact (C block P hr hD hs).toBounds

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
