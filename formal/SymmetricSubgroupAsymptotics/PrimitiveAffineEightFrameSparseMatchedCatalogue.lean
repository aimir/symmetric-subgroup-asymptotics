import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameWordCyclicOrbitImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameDisplacementImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreResidualAssembly
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameEmbedding

/-!
# Exact sparse matched catalogue for eight-block frames

This is the generated-certificate boundary for the thirty eight-block frame
rows.  A row contains locally checked sparse normal words, a vector-orbit
cover with deduplicated cyclic join columns, and exact equivalences to the
literal retained quotient top and translation representation.
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

local instance sparseMatchedCataloguePrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- One fully checked sparse eight-block row.  The group and module model
types are row-local.  The exact top equivalence and equivariant equivalence
of the full induced frame prevent using a numerically matching row for the
wrong action; the correlated literal translation module is then restricted
through its canonical injection into that frame. -/
structure DegreeFourZeroCoreEightSparseMatchedRow : Type 1 where
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
  fullFrameEquiv :
    (fullTranslationFrameRepresentation block P).Equiv
      (representation.comp groupEquiv.toMonoidHom)
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
  DegreeFourZeroCoreEightSparseMatchedRow.modelGroup
  DegreeFourZeroCoreEightSparseMatchedRow.modelFinite
  DegreeFourZeroCoreEightSparseMatchedRow.modelAddCommGroup
  DegreeFourZeroCoreEightSparseMatchedRow.modelModule
  DegreeFourZeroCoreEightSparseMatchedRow.modelFiniteDimensional
  DegreeFourZeroCoreEightSparseMatchedRow.modelModuleFinite
  DegreeFourZeroCoreEightSparseMatchedRow.topIndexFinite

namespace DegreeFourZeroCoreEightSparseMatchedRow

/-- A sparse matched row supplies the stronger `2+2≤5` fixed-frame
certificate required by the structural bridge. -/
noncomputable def toBounds
    (C : DegreeFourZeroCoreEightSparseMatchedRow block P) :
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
    C.fullFrameEquiv.toIntertwiningMap.comp
      (translationSubmoduleFullFrameEmbedding block P)
  have moduleEmbedding_injective : Function.Injective moduleEmbedding :=
    C.fullFrameEquiv.injective.comp
      (translationSubmoduleFullFrameEmbedding_injective block P)
  exact DegreeFourZeroCoreFiniteFrameBounds.ofMatchedWordCyclicOrbitRegistries
    block P C.conjugacyCover C.ambient C.stateGenerators C.representation
    C.groupEquiv moduleEmbedding moduleEmbedding_injective (by omega)
    C.top C.moduleRegistry.toHeadRegistry

end DegreeFourZeroCoreEightSparseMatchedRow

/-- The exact thirty-row output after the structural catalogue dispatcher
has selected the row matching the literal eight-block zero-core action. -/
abbrev DegreeFourZeroCoreEightSparseMatchedCatalogue :=
  ∀ {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre],
    Nat.card block.Fibre = 4 →
    degreeFourTernaryCore block P = ⊥ →
    Nat.card block.Points = 8 →
    DegreeFourZeroCoreEightSparseMatchedRow block P

/-- Thread the exact sparse catalogue into the frozen degree-four residual
interface. -/
noncomputable def DegreeFourZeroCoreEightSparseMatchedCatalogue.toFrameBoundsInput
    (C : DegreeFourZeroCoreEightSparseMatchedCatalogue) :
    DegreeFourZeroCoreEightFrameBoundsInput := by
  intro w U basePoint block P _ hr hD hs
  exact (C block P hr hD hs).toBounds

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
