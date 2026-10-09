import SymmetricSubgroupAsymptotics.FiniteFrameOddNormalizerImporter
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameEmbedding

/-!
# Reusable sixteen-block odd-normalizer row

The finite producer checks a top relative-head bound and one simultaneous
odd-subgroup/normalizer fixed space.  This file is the common importer for
all such rows.  It composes the actual correlated translation module into
the full frame and then into the checked 32-coordinate representation.
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

local instance sixteenEmbeddedPrimeFact : Fact P.p.Prime :=
  (elementaryChart block P).primeFact

/-- A generated sixteen-block row after the literal top and full induced
frame have been matched to the actual action. -/
structure DegreeFourZeroCoreSixteenEmbeddedRow : Type 1 where
  ModelGroup : Type
  [modelGroup : Group ModelGroup]
  [modelFinite : Finite ModelGroup]
  ModelModule : Type
  [modelAddCommGroup : AddCommGroup ModelModule]
  [modelModule : Module (ZMod P.p) ModelModule]
  [modelModuleFinite : Finite ModelModule]
  representation : Representation (ZMod P.p) ModelGroup ModelModule
  groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup
  fullFrameEmbedding :
    (fullTranslationFrameRepresentation block P).IntertwiningMap
      (representation.comp groupEquiv.toMonoidHom)
  fullFrameEmbedding_injective : Function.Injective fullFrameEmbedding
  topSlots : ℕ
  topRelativeBinaryRank : ∀
      (N : Subgroup (DegreeFourComplementQuotient block P)) [N.Normal],
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ topSlots
  fixedWitness : FiniteFrameOddNormalizerWitness representation
  slot_sum_le : topSlots + fixedWitness.dimension ≤ 10

attribute [instance]
  DegreeFourZeroCoreSixteenEmbeddedRow.modelGroup
  DegreeFourZeroCoreSixteenEmbeddedRow.modelModuleFinite
  DegreeFourZeroCoreSixteenEmbeddedRow.modelAddCommGroup
  DegreeFourZeroCoreSixteenEmbeddedRow.modelModule
  DegreeFourZeroCoreSixteenEmbeddedRow.modelFinite

namespace DegreeFourZeroCoreSixteenEmbeddedRow

/-- Every checked embedded row supplies the exact ten-slot finite-frame
bound consumed by the degree-four structural bridge. -/
noncomputable def toBounds
    (C : DegreeFourZeroCoreSixteenEmbeddedRow block P)
    (hr : Nat.card block.Fibre = 4) :
    DegreeFourZeroCoreFiniteFrameBounds block P 10 := by
  let chart := elementaryChart block P
  letI : Fact P.p.Prime := chart.primeFact
  have hp : P.p = 2 := (degreeFour_translationDimension block P hr).1
  letI : Finite chart.V := Finite.of_injective
    (fun v : chart.V ↦ chart.equiv.symm (Multiplicative.ofAdd v))
    chart.equiv.symm.injective
  let moduleEmbedding :
      (show Representation (ZMod P.p)
          (DegreeFourComplementQuotient block P)
          (TranslationSubmodule block P) from
        chart.quotientRepresentation.ρ).IntertwiningMap
        (C.representation.comp C.groupEquiv.toMonoidHom) :=
    C.fullFrameEmbedding.comp
      (translationSubmoduleFullFrameEmbedding block P)
  have moduleEmbedding_injective : Function.Injective moduleEmbedding :=
    C.fullFrameEmbedding_injective.comp
      (translationSubmoduleFullFrameEmbedding_injective block P)
  exact {
    topSlots := C.topSlots
    moduleSlots := C.fixedWitness.dimension
    slot_sum_le := C.slot_sum_le
    topRelativeBinaryRank := by
      intro N
      exact C.topRelativeBinaryRank N
    translationModuleHead := by
      intro B
      have hunit : IsUnit (Nat.card C.fixedWitness.A : ZMod P.p) :=
        isUnit_iff_ne_zero.mpr
        ((ZMod.natCast_eq_zero_iff (Nat.card C.fixedWitness.A) P.p).not.mpr
          (by simpa only [hp] using C.fixedWitness.odd_order))
      exact C.fixedWitness.module_bound_embedding hunit C.groupEquiv
        moduleEmbedding moduleEmbedding_injective B }

end DegreeFourZeroCoreSixteenEmbeddedRow
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
