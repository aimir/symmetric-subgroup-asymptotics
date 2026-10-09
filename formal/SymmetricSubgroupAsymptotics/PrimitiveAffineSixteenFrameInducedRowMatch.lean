import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameInduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameLiteralBinding
import SymmetricSubgroupAsymptotics.RepresentationIntertwinerGenerators

/-!
# Binding an emitted induced row to the literal sixteen-block frame

The generic wreath theorem embeds the actual full frame in an induced
representation.  A selected finite row therefore checks only an injective
intertwiner from that induced model to its emitted matrix representation.
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

local instance sixteenInducedRowMatchPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- Row-specific matching data after the generic full-frame-to-induced
transport has been removed. -/
structure DegreeFourZeroCoreSixteenInducedRowMatch
    (ModelGroup ModelModule : Type)
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup) : Type 1 where
  point : block.Points
  inducedEmbedding :
    (Representation.ind
      (fullFrameInducedStabilizer block P point).subtype
      (fullFrameInducedLocalRepresentation block P point)).IntertwiningMap
        (representation.comp groupEquiv.toMonoidHom)
  inducedEmbedding_injective : Function.Injective inducedEmbedding

namespace DegreeFourZeroCoreSixteenInducedRowMatch

/-- Build the row match from a linear coordinate map and equations on one
displayed generating tuple. -/
noncomputable def ofGeneratorEquations
    {ModelGroup ModelModule ι : Type}
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup)
    (point : block.Points)
    (generators : ι → DegreeFourComplementQuotient block P)
    (hgenerates : Subgroup.closure (Set.range generators) = ⊤)
    (coordinateMap :
      Representation.IndV
          (fullFrameInducedStabilizer block P point).subtype
          (fullFrameInducedLocalRepresentation block P point) →ₗ[
            ZMod P.p] ModelModule)
    (coordinateMap_injective : Function.Injective coordinateMap)
    (hgenerator : ∀ i v,
      coordinateMap
          (Representation.ind
            (fullFrameInducedStabilizer block P point).subtype
            (fullFrameInducedLocalRepresentation block P point)
            (generators i) v) =
        representation (groupEquiv (generators i))
          (coordinateMap v)) :
    DegreeFourZeroCoreSixteenInducedRowMatch
      block P ModelGroup ModelModule representation groupEquiv where
  point := point
  inducedEmbedding := representationIntertwiningMap_of_generators
    (Representation.ind
      (fullFrameInducedStabilizer block P point).subtype
      (fullFrameInducedLocalRepresentation block P point))
    (representation.comp groupEquiv.toMonoidHom)
    coordinateMap generators hgenerates (by
      intro i v
      exact hgenerator i v)
  inducedEmbedding_injective := coordinateMap_injective

/-- Compose the finite induced-row match with the generic full-frame
embedding. -/
noncomputable def fullFrameEmbedding
    {ModelGroup ModelModule : Type}
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup)
    (M : DegreeFourZeroCoreSixteenInducedRowMatch
      block P ModelGroup ModelModule representation groupEquiv) :
    (fullTranslationFrameRepresentation block P).IntertwiningMap
      (representation.comp groupEquiv.toMonoidHom) :=
  M.inducedEmbedding.comp (fullTranslationFrameToInduced block P M.point)

theorem fullFrameEmbedding_injective
    {ModelGroup ModelModule : Type}
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup)
    (M : DegreeFourZeroCoreSixteenInducedRowMatch
      block P ModelGroup ModelModule representation groupEquiv) :
    Function.Injective (M.fullFrameEmbedding block P representation groupEquiv) :=
  M.inducedEmbedding_injective.comp
    (fullTranslationFrameToInduced_injective block P M.point)

end DegreeFourZeroCoreSixteenInducedRowMatch

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
