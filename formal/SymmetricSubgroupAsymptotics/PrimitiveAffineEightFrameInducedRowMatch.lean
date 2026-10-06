import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameFullFrameInduced
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameLiteralBinding
import SymmetricSubgroupAsymptotics.RepresentationIntertwinerGenerators

/-!
# Binding an emitted induced row to the literal eight-block frame

The generic wreath theorem has already embedded the actual full frame in an
induced representation.  A selected finite row therefore has to check only
an injective intertwiner from that induced model to its emitted matrix
representation.  This is the exact consumer of the stored coset
representatives, local epimorphism and binary basis.
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

local instance inducedRowMatchPrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- Row-specific matching data after the generic full-frame-to-induced
transport has been removed. -/
structure DegreeFourZeroCoreEightInducedRowMatch
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

namespace DegreeFourZeroCoreEightInducedRowMatch

/-- Build the row match from a linear coordinate map and equations on one
displayed generating tuple.  This is the intended generated-certificate
constructor. -/
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
    DegreeFourZeroCoreEightInducedRowMatch
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

/-- Compose the finite induced-row match with the generic literal frame
embedding. -/
noncomputable def toLiteralFrameMatch
    {ModelGroup ModelModule : Type}
    [Group ModelGroup] [Finite ModelGroup]
    [AddCommGroup ModelModule]
    [Module (ZMod P.p) ModelModule]
    [FiniteDimensional (ZMod P.p) ModelModule]
    [Finite ModelModule]
    (representation : Representation
      (ZMod P.p) ModelGroup ModelModule)
    (groupEquiv : DegreeFourComplementQuotient block P ≃* ModelGroup)
    (M : DegreeFourZeroCoreEightInducedRowMatch
      block P ModelGroup ModelModule representation groupEquiv) :
    DegreeFourZeroCoreEightLiteralFrameMatch
      block P ModelGroup ModelModule representation groupEquiv where
  fullFrameEmbedding := M.inducedEmbedding.comp
    (fullTranslationFrameToInduced block P M.point)
  fullFrameEmbedding_injective := M.inducedEmbedding_injective.comp
    (fullTranslationFrameToInduced_injective block P M.point)

end DegreeFourZeroCoreEightInducedRowMatch

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
