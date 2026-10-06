import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameCyclicOrbitImporter
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantFiniteCertificate
import SymmetricSubgroupAsymptotics.BinaryCoordinateDisplacementCertificate

/-!
# Displacement-basis importer for finite frame rows

The generated eight-frame rows store a basis for a subspace of the literal
generator-displacement span at every invariant state.  Its codimension is
the computed module head.  This file turns those local checks into the
semantic cyclic-orbit head registry.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- A cyclic-orbit registry together with explicit displacement subspaces
for one retained generating tuple. -/
structure FiniteFrameModuleCyclicOrbitDisplacementRegistry
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (rho : Representation k G V) (rank : ℕ) : Type 1 where
  Index : Type
  [indexFinite : Finite Index]
  state : Index → Subrepresentation rho
  axes : BinaryInvariantCyclicOrbitRegistry rho state
  GeneratorIndex : Type
  generators : GeneratorIndex → G
  displacement : ∀ i, Submodule k (state i).toSubmodule
  displacement_le : ∀ i,
    displacement i ≤
      representationGeneratorDisplacementSpan rho generators (state i)
  codim_le : ∀ i,
    Module.finrank k (state i).toSubmodule ≤
      Module.finrank k (displacement i) + rank

attribute [instance]
  FiniteFrameModuleCyclicOrbitDisplacementRegistry.indexFinite

namespace FiniteFrameModuleCyclicOrbitDisplacementRegistry

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {rho : Representation k G V} {rank : ℕ}

/-- Discharge the per-state coinvariant bound from the emitted displacement
basis and retain the deduplicated cyclic join table. -/
noncomputable def toHeadRegistry
    (C : FiniteFrameModuleCyclicOrbitDisplacementRegistry rho rank) :
    FiniteFrameModuleCyclicOrbitHeadRegistry rho rank where
  Index := C.Index
  state := C.state
  axes := C.axes
  head_le i :=
    representationCoinvariants_finrank_le_of_displacementSubspace
      rho C.generators (C.state i) (C.displacement i) rank
      (C.displacement_le i) (C.codim_le i)

section BinaryCoordinates

variable {G I J : Type} [Group G] [Finite I]
  {w rank : ℕ}
  {rho : Representation (ZMod 2) G (Fin w → ZMod 2)}
  (state : I → Subrepresentation rho)
  (axes : BinaryInvariantCyclicOrbitRegistry rho state)
  (generators : J → G)
  (dimension : I → ℕ)
  (coordinates : ∀ i, BinaryCoordinateSpace w (dimension i))
  (certificate : ∀ i,
    BinaryCoordinateDisplacementCertificate rho generators (state i)
      (coordinates i))

/-- Assemble the module row directly from reversible binary-coordinate
charts and sparse displacement decompositions.  The generated row only
supplies the numerical codimension inequality; the displacement dimension
itself is proved from the chart. -/
noncomputable def ofBinaryCoordinateCertificates
    (codim_le : ∀ i,
      Module.finrank (ZMod 2) (state i).toSubmodule ≤
        dimension i + rank) :
    FiniteFrameModuleCyclicOrbitDisplacementRegistry rho rank where
  Index := I
  state := state
  axes := axes
  GeneratorIndex := J
  generators := generators
  displacement i := (certificate i).submodule
  displacement_le i :=
    (certificate i).le_generatorDisplacementSpan
  codim_le i := by
    simpa only [(certificate i).finrank] using codim_le i

end BinaryCoordinates

end FiniteFrameModuleCyclicOrbitDisplacementRegistry

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
