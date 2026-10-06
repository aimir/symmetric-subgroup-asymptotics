import SymmetricSubgroupAsymptotics.BinaryInvariantOrbitRegistry
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFiniteFrameSource

/-!
# Orbit-compressed importer for the eight-block frame rows

This file supplies the finite-certificate boundary used by the eight-block
exporter.  The committed JSON lists every invariant submodule, while the
independent checker proves closure after adjoining a cyclic orbit module.
The orbit-compressed registry below retains precisely those checks and
converts them to the semantic finite-frame bound used by the structural
degree-four proof.

The remaining generated row files must provide the concrete states, orbit
representatives, transitions, and the per-state head calculations.  No
enumeration-completeness proposition is accepted as a field: completeness
continues to follow from the local orbit-cover and join equations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- The checkable module half of an eight-block row, compressed by vector
orbits.  It converts to `FiniteFrameModuleHeadRegistry` without expanding a
child table indexed by every vector. -/
structure FiniteFrameModuleOrbitHeadRegistry
    {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V) (rank : ℕ) : Type 1 where
  Index : Type
  [indexFinite : Finite Index]
  state : Index → Subrepresentation rho
  axes : BinaryInvariantOrbitRegistry rho state
  head_le : ∀ i,
    Module.finrank k (state i).toRepresentation.Coinvariants ≤ rank

attribute [instance] FiniteFrameModuleOrbitHeadRegistry.indexFinite

namespace FiniteFrameModuleOrbitHeadRegistry

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  {rho : Representation k G V} {rank : ℕ}

/-- Forget the orbit compression after its local cover has been checked. -/
noncomputable def toRegistry
    (C : FiniteFrameModuleOrbitHeadRegistry rho rank) :
    FiniteFrameModuleHeadRegistry rho rank where
  Index := C.Index
  state := C.state
  axes := C.axes.toRegistry
  head_le := C.head_le

/-- The compressed row proves the same uniform module-head bound. -/
theorem bound [Finite V]
    (C : FiniteFrameModuleOrbitHeadRegistry rho rank)
    (B : Subrepresentation rho) :
    Module.finrank k B.toRepresentation.Coinvariants ≤ rank :=
  C.toRegistry.bound B

end FiniteFrameModuleOrbitHeadRegistry

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

namespace DegreeFourZeroCoreFiniteFrameBounds

/-- Import a top registry and an orbit-compressed module registry when the
checked representation is already the actual correlated translation
representation.  The later matched-row importer only has to transport the
literal finite model to this representation. -/
noncomputable def ofOrbitRegistries {slots topSlots moduleSlots : ℕ}
    [Finite (elementaryChart block P).V]
    (slot_sum_le : topSlots + moduleSlots ≤ slots)
    (top : FiniteTopRelativeBinaryRankRegistry
      (DegreeFourComplementQuotient block P) topSlots)
    (module : FiniteFrameModuleOrbitHeadRegistry
      (elementaryChart block P).quotientRepresentation.ρ moduleSlots) :
    DegreeFourZeroCoreFiniteFrameBounds block P slots :=
  DegreeFourZeroCoreFiniteFrameBounds.ofRegistries block P slot_sum_le top
    module.toRegistry

end DegreeFourZeroCoreFiniteFrameBounds

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
