import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicOrbitRegistry
import SymmetricSubgroupAsymptotics.FiniteLinearOrbitStabilizerCover
import SymmetricSubgroupAsymptotics.FiniteLinearOrbitMinimalStabilizerCover

/-!
# Cyclic-orbit registries from checked stabilizer orders

This is the generated-row convenience constructor used by the eight-frame
certificate: vector-orbit coverage is paid by checked stabilizer orders,
while the join table remains indexed only by distinct cyclic submodules.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G V I : Type*} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [Finite V]
  {rho : Representation k G V}
  {states : I → Subrepresentation rho}

namespace BinaryInvariantCyclicOrbitRegistry

/-- Stabilizer-cardinality form of `ofCardinalCover`. -/
noncomputable def ofStabilizerCover {c d : ℕ}
    (orbitRepresentative : Fin c → V)
    (orbitCover : FiniteLinearOrbitStabilizerCover rho orbitRepresentative)
    (cyclicRepresentative : Fin d → V)
    (orbitCyclic : Fin c → Fin d)
    (orbit_span_eq : ∀ o,
      binaryOrbitSpan rho (orbitRepresentative o) =
        binaryOrbitSpan rho (cyclicRepresentative (orbitCyclic o)))
    (bottom : I) (bottom_eq : (states bottom).toSubmodule = ⊥)
    (child : I → Fin d → I)
    (child_eq : ∀ i c, (states (child i c)).toSubmodule =
      (states i).toSubmodule ⊔ binaryOrbitSpan rho (cyclicRepresentative c)) :
    BinaryInvariantCyclicOrbitRegistry rho states :=
  BinaryInvariantCyclicOrbitRegistry.ofCardinalCover
    orbitRepresentative orbitCover.toCardinalCover cyclicRepresentative
    orbitCyclic orbit_span_eq bottom bottom_eq child child_eq

/-- Canonical-minimum form used by generated eight-frame rows. -/
noncomputable def ofMinimalStabilizerCover {c d : ℕ}
    (orbitRepresentative : Fin c → V)
    (orbitCover :
      FiniteLinearOrbitMinimalStabilizerCover rho orbitRepresentative)
    (cyclicRepresentative : Fin d → V)
    (orbitCyclic : Fin c → Fin d)
    (orbit_span_eq : ∀ o,
      binaryOrbitSpan rho (orbitRepresentative o) =
        binaryOrbitSpan rho (cyclicRepresentative (orbitCyclic o)))
    (bottom : I) (bottom_eq : (states bottom).toSubmodule = ⊥)
    (child : I → Fin d → I)
    (child_eq : ∀ i c, (states (child i c)).toSubmodule =
      (states i).toSubmodule ⊔ binaryOrbitSpan rho (cyclicRepresentative c)) :
    BinaryInvariantCyclicOrbitRegistry rho states :=
  BinaryInvariantCyclicOrbitRegistry.ofStabilizerCover
    orbitRepresentative orbitCover.toStabilizerCover cyclicRepresentative
    orbitCyclic orbit_span_eq bottom bottom_eq child child_eq

end BinaryInvariantCyclicOrbitRegistry
end SymmetricSubgroupAsymptotics

end
