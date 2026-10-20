import SymmetricSubgroupAsymptotics.CyclicQuotientInducedUniformCapacity
import SymmetricSubgroupAsymptotics.RepresentationFiniteCoordinateGenerators
import SymmetricSubgroupAsymptotics.InducedTernaryHead
import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke

/-! One genuine generator per actual cyclic Mackey orbit when the local
core acts transitively on nonzero dual coefficients. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics
attribute [local instance] inducedMackeyComponentAddCommGroup inducedMackeyComponentModule

variable {k G V : Type} [Field k] [Finite k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V] [FiniteDimensional k V]

/-- Every orbit, local stabilizer, twisted fibre, and original coordinate
map is retained. The hypotheses are actual local structure, not a module
generation bound. -/
theorem induced_cyclic_orbit_uniform_one_each
    (H N : Subgroup G) (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (N : Set G))]
    (hNormal : ∀ q : DoubleCoset.Quotient (H : Set G) (N : Set G),
      (inducedOrbitStabilizer H N q.out).Normal)
    (hCyclic : ∀ q : DoubleCoset.Quotient (H : Set G) (N : Set G),
      letI := hNormal q
      IsCyclic (N⧸inducedOrbitStabilizer H N q.out))
    (L : ∀ q : DoubleCoset.Quotient (H : Set G) (N : Set G),
      Subgroup (inducedOrbitStabilizer H N q.out))
    (hL : ∀ q,(L q).map (inducedOrbitStabilizer H N q.out).subtype≤
      (inducedOrbitStabilizer H N q.out).normalCore)
    (hchi : ∀ q,Nat.card (Quotient (representationNonzeroOrbitRel
      (Representation.dual (((inducedOrbitFibre H N rho q.out).comp (L q).subtype) :
        Representation k (L q) V))))=1) :
    UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho)
      (Fintype.card (DoubleCoset.Quotient (H : Set G) (N : Set G))) := by
  intro M
  have hlocal (q : DoubleCoset.Quotient (H : Set G) (N : Set G)) :
      UniformSubrepresentationGeneratorBound
        (Representation.ind (inducedOrbitStabilizer H N q.out).subtype
          (inducedOrbitFibre H N rho q.out)) 1 := by
    letI := hNormal q
    letI := hCyclic q
    have h := cyclicQuotient_induced_uniform_capacity
      (inducedOrbitStabilizer H N q.out) (inducedOrbitFibre H N rho q.out) (L q) (hL q)
    apply h.mono
    rw [hchi q]
    exact min_le_right _ _
  have h := representationGeneratedBy_of_finite_coordinate_bounds
    (fun q => inducedMackeyComponent H N rho q)
    (M.toRepresentation.comp N.subtype)
    (fun q => Representation.ind (inducedOrbitStabilizer H N q.out).subtype
      (inducedOrbitFibre H N rho q.out)) (fun _ => 1)
    (fun q S => hlocal q S)
    (inducedMackeySubmoduleCoordinate H N rho M)
    (inducedMackeySubmoduleCoordinate_injective H N rho M)
  apply RepresentationGeneratedBy.of_comp M.toRepresentation N.subtype
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using h

end SymmetricSubgroupAsymptotics
