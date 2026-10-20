import SymmetricSubgroupAsymptotics.InducedCyclicOrbitGenerators
import SymmetricSubgroupAsymptotics.InducedNormalCoreOrbitTwist
import SymmetricSubgroupAsymptotics.CyclicQuotientOvergroup

/-! An actual globally normal coefficient core and a cyclic orbit group
quotient give one generator per literal Mackey orbit. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Finite k] [Group G] [Finite G]
    [AddCommGroup V] [Module k V] [Finite V] [Nontrivial V] [FiniteDimensional k V]

theorem induced_normalCore_cyclic_orbit_uniform
    (H N B : Subgroup G) [B.Normal] (hBH : B≤H) (hBN : B≤N)
    [IsCyclic (N⧸B.subgroupOf N)] (rho : Representation k H V)
    [Fintype (DoubleCoset.Quotient (H : Set G) (N : Set G))]
    (hchi : Nat.card (Quotient (representationNonzeroOrbitRel
      (Representation.dual (rho.comp (B.subgroupOf H).subtype))))=1) :
    UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho)
      (Fintype.card (DoubleCoset.Quotient (H : Set G) (N : Set G))) := by
  have hBq (x : G) : B.subgroupOf N ≤ inducedOrbitStabilizer H N x := by
    intro b hb
    change x*(b : G)*x⁻¹∈H
    exact hBH ((inferInstance : B.Normal).conj_mem _ hb x)
  have hNormal (q : DoubleCoset.Quotient (H : Set G) (N : Set G)) :
      (inducedOrbitStabilizer H N q.out).Normal :=
    normal_of_cyclic_quotient_kernel (B.subgroupOf N)
      (inducedOrbitStabilizer H N q.out) (hBq q.out)
  have hCyclic (q : DoubleCoset.Quotient (H : Set G) (N : Set G)) :
      letI := hNormal q
      IsCyclic (N⧸inducedOrbitStabilizer H N q.out) :=
    cyclic_quotient_of_kernel_le (B.subgroupOf N)
      (inducedOrbitStabilizer H N q.out) (hBq q.out)
  apply induced_cyclic_orbit_uniform_one_each H N rho hNormal hCyclic
    (fun q => inducedNormalCore H N B q.out)
  · intro q
    letI := hNormal q
    rw [Subgroup.normalCore_eq_self]
    rintro a ⟨l,_,rfl⟩
    exact l.property
  · intro q
    exact (inducedNormalCore_dualOrbitCard H N B hBN q.out rho).trans hchi

end SymmetricSubgroupAsymptotics
