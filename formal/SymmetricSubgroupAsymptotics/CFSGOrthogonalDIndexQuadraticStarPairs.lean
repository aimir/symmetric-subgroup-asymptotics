import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexPairProductQuadratic
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneIntersectionPartition

/-! Quadratic, characteristic-free local star relations. Nonzero
polar pairing of two companions forces an intersecting nonsingular
plane pair; conversely zero pairing makes their common-axis sum
quadratically singular. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticStarPairs
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexPairProductQuadratic
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem intersecting_nonsingular_of_pairing (Q : QuadraticForm K V)
    (P R : Submodule K V) (hP : Module.finrank K P = 2) (hR : Module.finrank K R = 2)
    (hPs : ∀ x ∈ P, Q x = 0) (hRs : ∀ x ∈ R, Q x = 0)
    (u v w : V) (hu : u ≠ 0) (huP : u ∈ P) (huR : u ∈ R)
    (hvP : v ∈ P) (hwR : w ∈ R) (hvw : Q.polarBilin v w ≠ 0) :
    Module.finrank K ↥(P ⊓ R) = 1 ∧ ¬∀ x ∈ P ⊔ R, Q x = 0 := by
  have hne : P ≠ R := by
    intro he
    exact hvw (polar_zero_of_singular Q P hPs v w hvP (he.symm ▸ hwR))
  have hnd : ¬Disjoint P R := by
    intro hd
    have hz : u ∈ (⊥ : Submodule K V) :=
      (disjoint_iff.mp hd) ▸ (show u ∈ P ⊓ R from ⟨huP, huR⟩)
    exact hu (by simpa only [Submodule.mem_bot] using hz)
  refine ⟨CFSGTwoPlaneIntersectionPartition.inf_finrank_eq_one_of_not_disjoint
    P R hP hR hne hnd, ?_⟩
  intro hs
  exact hvw (polar_zero_of_singular Q (P ⊔ R) hs v w
    (Submodule.mem_sup_left hvP) (Submodule.mem_sup_right hwR))

theorem singular_join_of_companion_pairing_zero (Q : QuadraticForm K V)
    (u v w : V) (hu : Q u = 0) (hv : Q v = 0) (hw : Q w = 0)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0)
    (hvw : Q.polarBilin v w = 0) :
    ∀ x ∈ Submodule.span K {u, v} ⊔ Submodule.span K {u, w}, Q x = 0 := by
  intro x hx
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hq
  have he : a • u + b • v + (c • u + d • w) = (a + c) • u + b • v + d • w := by
    module
  rw [he, singular_shared_combination Q u v w hu hv hw huv huw, hvw, mul_zero]

theorem pairing_ne_zero_of_nonsingular_join (Q : QuadraticForm K V)
    (u v w : V) (hu : Q u = 0) (hv : Q v = 0) (hw : Q w = 0)
    (huv : Q.polarBilin u v = 0) (huw : Q.polarBilin u w = 0)
    (hn : ¬∀ x ∈ Submodule.span K {u, v} ⊔ Submodule.span K {u, w}, Q x = 0) :
    Q.polarBilin v w ≠ 0 := by
  intro hz
  exact hn (singular_join_of_companion_pairing_zero Q u v w hu hv hw huv huw hz)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticStarPairs
