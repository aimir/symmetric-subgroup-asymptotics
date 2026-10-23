import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearCompanion

/-! Intersecting singular two-planes with nonsingular sum have actual
independent companions with nonzero cross pairing, in any quadratic
module. This retains Q in characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticNonorthogonalCompanions
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem exists_companions (A : QuadraticForm K V) (P Q : Submodule K V)
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hPs : ∀ x ∈ P, A x = 0) (hQs : ∀ x ∈ Q, A x = 0)
    (hmeet : P ⊓ Q ≠ ⊥) (hnonsingular : ¬∀ x ∈ P ⊔ Q, A x = 0) :
    ∃ u ∈ P, u ∈ Q ∧ u ≠ 0 ∧ ∃ v ∈ P, ∃ w ∈ Q,
      (∀ a : K, v ≠ a • u) ∧ (∀ a : K, w ≠ a • u) ∧
      Submodule.span K {u, v} = P ∧ Submodule.span K {u, w} = Q ∧
      A.polarBilin v w ≠ 0 := by
  obtain ⟨u, huPQ, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  obtain ⟨v, hv, hnv, hspanP⟩ := CFSGTwoDimensionalLinearBasis.exists_companion P hP u huPQ.1 hu
  obtain ⟨w, hw, hnw, hspanQ⟩ := CFSGTwoDimensionalLinearBasis.exists_companion Q hQ u huPQ.2 hu
  refine ⟨u, huPQ.1, huPQ.2, hu, v, hv, w, hw, hnv, hnw, hspanP, hspanQ, ?_⟩
  intro hvw
  have huu : A.polarBilin u u = 0 := polar_zero_of_singular A P hPs u u huPQ.1 huPQ.1
  have huw : A.polarBilin u w = 0 := polar_zero_of_singular A Q hQs u w huPQ.2 hw
  have hvu : A.polarBilin v u = 0 := polar_zero_of_singular A P hPs v u hv huPQ.1
  apply hnonsingular
  apply singular_sup A P Q hPs hQs
  intro p hp q hq
  rw [← hspanP] at hp
  rw [← hspanQ] at hq
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hq
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    huu, huw, hvu, hvw, smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGQuadraticNonorthogonalCompanions
