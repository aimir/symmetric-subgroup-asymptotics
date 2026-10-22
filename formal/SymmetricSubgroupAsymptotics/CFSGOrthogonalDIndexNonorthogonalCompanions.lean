import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexBundledQuadratic
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion

/-! Original intersecting singular planes with nonsingular sum have
actual companions that pair nontrivially. This derives the transverse
coefficient needed for normalization; it is not an extra R11 premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNonorthogonalCompanions
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane
variable (K : Type) [Field K]

theorem exists_companions (r : ℕ) (P Q : Submodule K (Index r → K))
    (hP : Module.finrank K P = 2) (hQ : Module.finrank K Q = 2)
    (hPs : ∀ x ∈ P, splitQuadraticForm K r x = 0)
    (hQs : ∀ x ∈ Q, splitQuadraticForm K r x = 0)
    (hmeet : P ⊓ Q ≠ ⊥)
    (hnonsingular : ¬∀ x ∈ P ⊔ Q, splitQuadraticForm K r x = 0) :
    ∃ u ∈ P, u ∈ Q ∧ u ≠ 0 ∧ ∃ v ∈ P, ∃ w ∈ Q,
      (∀ a : K, v ≠ a • u) ∧ (∀ a : K, w ≠ a • u) ∧
      Submodule.span K {u, v} = P ∧ Submodule.span K {u, w} = Q ∧
      (splitQuadraticForm K r).polarBilin v w ≠ 0 := by
  obtain ⟨u, huPQ, hu⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  obtain ⟨v, hv, hnv, hspanP⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion P hP u huPQ.1 hu
  obtain ⟨w, hw, hnw, hspanQ⟩ := CFSGTwoDimensionalSubmoduleBasis.exists_companion Q hQ u huPQ.2 hu
  refine ⟨u, huPQ.1, huPQ.2, hu, v, hv, w, hw, hnv, hnw, hspanP, hspanQ, ?_⟩
  intro hvw
  have huu : (splitQuadraticForm K r).polarBilin u u = 0 :=
    polar_zero_of_singular _ P hPs u u huPQ.1 huPQ.1
  have huw : (splitQuadraticForm K r).polarBilin u w = 0 :=
    polar_zero_of_singular _ Q hQs u w huPQ.2 hw
  have hvu : (splitQuadraticForm K r).polarBilin v u = 0 :=
    polar_zero_of_singular _ P hPs v u hv huPQ.1
  apply hnonsingular
  apply singular_sup _ P Q hPs hQs
  intro p hp q hq
  rw [← hspanP] at hp
  rw [← hspanQ] at hq
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hp
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hq
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    huu, huw, hvu, hvw, smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexNonorthogonalCompanions
