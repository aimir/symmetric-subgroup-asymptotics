import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GeneratorHeads
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborCount

/-! Each actual original simple D4 root moves the original root
plane by zero or one edge of the SAME quadratic singular-plane graph.
The proof uses a fixed nonzero original head and the original positive
space, including characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexPositiveGraph CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexResidualNeighborCount
variable (K : Type) [Field K]

def generatorLinear (neg : Bool) (i : Fin 4) (a : K) :
    (Index 4 → K) ≃ₗ[K] (Index 4 → K) :=
  ambientLinearEquiv K 4 (rootTransvection K 4 neg i a)

theorem rootPlane_le_positive : rootPlane K ≤ positiveSpace K 4 := by
  apply Submodule.span_le.mpr
  rintro x (rfl | rfl) <;> intro j <;>
    simp only [head0, head1, Pi.single_apply, Sum.inr_ne_inl, if_false]

theorem generator_rootPlane_le_positive (neg : Bool) (i : Fin 4) (a : K) :
    (rootPlane K).map (generatorLinear K neg i a).toLinearMap ≤ positiveSpace K 4 := by
  apply Submodule.map_le_iff_le_comap.mpr
  apply Submodule.span_le.mpr
  rintro x (rfl | rfl)
  · change (rootTransvection K 4 neg i a : Mat K 4) *ᵥ head0 K ∈ positiveSpace K 4
    simpa only [head0, Matrix.mulVec_single_one] using (root_head_columns_positive K neg i a).1
  · change (rootTransvection K 4 neg i a : Mat K 4) *ᵥ head1 K ∈ positiveSpace K 4
    simpa only [head1, Matrix.mulVec_single_one] using (root_head_columns_positive K neg i a).2

theorem generator_intersection_nonzero (neg : Bool) (i : Fin 4) (a : K) :
    ∃ v : Index 4 → K,
      v ∈ rootPlane K ⊓ (rootPlane K).map (generatorLinear K neg i a).toLinearMap ∧ v ≠ 0 := by
  rcases root_fixes_head K neg i a with h0 | h1
  · have hmem : head0 K ∈ rootPlane K := Submodule.subset_span (Or.inl rfl)
    exact ⟨head0 K, ⟨hmem, ⟨head0 K, hmem, h0⟩⟩, head0_ne_zero K⟩
  · have hmem : head1 K ∈ rootPlane K := Submodule.subset_span (Or.inr rfl)
    exact ⟨head1 K, ⟨hmem, ⟨head1 K, hmem, h1⟩⟩, head1_ne_zero K⟩

theorem root_generator_plane_eq_or_adjacent (neg : Bool) (i : Fin 4) (a : K) :
    rootPlane K = (rootPlane K).map (generatorLinear K neg i a).toLinearMap ∨
      QuadraticAdjacent K 4 (rootPlane K)
        ((rootPlane K).map (generatorLinear K neg i a).toLinearMap) := by
  classical
  let M := (rootPlane K).map (generatorLinear K neg i a).toLinearMap
  have hM : Module.finrank K M = 2 :=
    ((generatorLinear K neg i a).finrank_map_eq (rootPlane K)).trans (rootPlane_finrank K)
  by_cases he : rootPlane K = M
  · exact Or.inl he
  · right
    have hlo : 1 ≤ Module.finrank K ↥(rootPlane K ⊓ M) := by
      obtain ⟨v, hv, hne⟩ := generator_intersection_nonzero K neg i a
      have hle : Submodule.span K {v} ≤ rootPlane K ⊓ M :=
        (Submodule.span_singleton_le_iff_mem _ _).mpr hv
      have hh := Submodule.finrank_mono hle
      rw [finrank_span_singleton hne] at hh
      exact hh
    have hhi : Module.finrank K ↥(rootPlane K ⊓ M) ≤ 1 := by
      have hb := Submodule.finrank_mono (inf_le_left : rootPlane K ⊓ M ≤ rootPlane K)
      rw [rootPlane_finrank] at hb
      by_contra hn
      have hd : Module.finrank K ↥(rootPlane K ⊓ M) = 2 := by omega
      have hR : rootPlane K ⊓ M = rootPlane K :=
        Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hd, rootPlane_finrank])
      have hM' : rootPlane K ⊓ M = M :=
        Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hd, hM])
      exact he (hR.symm.trans hM')
    refine ⟨he, le_antisymm hhi hlo, ?_⟩
    intro z hz
    exact positiveSpace_singular K 4
      ⟨z, (sup_le (rootPlane_le_positive K) (generator_rootPlane_le_positive K neg i a)) hz⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
