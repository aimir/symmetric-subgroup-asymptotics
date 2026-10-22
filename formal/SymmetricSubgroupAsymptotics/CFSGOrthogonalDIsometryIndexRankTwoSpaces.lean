import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexCrossingSpaces
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Orbit

/-! The two actual D2 plane directions are the literal positive and
one-pair-crossed spaces used in the general-rank induction. The original
elementary word, not a larger isometry, performs the normalization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexRankTwoSpaces
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPositiveSpace
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDIsometryIndexCrossingSpaces
variable (K : Type) [Field K]

theorem positivePlane_eq_positiveSpace : positivePlane K = positiveSpace K 2 := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl) i <;> simp [e0, e1, Pi.single_apply]
  · rw [positiveSpace_finrank, positivePlane_finrank]

theorem crossingPlane_eq_crossingSpace : crossingPlane K = crossingSpace K 2 1 := by
  apply Submodule.eq_of_le_of_finrank_le
  · apply Submodule.span_le.mpr
    rintro v (rfl | rfl)
    · refine ⟨?_, ?_⟩
      · simp [e0, Pi.single_apply]
      · intro i _
        simp [e0, Pi.single_apply]
    · refine ⟨?_, ?_⟩
      · simp [f1, Pi.single_apply]
      · intro i hi
        simp [f1, Pi.single_apply, hi, Ne.symm hi]
  · rw [crossingSpace_finrank, crossingPlane_finrank]

theorem exists_normalize_rank_two (P : Submodule K (Index 2 → K))
    (hd : Module.finrank K P = 2) (hz : ∀ v ∈ P, splitQuadraticForm K 2 v = 0) :
    ∃ g : elementaryRootGroup K 2,
      P.map (naturalLinearHom K 2 g).toLinearMap = positiveSpace K 2 ∨
      ∃ j : Fin 2, P.map (naturalLinearHom K 2 g).toLinearMap = crossingSpace K 2 j := by
  obtain ⟨g, hg | hg⟩ := exists_elementary_plane_normal_form K P hd hz
  · exact ⟨g, Or.inl (hg.trans (positivePlane_eq_positiveSpace K))⟩
  · exact ⟨g, Or.inr ⟨1, hg.trans (crossingPlane_eq_crossingSpace K)⟩⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIsometryIndexRankTwoSpaces
