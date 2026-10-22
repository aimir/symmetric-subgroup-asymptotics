import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticStarPairs
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection
import SymmetricSubgroupAsymptotics.CFSGTwoDimensionalCompanion
import Mathlib.Tactic.FinCases

/-! The two literal singular-plane directions through e0 in the
split D2 residual four-space. This is quadratic, valid over F2 as well,
and is the first coordinate step towards the two residual rulings.
No triality action or global coherence is assumed by this lemma. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexQuadraticForm CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDIndexQuadraticNeighborPlane CFSGOrthogonalDIndexQuadraticCorrection
open CFSGTwoDimensionalSubmoduleBasis CFSGPolarCommonPointPlanes
variable (K : Type) [Field K]

def e0 : Index 2 → K := Pi.single (Sum.inl 0) 1
def e1 : Index 2 → K := Pi.single (Sum.inl 1) 1
def f1 : Index 2 → K := Pi.single (Sum.inr 1) 1
def positivePlane : Submodule K (Index 2 → K) := Submodule.span K {e0 K, e1 K}
def crossingPlane : Submodule K (Index 2 → K) := Submodule.span K {e0 K, f1 K}

theorem e0_ne_zero : e0 K ≠ 0 := by
  intro he
  have hh := congrFun he (Sum.inl 0)
  exact one_ne_zero (by simpa only [e0, Pi.single_eq_same, Pi.zero_apply] using hh)

theorem positivePlane_finrank : Module.finrank K (positivePlane K) = 2 := by
  apply pairPlane_finrank (e0 K) (e1 K) (e0_ne_zero K)
  intro a he
  have hh := congrFun he (Sum.inl 1)
  have hz : (1 : K) = 0 := by simpa [e0, e1, Pi.single_apply] using hh
  exact one_ne_zero hz

theorem crossingPlane_finrank : Module.finrank K (crossingPlane K) = 2 := by
  apply pairPlane_finrank (e0 K) (f1 K) (e0_ne_zero K)
  intro a he
  have hh := congrFun he (Sum.inr 1)
  have hz : (1 : K) = 0 := by simpa [e0, f1, Pi.single_apply] using hh
  exact one_ne_zero hz

theorem positivePlane_singular : ∀ x ∈ positivePlane K, splitQuadraticForm K 2 x = 0 := by
  apply singular_span_pair
  · exact positive_quadratic K 2 0
  · exact positive_quadratic K 2 1
  · dsimp only [e0]
    rw [positive_polar]
    simp only [e1, Pi.single_apply, Sum.inr_ne_inl, if_false]

theorem crossingPlane_singular : ∀ x ∈ crossingPlane K, splitQuadraticForm K 2 x = 0 := by
  apply singular_span_pair
  · exact positive_quadratic K 2 0
  · rw [splitQuadraticForm_apply]
    simp [f1, splitQ, leftPart, rightPart, dotProduct, Pi.single_apply]
  · dsimp only [e0]
    rw [positive_polar]
    simp [f1, Pi.single_apply]

theorem negative_head_zero_decomposition (w : Index 2 → K) (hw : w (Sum.inr 0) = 0) :
    w = w (Sum.inl 0) • e0 K + w (Sum.inl 1) • e1 K + w (Sum.inr 1) • f1 K := by
  funext x
  rcases x with i | i
  · fin_cases i <;> simp [e0, e1, f1]
  · fin_cases i <;> simp [e0, e1, f1, hw]

theorem singular_plane_through_e0 (P : Submodule K (Index 2 → K))
    (hP : Module.finrank K P = 2) (hPs : ∀ x ∈ P, splitQuadraticForm K 2 x = 0)
    (hu : e0 K ∈ P) : P = positivePlane K ∨ P = crossingPlane K := by
  obtain ⟨w, hw, _, hspan⟩ := exists_companion P hP (e0 K) hu (e0_ne_zero K)
  have hw0 : w (Sum.inr 0) = 0 := by
    have hh := polar_zero_of_singular (splitQuadraticForm K 2) P hPs (e0 K) w hu hw
    change (splitQuadraticForm K 2).polarBilin (Pi.single (Sum.inl (0 : Fin 2)) 1) w = 0 at hh
    rwa [positive_polar] at hh
  have hprod : w (Sum.inl 1) * w (Sum.inr 1) = 0 := by
    have hh := hPs w hw
    rw [splitQuadraticForm_apply] at hh
    change (∑ i : Fin 2, w (Sum.inl i) * w (Sum.inr i)) = 0 at hh
    rwa [Fin.sum_univ_two, hw0, mul_zero, zero_add] at hh
  have he := negative_head_zero_decomposition K w hw0
  rcases mul_eq_zero.mp hprod with hp | hn
  · right
    have hle : P ≤ crossingPlane K := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro x (rfl | rfl)
      · exact Submodule.subset_span (Or.inl rfl)
      · rw [he, hp, zero_smul, add_zero]
        exact (crossingPlane K).add_mem
          ((crossingPlane K).smul_mem _ (Submodule.subset_span (Or.inl rfl)))
          ((crossingPlane K).smul_mem _ (Submodule.subset_span (Or.inr rfl)))
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [crossingPlane_finrank, hP])
  · left
    have hle : P ≤ positivePlane K := by
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro x (rfl | rfl)
      · exact Submodule.subset_span (Or.inl rfl)
      · rw [he, hn, zero_smul, add_zero]
        exact (positivePlane K).add_mem
          ((positivePlane K).smul_mem _ (Submodule.subset_span (Or.inl rfl)))
          ((positivePlane K).smul_mem _ (Submodule.subset_span (Or.inr rfl)))
    exact Submodule.eq_of_le_of_finrank_le hle (by rw [positivePlane_finrank, hP])

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Coordinates
