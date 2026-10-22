import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualCorrection
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualChart
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularPlaneOrbit
import SymmetricSubgroupAsymptotics.CFSGPolarCommonPointPlanes

/-! The corrected normalized residual chart gives q^4 distinct actual
original D root planes through the same original positive axis, for
rank>=5. The left inverse and fixed chart coordinate remove all scalar
fibres. Actual quadratic singularity is proved separately in char2. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualPlaneFamily
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDIndexResidualChart CFSGOrthogonalDIndexQuadraticCorrection
open CFSGOrthogonalDIndexSingularPlaneOrbit CFSGOrthogonalDIndexPlaneRootLine
open CFSGPolarCommonPointPlanes
variable (K : Type) [Field K]

def residualPlane (s : ℕ) (w : Index (s + 5) → K) (p : Fin 4 → K) :
    Submodule K (Index (s + 5) → K) :=
  pairPlane (Pi.single (Sum.inl 0) 1) (residualMap K (s + 3) w (normalizedChart K s p))

theorem residualPlane_injective (s : ℕ) (w : Index (s + 5) → K) :
    Function.Injective (residualPlane K s w) := by
  intro p q he
  obtain ⟨a, ha⟩ := pairPlane_eq_implies_proportional
    (Pi.single (Sum.inl (0 : Fin (s + 5))) 1)
    (residualMap K (s + 3) w) (twiceTailRestriction K (s + 3))
    (residualMap_leftInverse K (s + 3) w) (twiceTailRestriction_first K (s + 3))
    (normalizedChart K s p) (normalizedChart K s q) he
  exact normalizedChart_eq_of_proportional K s p q a ha

theorem residualPlane_range_card (s : ℕ) (w : Index (s + 5) → K) :
    Nat.card (Set.range (residualPlane K s w)) = Nat.card K ^ 4 :=
  (Nat.card_range_of_injective (residualPlane_injective K s w)).trans (parameter_card K)

theorem residualPlane_finrank (s : ℕ) (w : Index (s + 5) → K) (p : Fin 4 → K) :
    Module.finrank K (residualPlane K s w p) = 2 := by
  have hu : (Pi.single (Sum.inl (0 : Fin (s + 5))) (1 : K) : Index (s + 5) → K) ≠ 0 := by
    intro he
    have hh := congrFun he (Sum.inl 0)
    exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hh)
  apply pairPlane_finrank _ _ hu
  intro a he
  apply normalizedChart_ne_zero K s p
  have hh := congrArg (twiceTailRestriction K (s + 3)) he
  simpa only [residualMap_leftInverse, map_smul, twiceTailRestriction_first, smul_zero] using hh

theorem residualPlane_singular (s : ℕ) (w : Index (s + 5) → K) (p : Fin 4 → K) :
    ∀ z ∈ residualPlane K s w p, splitQuadraticForm K (s + 5) z = 0 := by
  apply singular_span_pair
  · exact positive_quadratic K (s + 5) 0
  · exact (residualMap_quadratic K (s + 3) w _).trans (normalizedChart_singular K s p)
  · exact residualMap_perp_positive K (s + 3) w _ 0 (Or.inl rfl)

theorem residualPlane_is_original_rootPlane (s : ℕ) (w : Index (s + 5) → K) (p : Fin 4 → K) :
    ∃ g : elementaryRootGroup K (s + 5), residualPlane K s w p =
      conjugateRootPlane K (s + 1) g :=
  exists_conjugateRootPlane_of_singular K (s + 1) _
    (residualPlane_finrank K s w p) (residualPlane_singular K s w p)

theorem residualPlane_perp_companion (s : ℕ) (w : Index (s + 5) → K)
    (hu : (splitQuadraticForm K (s + 5)).polarBilin w (Pi.single (Sum.inl 0) 1) = 0)
    (hw : (splitQuadraticForm K (s + 5)).polarBilin w
      (Pi.single (Sum.inl (tailSecondIndex (s + 3))) 1) ≠ 0)
    (p : Fin 4 → K) : ∀ z ∈ residualPlane K s w p,
      (splitQuadraticForm K (s + 5)).polarBilin w z = 0 := by
  intro z hz
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
  simp only [map_add, map_smul, hu,
    residualMap_perp_companion K (s + 3) w hw (normalizedChart K s p), smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualPlaneFamily
