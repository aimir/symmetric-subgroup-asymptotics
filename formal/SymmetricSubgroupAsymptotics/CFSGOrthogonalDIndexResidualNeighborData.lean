import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualPlaneFamily
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane

/-! Exact original common-neighbour data for the corrected q^4 chart
after a singular-pair frame is normalized. The companion pairs nontrivially
with the second positive axis, so each chart plane is distinct from both
original planes. Actual Q-singularity is retained in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborData
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexTailCoordinates
open CFSGOrthogonalDIndexBundledQuadratic CFSGOrthogonalDIndexResidualCorrection
open CFSGOrthogonalDIndexResidualChart CFSGOrthogonalDIndexResidualPlaneFamily
open CFSGOrthogonalDIndexQuadraticCorrection CFSGOrthogonalDIndexQuadraticNeighborPlane
open CFSGPolarCommonPointPlanes
variable (K : Type) [Field K]

def axis0 (s : ℕ) : Index (s + 5) → K := Pi.single (Sum.inl 0) 1
def axis1 (s : ℕ) : Index (s + 5) → K := Pi.single (Sum.inl (tailSecondIndex (s + 3))) 1
def leftPlane (s : ℕ) : Submodule K (Index (s + 5) → K) := pairPlane (axis0 K s) (axis1 K s)
def rightPlane (s : ℕ) (w : Index (s + 5) → K) : Submodule K (Index (s + 5) → K) :=
  pairPlane (axis0 K s) w

private theorem axis0_ne_zero (s : ℕ) : axis0 K s ≠ 0 := by
  intro he
  have hh := congrFun he (Sum.inl 0)
  exact one_ne_zero (by simpa only [axis0, Pi.single_eq_same, Pi.zero_apply] using hh)

private theorem axes_polar_zero (s : ℕ) :
    (splitQuadraticForm K (s + 5)).polarBilin (axis0 K s) (axis1 K s) = 0 := by
  rw [axis0, positive_polar]
  simp only [axis1, Pi.single_apply, Sum.inr_ne_inl, if_false]

private theorem axes_reverse_polar_zero (s : ℕ) :
    (splitQuadraticForm K (s + 5)).polarBilin (axis1 K s) (axis0 K s) = 0 := by
  exact (QuadraticMap.polar_comm (splitQuadraticForm K (s + 5) :
    (Index (s + 5) → K) → K) _ _).trans (axes_polar_zero K s)

theorem leftPlane_finrank (s : ℕ) : Module.finrank K (leftPlane K s) = 2 := by
  apply pairPlane_finrank _ _ (axis0_ne_zero K s)
  intro a he
  have hh := congrFun he (Sum.inl (tailSecondIndex (s + 3)))
  have hn : (0 : Fin (s + 5)) ≠ tailSecondIndex (s + 3) := by
    intro he
    have hv := congrArg Fin.val he
    change 0 = 1 at hv
    omega
  have hz : (1 : K) = 0 := by simpa [axis0, axis1, Pi.single_apply, hn, Ne.symm hn] using hh
  exact one_ne_zero hz

theorem leftPlane_singular (s : ℕ) :
    ∀ x ∈ leftPlane K s, splitQuadraticForm K (s + 5) x = 0 :=
  singular_span_pair _ _ _ (positive_quadratic K (s + 5) 0)
    (positive_quadratic K (s + 5) (tailSecondIndex (s + 3))) (axes_polar_zero K s)

theorem rightPlane_finrank (s : ℕ) (w : Index (s + 5) → K)
    (hw : (splitQuadraticForm K (s + 5)).polarBilin w (axis1 K s) ≠ 0) :
    Module.finrank K (rightPlane K s w) = 2 := by
  apply pairPlane_finrank _ _ (axis0_ne_zero K s)
  intro a he
  apply hw
  simp only [he, map_smul, LinearMap.smul_apply, axes_polar_zero K s, smul_zero]

theorem residualVector_not_mem_left (s : ℕ) (w : Index (s + 5) → K) (p : Fin 4 → K) :
    residualMap K (s + 3) w (normalizedChart K s p) ∉ leftPlane K s := by
  intro hz
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hz
  have hh := congrArg (twiceTailRestriction K (s + 3)) he
  have hzero : normalizedChart K s p = 0 := by
    simpa only [map_add, map_smul, axis0, axis1, twiceTailRestriction_first,
      twiceTailRestriction_second, smul_zero, zero_add, residualMap_leftInverse] using hh.symm
  exact normalizedChart_ne_zero K s p hzero

theorem residualVector_not_mem_right (s : ℕ) (w : Index (s + 5) → K)
    (hw : (splitQuadraticForm K (s + 5)).polarBilin w (axis1 K s) ≠ 0) (p : Fin 4 → K) :
    residualMap K (s + 3) w (normalizedChart K s p) ∉ rightPlane K s w := by
  intro hz
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hz
  let B := (splitQuadraticForm K (s + 5)).polarBilin
  have hc : B (axis1 K s) w ≠ 0 := by
    intro hc
    exact hw ((QuadraticMap.polar_comm (splitQuadraticForm K (s + 5) :
      (Index (s + 5) → K) → K) _ _).trans hc)
  have hh := congrArg (fun z => B (axis1 K s) z) he
  dsimp only at hh
  have hbp : B (axis1 K s) (residualMap K (s + 3) w (normalizedChart K s p)) = 0 :=
    residualMap_perp_positive K (s + 3) w _ _ (Or.inr rfl)
  have h10 : B (axis1 K s) (axis0 K s) = 0 := axes_reverse_polar_zero K s
  have hbc : b * B (axis1 K s) w = 0 := by
    simpa only [map_add, map_smul, h10, smul_zero,
      zero_add, smul_eq_mul, mul_zero, hbp] using hh
  have hb : b = 0 := (mul_eq_zero.mp hbc).resolve_right hc
  apply residualVector_not_mem_left K s w p
  rw [← he, hb, zero_smul, add_zero]
  exact (leftPlane K s).smul_mem a (Submodule.subset_span (Or.inl rfl))

theorem residualPlane_common_neighbor_data (s : ℕ) (w : Index (s + 5) → K)
    (hws : splitQuadraticForm K (s + 5) w = 0)
    (hwu : (splitQuadraticForm K (s + 5)).polarBilin w (axis0 K s) = 0)
    (hw : (splitQuadraticForm K (s + 5)).polarBilin w (axis1 K s) ≠ 0)
    (p : Fin 4 → K) :
    (leftPlane K s ≠ residualPlane K s w p ∧
      Module.finrank K ↥(leftPlane K s ⊓ residualPlane K s w p) = 1 ∧
      ∀ z ∈ leftPlane K s ⊔ residualPlane K s w p, splitQuadraticForm K (s + 5) z = 0) ∧
    (rightPlane K s w ≠ residualPlane K s w p ∧
      Module.finrank K ↥(rightPlane K s w ⊓ residualPlane K s w p) = 1 ∧
      ∀ z ∈ rightPlane K s w ⊔ residualPlane K s w p, splitQuadraticForm K (s + 5) z = 0) := by
  let z := residualMap K (s + 3) w (normalizedChart K s p)
  have hz : splitQuadraticForm K (s + 5) z = 0 :=
    (residualMap_quadratic K (s + 3) w _).trans (normalizedChart_singular K s p)
  have hu0 := positive_quadratic K (s + 5) (0 : Fin (s + 5))
  have huw : (splitQuadraticForm K (s + 5)).polarBilin (axis0 K s) w = 0 :=
    (QuadraticMap.polar_comm (splitQuadraticForm K (s + 5) :
      (Index (s + 5) → K) → K) _ _).trans hwu
  have hQ : ∀ x ∈ rightPlane K s w, splitQuadraticForm K (s + 5) x = 0 :=
    singular_span_pair _ _ _ hu0 hws huw
  have h0z : (splitQuadraticForm K (s + 5)).polarBilin (axis0 K s) z = 0 :=
    residualMap_perp_positive K (s + 3) w _ _ (Or.inl rfl)
  have h1z : (splitQuadraticForm K (s + 5)).polarBilin (axis1 K s) z = 0 :=
    residualMap_perp_positive K (s + 3) w _ _ (Or.inr rfl)
  have hwz : (splitQuadraticForm K (s + 5)).polarBilin w z = 0 :=
    residualMap_perp_companion K (s + 3) w hw _
  constructor
  · apply quadratic_pairPlane_adjacent_data _ _ (leftPlane_finrank K s) (leftPlane_singular K s)
      _ _ (Submodule.subset_span (Or.inl rfl)) (axis0_ne_zero K s) hz
      (residualVector_not_mem_left K s w p)
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h0z, h1z, smul_zero, add_zero]
  · apply quadratic_pairPlane_adjacent_data _ _ (rightPlane_finrank K s w hw) hQ
      _ _ (Submodule.subset_span (Or.inl rfl)) (axis0_ne_zero K s) hz
      (residualVector_not_mem_right K s w hw p)
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h0z, hwz, smul_zero, add_zero]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexResidualNeighborData
