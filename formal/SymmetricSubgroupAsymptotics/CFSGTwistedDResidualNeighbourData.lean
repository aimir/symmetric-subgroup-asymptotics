import SymmetricSubgroupAsymptotics.CFSGTwistedDResidualCorrection
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPointCharts
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularDimensionBound
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexQuadraticNeighborPlane

/-! Corrected normalized fixed-field singular vectors produce common
adjacent planes for the first positive plane and an actual nonorthogonal
companion plane. The exact twice-tail retains the normalized parameters. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDResidualNeighbourData
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDHighestPairOperator
open CFSGTwistedDSingularPlaneOrbit CFSGTwistedDDoubleTailEmbedding
open CFSGTwistedDResidualCorrection CFSGTwistedDSingularPointCharts CFSGTwistedA2FixedField
open CFSGPolarCommonPointPlanes CFSGOrthogonalDIndexQuadraticCorrection
open CFSGOrthogonalDIndexQuadraticNeighborPlane

local instance (n : ℕ) (q : CFSG.PrimePower) :
    Module.Finite (fixedField q) (fixedSpace n q) := Module.Finite.of_finite

def rightPlane (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q) :
    Submodule (fixedField q) (fixedSpace (s + 2) q) := pairPlane (firstVector s q) w

def residualPlane (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q)
    (p : Parameters s q) : Submodule (fixedField q) (fixedSpace (s + 2) q) :=
  pairPlane (firstVector s q) (residualMap s q w (chart s q p))

private theorem first_nonzero (s : ℕ) (q : CFSG.PrimePower) : firstVector s q ≠ 0 :=
  CFSGTwistedDSingularDimensionBound.firstAxis_nonzero (s + 2) q

theorem rightPlane_finrank (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0) :
    Module.finrank (fixedField q) (rightPlane s q w) = 2 := by
  apply pairPlane_finrank _ _ (first_nonzero s q)
  intro a he
  apply hw
  simp only [he, map_smul, LinearMap.smul_apply, (axes_polar_zero s q).1, smul_zero]

theorem residualVector_not_mem_left (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q) (p : Parameters s q) :
    residualMap s q w (chart s q p) ∉ standardRootPlane s q := by
  intro hz
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hz
  have hh := congrArg (doubleRestriction s q) he
  have hzero : chart s q p = 0 := by
    simpa only [map_add, map_smul, doubleRestriction_first, doubleRestriction_second,
      smul_zero, zero_add, residualMap_leftInverse] using hh.symm
  exact chart_nonzero s q p hzero

theorem residualVector_not_mem_right (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0)
    (p : Parameters s q) : residualMap s q w (chart s q p) ∉ rightPlane s q w := by
  intro hz
  obtain ⟨a, b, he⟩ := Submodule.mem_span_pair.mp hz
  let B := (fixedQuadraticForm (s + 2) q).polarBilin
  have hc : B (secondVector s q) w ≠ 0 := by
    intro hc
    exact hw ((QuadraticMap.polar_comm
      (fixedQuadraticForm (s + 2) q : _ → fixedField q) _ _).trans hc)
  have hh := congrArg (fun z => B (secondVector s q) z) he
  dsimp only at hh
  have hbp : B (secondVector s q) (residualMap s q w (chart s q p)) = 0 :=
    residualMap_perp_second s q w _
  have h10 : B (secondVector s q) (firstVector s q) = 0 :=
    (QuadraticMap.polar_comm (fixedQuadraticForm (s + 2) q : _ → fixedField q) _ _).trans
      (axes_polar_zero s q).1
  have hbc : b * B (secondVector s q) w = 0 := by
    simpa only [map_add, map_smul, h10, smul_zero,
      zero_add, smul_eq_mul, mul_zero, hbp] using hh
  have hb : b = 0 := (mul_eq_zero.mp hbc).resolve_right hc
  apply residualVector_not_mem_left s q w p
  rw [← he, hb, zero_smul, add_zero]
  exact (standardRootPlane s q).smul_mem a (Submodule.subset_span (Or.inl rfl))

theorem residualPlane_common_neighbour_data (s : ℕ) (q : CFSG.PrimePower)
    (w : fixedSpace (s + 2) q)
    (hws : fixedQuadraticForm (s + 2) q w = 0)
    (hwu : (fixedQuadraticForm (s + 2) q).polarBilin w (firstVector s q) = 0)
    (hw : (fixedQuadraticForm (s + 2) q).polarBilin w (secondVector s q) ≠ 0)
    (p : Parameters s q) :
    (standardRootPlane s q ≠ residualPlane s q w p ∧
      Module.finrank (fixedField q)
        (standardRootPlane s q ⊓ residualPlane s q w p : Submodule (fixedField q) _) = 1 ∧
      ∀ z ∈ standardRootPlane s q ⊔ residualPlane s q w p,
        fixedQuadraticForm (s + 2) q z = 0) ∧
    (rightPlane s q w ≠ residualPlane s q w p ∧
      Module.finrank (fixedField q)
        (rightPlane s q w ⊓ residualPlane s q w p : Submodule (fixedField q) _) = 1 ∧
      ∀ z ∈ rightPlane s q w ⊔ residualPlane s q w p,
        fixedQuadraticForm (s + 2) q z = 0) := by
  let z := residualMap s q w (chart s q p)
  have hz : fixedQuadraticForm (s + 2) q z = 0 :=
    (residualMap_quadratic s q w _).trans (chart_singular s q p)
  have hu0 : fixedQuadraticForm (s + 2) q (firstVector s q) = 0 :=
    standardRootPlane_singular s q _ (Submodule.subset_span (Or.inl rfl))
  have huw : (fixedQuadraticForm (s + 2) q).polarBilin (firstVector s q) w = 0 :=
    (QuadraticMap.polar_comm (fixedQuadraticForm (s + 2) q : _ → fixedField q) _ _).trans hwu
  have hQ : ∀ x ∈ rightPlane s q w, fixedQuadraticForm (s + 2) q x = 0 :=
    singular_span_pair _ _ _ hu0 hws huw
  have h0z := residualMap_perp_first s q w (chart s q p)
  have h1z := residualMap_perp_second s q w (chart s q p)
  have hwz := residualMap_perp_companion s q w hw (chart s q p)
  constructor
  · apply quadratic_pairPlane_adjacent_data _ _ (standardRootPlane_finrank s q)
      (standardRootPlane_singular s q) _ _ (Submodule.subset_span (Or.inl rfl))
      (first_nonzero s q) hz (residualVector_not_mem_left s q w p)
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    dsimp only [z]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h0z, h1z, smul_zero, add_zero]
  · apply quadratic_pairPlane_adjacent_data _ _ (rightPlane_finrank s q w hw) hQ
      _ _ (Submodule.subset_span (Or.inl rfl)) (first_nonzero s q) hz
      (residualVector_not_mem_right s q w hw p)
    intro x hx
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
    dsimp only [z]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      h0z, hwz, smul_zero, add_zero]

theorem residualPlane_injective (s : ℕ) (q : CFSG.PrimePower) (w : fixedSpace (s + 2) q) :
    Function.Injective (residualPlane s q w) := by
  intro p p' he
  obtain ⟨a, ha⟩ := pairPlane_eq_implies_proportional (firstVector s q)
    (residualMap s q w) (doubleRestriction s q) (residualMap_leftInverse s q w)
    (doubleRestriction_first s q) (chart s q p) (chart s q p') he
  have hv := congrArg (fun v : fixedSpace s q => v.val (Sum.inr 0)) ha
  change (chart s q p).val (Sum.inr 0) =
    (a : q.Extension 2) * (chart s q p').val (Sum.inr 0) at hv
  rw [chart_normalized, chart_normalized, mul_one] at hv
  have ha1 : a = 1 := Subtype.ext hv.symm
  rw [ha1, one_smul] at ha
  exact chart_injective s q ha

end SymmetricSubgroupAsymptotics.CFSGTwistedDResidualNeighbourData
