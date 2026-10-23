import SymmetricSubgroupAsymptotics.CFSGTrialityFrobeniusSeparation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLowestBracketRaise
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator

/-! Commuting with every literal short Frobenius-orbit word forces the
three OUTER simple brackets of the lowest height part to vanish. This
is a lowest-layer calculation, not full ambient-U commutant recognition. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortLowestCommutant
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckFixedRootWords CFSGTrialityFrobeniusSeparation
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckHeightSupport CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoCoordinateHeight CFSGNormTwoCoordinateRootHeightLeading
open CFSGNormTwoGeckPositiveFirstLayer CFSGNormTwoGeckIntegralRealization
open CFSGGradedMatrixGroupFirstLayer CFSGGradedMatrixLieFirstLayer
open CFSGGradedMatrixSubgroups CFSGGradedMatrixHighLayerProducts
open CFSGGradedMatrixLowestProduct CFSGGradedMatrixSingleDegreeSpan
open CFSGSerreOrdinaryTwists
local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local notation "w" => heightWeight A hd hs hp ho
local instance : DecidableEq (Roots A) := Classical.decEq _

private theorem weight_eq : weight A hs hp Base coordinateHeight = w := by
  funext j
  rcases j with j | j
  · simp [weight,heightWeight,latticeWeight,CFSGIntegerHeightSign.height]
  · rfl

theorem simple_strict_height (K : Type) [Field K] (i : Fin 4) (t : K) :
    canonicalRoot rawData K false i t ∈ strictUnits w := by
  have h := simple_strict A hs hp Base Index coordinateHeight
    (simple_height A hd hs hp ho) K i t
  rwa [weight_eq] at h

theorem simple_first_height (K : Type) [Field K] (i : Fin 4) (t : K) :
    firstLayer w (canonicalRoot rawData K false i t) = t • fieldRoot rawData K false i := by
  have h := simple_firstLayer A hs hp Base Index coordinateHeight
    (simple_height A hd hs hp ho) K i t
  rwa [weight_eq] at h

theorem shortOrbit_strict (K : Type) [Field K] (sigma : K ≃+* K) (t : K) :
    shortOrbit K sigma false t ∈ strictUnits w :=
  (strictUnits w).mul_mem
    ((strictUnits w).mul_mem (simple_strict_height K 0 t)
      (simple_strict_height K 2 (sigma t)))
    (simple_strict_height K 3 (sigma (sigma t)))

theorem shortOrbit_first_height (K : Type) [Field K] (sigma : K ≃+* K) (t : K) :
    firstLayer w (shortOrbit K sigma false t) =
      t • fieldRoot rawData K false 0 + sigma t • fieldRoot rawData K false 2 +
        sigma (sigma t) • fieldRoot rawData K false 3 := by
  change firstLayer w (canonicalRoot rawData K false 0 t *
      canonicalRoot rawData K false 2 (sigma t) *
      canonicalRoot rawData K false 3 (sigma (sigma t))) = _
  rw [firstLayer_mul w _ _
    ((strictUnits w).mul_mem (simple_strict_height K 0 t) (simple_strict_height K 2 (sigma t)))
      (simple_strict_height K 3 (sigma (sigma t))),
    firstLayer_mul w _ _ (simple_strict_height K 0 t) (simple_strict_height K 2 (sigma t)),
    simple_first_height,simple_first_height,simple_first_height]

theorem shortOrbit_below_one (K : Type) [Field K] (sigma : K ≃+* K) (t : K) :
    BelowCut w 1 ((shortOrbit K sigma false t : Matrix GeckIndex GeckIndex K)-1) := by
  have hpositive := deviation_positive w (shortOrbit K sigma false t) (shortOrbit_strict K sigma t)
  intro i j hij
  exact hpositive i j (by omega)

def lowestPart (K : Type) [Field K] (h : ℤ) (u : (Matrix GeckIndex GeckIndex K)ˣ) :
    Matrix GeckIndex GeckIndex K :=
      degreePart (I := GeckIndex) w h ((u : Matrix GeckIndex GeckIndex K)-1)

theorem short_commutation_lowest_brackets (q : CFSG.PrimePower) (h : ℤ)
    (u : (Matrix GeckIndex GeckIndex (q.Extension 3))ˣ)
    (hu : BelowCut w h ((u : Matrix GeckIndex GeckIndex (q.Extension 3))-1))
    (hc : ∀ t : q.Extension 3, u*shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t =
      shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) false t*u) :
    ⁅fieldRoot rawData (q.Extension 3) false 0,lowestPart (q.Extension 3) h u⁆=0 ∧
    ⁅fieldRoot rawData (q.Extension 3) false 2,lowestPart (q.Extension 3) h u⁆=0 ∧
    ⁅fieldRoot rawData (q.Extension 3) false 3,lowestPart (q.Extension 3) h u⁆=0 := by
  let K := q.Extension 3
  let sigma := definingFieldAutomorphism q 3
  let L := lowestPart K h u
  have hb (t : K) : t • ⁅fieldRoot rawData K false 0,L⁆ +
      sigma t • ⁅fieldRoot rawData K false 2,L⁆ +
      sigma (sigma t) • ⁅fieldRoot rawData K false 3,L⁆ = 0 := by
    have hh := commuting_units_lowest_parts (I := GeckIndex) w h 1 u (shortOrbit K sigma false t) hu
      (shortOrbit_below_one K sigma t) (hc t)
    have hz : ⁅firstLayer (I := GeckIndex) w (shortOrbit K sigma false t),L⁆ = 0 := sub_eq_zero.mpr hh.symm
    rw [shortOrbit_first_height] at hz
    simpa only [add_lie,smul_lie] using hz
  have hij (i j : GeckIndex) :
      ⁅fieldRoot rawData K false 0,L⁆ i j = 0 ∧
      ⁅fieldRoot rawData K false 2,L⁆ i j = 0 ∧
      ⁅fieldRoot rawData K false 3,L⁆ i j = 0 := by
    apply actual_frobenius_coefficients_zero q
    intro t
    have ht := congrArg (fun M : Matrix GeckIndex GeckIndex K => M i j) (hb t)
    change t * ⁅fieldRoot rawData K false 0,L⁆ i j +
      sigma t * ⁅fieldRoot rawData K false 2,L⁆ i j +
      sigma (sigma t) * ⁅fieldRoot rawData K false 3,L⁆ i j = 0 at ht
    simpa only [mul_comm] using ht
  refine ⟨?_,?_,?_⟩
  · apply Matrix.ext
    intro i j
    exact (hij i j).1
  · apply Matrix.ext
    intro i j
    exact (hij i j).2.1
  · apply Matrix.ext
    intro i j
    exact (hij i j).2.2

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortLowestCommutant
