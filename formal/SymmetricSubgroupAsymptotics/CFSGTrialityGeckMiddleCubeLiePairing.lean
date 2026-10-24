import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubePairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleHighestSecondLayer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoordinates

/-! The primitive anti-diagonal pairing of the original cube coefficients
is read from actual group commutators by their degree-two matrix layer.
No explicit matrix-entry table or characteristic restriction is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLiePairing

open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4CubeComplement CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleCubePairing
open CFSGTrialityGeckMiddleHighestSecondLayer CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoCoordinateRootBracketTransport CFSGGradedMatrixCommutatorSecondLayer
open CFSGGradedMatrixSingleDegreeSpan
open CFSGGradedMatrixGroupFirstLayer

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem complementary_coefficient_bracket (a : Cube) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [Field K],
      ⁅cubeCoefficient K a, cubeCoefficient K (complement a)⁆ =
        (ε : K) • selectedFieldCoefficient A hd hs hp ho K (longRoot 2) := by
  obtain ⟨ε, hε, he⟩ := complementary_commutator_sign a
  refine ⟨ε, hε, ?_⟩
  intro K _
  let u : Raw K := selectedRootElement A hd hs hp ho K (cubeRoot a) 1
  let v : Raw K := selectedRootElement A hd hs hp ho K (cubeRoot (complement a)) 1
  have hu := middle_le_strict K
    (middle_root_mem K (cubeRoot a) (cubeRoot_positive a) (by rw [cubeRoot_middle]) 1)
  have hv := middle_le_strict K
    (middle_root_mem K (cubeRoot (complement a)) (cubeRoot_positive (complement a))
      (by rw [cubeRoot_middle]) 1)
  have h := commutator_secondLayer middleWeight u v hu hv
  have hc : u * v * u⁻¹ * v⁻¹ =
      selectedRootElement A hd hs hp ho K (longRoot 2) (ε : K) := by
    simpa only [mul_one] using he K 1 1
  let P : Raw K → Mat K := fun z => degreePart middleWeight (2 : ℤ)
    ((z.val : Mat K) - (1 : Mat K))
  have hproj := congrArg P hc
  have htop : P (selectedRootElement A hd hs hp ho K (longRoot 2) (ε : K)) =
      (ε : K) • selectedFieldCoefficient A hd hs hp ho K (longRoot 2) :=
    highest_secondLayer K (ε : K)
  have hbr := h.symm.trans (hproj.trans htop)
  have hua : firstLayer middleWeight u = cubeCoefficient K a :=
    (root_firstLayer K (cubeRoot a) (cubeRoot_middle a) 1).trans (one_smul K _)
  have hvb : firstLayer middleWeight v = cubeCoefficient K (complement a) :=
    (root_firstLayer K (cubeRoot (complement a)) (cubeRoot_middle (complement a)) 1).trans
      (one_smul K _)
  rw [hua, hvb] at hbr
  exact hbr

theorem noncomplementary_coefficient_bracket (K : Type) [Field K] (a b : Cube)
    (hab : b ≠ complement a) : ⁅cubeCoefficient K a, cubeCoefficient K b⁆ = 0 := by
  let u : Raw K := selectedRootElement A hd hs hp ho K (cubeRoot a) 1
  let v : Raw K := selectedRootElement A hd hs hp ho K (cubeRoot b) 1
  have hu := middle_le_strict K
    (middle_root_mem K (cubeRoot a) (cubeRoot_positive a) (by rw [cubeRoot_middle]) 1)
  have hv := middle_le_strict K
    (middle_root_mem K (cubeRoot b) (cubeRoot_positive b) (by rw [cubeRoot_middle]) 1)
  have h := commutator_secondLayer middleWeight u v hu hv
  have hc : u * v * u⁻¹ * v⁻¹ = 1 := by
    have hcomm : Commute u v := noncomplementary_commute K a b hab 1 1
    rw [hcomm.eq]
    group
  let P : Raw K → Mat K := fun z => degreePart middleWeight (2 : ℤ)
    ((z.val : Mat K) - (1 : Mat K))
  have hproj := congrArg P hc
  have hzero : P 1 = 0 := by
    change degreePart middleWeight (2 : ℤ) (((1 : Raw K).val : Mat K) - (1 : Mat K)) = 0
    rw [Units.val_one, sub_self, map_zero]
  have hbr := h.symm.trans (hproj.trans hzero)
  have hua : firstLayer middleWeight u = cubeCoefficient K a :=
    (root_firstLayer K (cubeRoot a) (cubeRoot_middle a) 1).trans (one_smul K _)
  have hvb : firstLayer middleWeight v = cubeCoefficient K b :=
    (root_firstLayer K (cubeRoot b) (cubeRoot_middle b) 1).trans (one_smul K _)
  rw [hua, hvb] at hbr
  exact hbr

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLiePairing
