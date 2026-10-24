import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLiePairing

/-! Complementary original root coefficients detect every cube coordinate.
The proof uses only a single finite-sum selection and integral unit signs;
there is no 64-entry pairing table or characteristic-dependent eigenvalue
argument. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoefficientSeparation

open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4CubeComplement CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleCubeLiePairing
open CFSGNormTwoCoordinateRootBracketTransport

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

theorem bracket_sum_complement (K : Type) [Field K] (c : Cube → K) (a : Cube) :
    ⁅∑ b, c b • cubeCoefficient K b, cubeCoefficient K (complement a)⁆ =
      c a • ⁅cubeCoefficient K a, cubeCoefficient K (complement a)⁆ := by
  rw [sum_lie]
  simp only [smul_lie]
  apply Finset.sum_eq_single a
  · intro b _ hba
    have hne : complement a ≠ complement b := by
      intro he
      exact hba (complement_involutive.injective he).symm
    rw [noncomplementary_coefficient_bracket K b (complement a) hne, smul_zero]
  · intro ha
    exact (ha (Finset.mem_univ a)).elim

theorem coefficients_zero_of_all_brackets_zero (K : Type) [Field K] (c : Cube → K)
    (hc : ∀ b : Cube, ⁅∑ a, c a • cubeCoefficient K a, cubeCoefficient K b⁆ = 0) :
    c = 0 := by
  funext a
  obtain ⟨ε, hε, hbr⟩ := complementary_coefficient_bracket a
  have h := hc (complement a)
  rw [bracket_sum_complement, hbr K] at h
  let E : CFSGTrialityGeckMiddleFirstLayer.Mat K :=
    selectedFieldCoefficient A hd hs hp ho K (longRoot 2)
  have hprod : (c a * (ε : K)) • E = 0 :=
    (smul_smul (c a) (ε : K) E).symm.trans h
  have he : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> simp
  have hzero : c a * (ε : K) = 0 :=
    (smul_eq_zero.mp hprod).resolve_right
      (selectedFieldCoefficient_ne_zero A hd hs hp ho K (longRoot 2))
  exact (mul_eq_zero.mp hzero).resolve_right he

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoefficientSeparation
