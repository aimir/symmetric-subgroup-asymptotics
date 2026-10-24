import SymmetricSubgroupAsymptotics.CFSGTrialityD4CubeComplement
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleRadicalCommutators

/-! Literal primitive commutator coefficients for complementary D4 cube
roots, together with commutation for all noncomplementary vertices. The
coefficients are integral units, valid in characteristics two and three.
No fixed quotient lifting or Heisenberg recognition is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubePairing

open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGTrialityD4NormTwo CFSGTrialityD4MiddleCube CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4CubeComplement CFSGTrialityGeckDiagramCovariance
open CFSGNormTwoCoordinatePositivePairCollecting CFSGNormTwoCoordinateSelectedRootElement

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (Roots A) := Classical.decEq _

theorem complementary_sumRoot (a : Cube) :
    sumRoot A hs (cubeRoot a) (cubeRoot (complement a))
      ((cube_pairing_eq_neg_one_iff a (complement a)).mpr rfl) = longRoot 2 := by
  apply Subtype.ext
  exact complementary_root_sum a

theorem complementary_commutator_sign (a : Cube) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ (K : Type) [Field K] (s t : K),
      selectedRootElement A hd hs hp ho K (cubeRoot a) s *
        selectedRootElement A hd hs hp ho K (cubeRoot (complement a)) t *
        (selectedRootElement A hd hs hp ho K (cubeRoot a) s)⁻¹ *
        (selectedRootElement A hd hs hp ho K (cubeRoot (complement a)) t)⁻¹ =
      selectedRootElement A hd hs hp ho K (longRoot 2) ((ε : K) * (s * t)) := by
  obtain ⟨ε, hε, he⟩ := positive_pair_commutator_sign A hd hs hp ho
    (cubeRoot a) (cubeRoot (complement a)) (cubeRoot_positive a)
    (cubeRoot_positive (complement a))
    ((cube_pairing_eq_neg_one_iff a (complement a)).mpr rfl)
  refine ⟨ε, hε, ?_⟩
  intro K _ s t
  have h := he K s t
  rw [complementary_sumRoot] at h
  exact h

private theorem distinct_noncomplementary_pairing (a b : Cube)
    (hne : b ≠ a) (hab : b ≠ complement a) :
    integerPairing A (cubeRoot a).val (cubeRoot b).val = 0 ∨
      integerPairing A (cubeRoot a).val (cubeRoot b).val = 1 := by
  have h : ∀ c d : Cube, d ≠ c → d ≠ complement c →
      integerPairing A (cubeRoot c).val (cubeRoot d).val = 0 ∨
        integerPairing A (cubeRoot c).val (cubeRoot d).val = 1 := by decide +kernel
  exact h a b hne hab

theorem noncomplementary_commute (K : Type) [Field K] (a b : Cube)
    (hab : b ≠ complement a) (s t : K) :
    Commute (selectedRootElement A hd hs hp ho K (cubeRoot a) s)
      (selectedRootElement A hd hs hp ho K (cubeRoot b) t) := by
  by_cases hba : b = a
  · subst b
    exact CFSGNormTwoCoordinateSelectedRootAdditive.selectedRootElement_commute
      A hd hs hp ho K (cubeRoot a) s t
  · exact CFSGNormTwoCoordinatePositivePairCommute.positive_pair_commute A hd hs hp ho K
      (cubeRoot a) (cubeRoot b) (cubeRoot_positive a) (cubeRoot_positive b)
      (distinct_noncomplementary_pairing a b hba hab) s t

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubePairing
