import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLiePairing
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeSpanActions

/-! The bracket of arbitrary original cube coefficients lies on the
single primitive highest-root line. Two linear span inductions extend the
checked root-pair identities; no word enumeration or new group presentation
is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeBracketLine

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4MiddleCube
open CFSGTrialityD4CubeComplement CFSGTrialityGeckDiagramCovariance
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeSpanActions CFSGTrialityGeckMiddleCubeLiePairing
open CFSGNormTwoCoordinateRootBracketTransport

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def highestCoefficientLine (K : Type) [Field K] : Submodule K (Mat K) :=
  Submodule.span K ({(selectedFieldCoefficient A hd hs hp ho K (longRoot 2) : Mat K)} : Set (Mat K))

private theorem root_bracket_mem (K : Type) [Field K] (a b : Cube) :
    ⁅cubeCoefficient K a, cubeCoefficient K b⁆ ∈ highestCoefficientLine K := by
  by_cases hab : b = complement a
  · subst b
    obtain ⟨ε, _, hbr⟩ := complementary_coefficient_bracket a
    rw [hbr K]
    have hmem : (selectedFieldCoefficient A hd hs hp ho K (longRoot 2) : Mat K) ∈
        highestCoefficientLine K :=
      Submodule.subset_span (Set.mem_singleton _)
    exact (highestCoefficientLine K).smul_mem (ε : K) hmem
  · rw [noncomplementary_coefficient_bracket K a b hab]
    exact (highestCoefficientLine K).zero_mem

theorem cube_bracket_mem_highest_line (K : Type) [Field K] (M N : Mat K)
    (hM : M ∈ cubeSpan K) (hN : N ∈ cubeSpan K) :
    ⁅M, N⁆ ∈ highestCoefficientLine K := by
  induction hM using Submodule.span_induction with
  | mem M hM =>
    obtain ⟨a, rfl⟩ := hM
    induction hN using Submodule.span_induction with
    | mem N hN =>
      obtain ⟨b, rfl⟩ := hN
      exact root_bracket_mem K a b
    | zero => rw [lie_zero]; exact (highestCoefficientLine K).zero_mem
    | add N P _ _ hN hP =>
      rw [lie_add]
      exact (highestCoefficientLine K).add_mem hN hP
    | smul t N _ hN =>
      rw [lie_smul]
      exact (highestCoefficientLine K).smul_mem t hN
  | zero => rw [zero_lie]; exact (highestCoefficientLine K).zero_mem
  | add M P _ _ hM hP =>
    rw [add_lie]
    exact (highestCoefficientLine K).add_mem hM hP
  | smul t M _ hM =>
    rw [smul_lie]
    exact (highestCoefficientLine K).smul_mem t hM

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeBracketLine
