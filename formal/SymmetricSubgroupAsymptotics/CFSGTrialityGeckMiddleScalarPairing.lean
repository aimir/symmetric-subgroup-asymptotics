import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeBracketLine
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoefficientSeparation
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A genuine scalar-valued alternating pairing on the original cube
coefficient space. The scalar is extracted from its proved highest-root
line, and primitive complementary coefficients establish nondegeneracy
over every coefficient field. This is not yet fixed-field descent. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleScalarPairing

open CFSGTrialityD4NormTwo CFSGTrialityD4PositiveRootOrbits CFSGTrialityD4MiddleCube
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleCubeSpanActions
open CFSGTrialityGeckMiddleCubeBracketLine CFSGTrialityGeckMiddleCubeCoefficientSeparation
open CFSGNormTwoCoordinateRootBracketTransport

local notation "A" => CartanMatrix.D 4
local notation "hd" => CartanMatrix.D_diag 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite
local notation "ho" => CartanMatrix.D_off_diag_nonpos 4
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _

def highestFunctional (K : Type) [Field K] : Mat K →ₗ[K] K :=
  Classical.choose (Module.Projective.exists_dual_eq_one K
    (selectedFieldCoefficient_ne_zero A hd hs hp ho K (longRoot 2)))

theorem highestFunctional_highest (K : Type) [Field K] :
    highestFunctional K (selectedFieldCoefficient A hd hs hp ho K (longRoot 2)) = 1 :=
  Classical.choose_spec (Module.Projective.exists_dual_eq_one K
    (selectedFieldCoefficient_ne_zero A hd hs hp ho K (longRoot 2)))

def cubePairing (K : Type) [Field K] : cubeSpan K →ₗ[K] cubeSpan K →ₗ[K] K where
  toFun u :=
    { toFun := fun v => highestFunctional K ⁅u.val, v.val⁆
      map_add' := by
        intro v w
        change highestFunctional K ⁅u.val, v.val + w.val⁆ = _
        rw [lie_add, map_add]
      map_smul' := by
        intro a v
        change highestFunctional K ⁅u.val, a • v.val⁆ = a • highestFunctional K ⁅u.val, v.val⁆
        rw [lie_smul, map_smul] }
  map_add' := by
    intro u v
    ext w
    change highestFunctional K ⁅u.val + v.val, w.val⁆ =
      highestFunctional K ⁅u.val, w.val⁆ + highestFunctional K ⁅v.val, w.val⁆
    rw [add_lie, map_add]
  map_smul' := by
    intro a u
    ext w
    change highestFunctional K ⁅a • u.val, w.val⁆ = a • highestFunctional K ⁅u.val, w.val⁆
    rw [smul_lie, map_smul]

theorem cubePairing_apply (K : Type) [Field K] (u v : cubeSpan K) :
    cubePairing K u v = highestFunctional K ⁅u.val, v.val⁆ := rfl

theorem matrix_bracket_eq_pairing_smul (K : Type) [Field K] (u v : cubeSpan K) :
    ⁅u.val, v.val⁆ = cubePairing K u v •
      selectedFieldCoefficient A hd hs hp ho K (longRoot 2) := by
  have hm := cube_bracket_mem_highest_line K u.val v.val u.property v.property
  change ⁅u.val, v.val⁆ ∈ Submodule.span K
    ({(selectedFieldCoefficient A hd hs hp ho K (longRoot 2) : Mat K)} : Set (Mat K)) at hm
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
  have hc : cubePairing K u v = a := by
    rw [cubePairing_apply, ← ha, map_smul, highestFunctional_highest]
    exact mul_one a
  rw [hc]
  exact ha.symm

theorem cubePairing_alternating (K : Type) [Field K] (u : cubeSpan K) :
    cubePairing K u u = 0 := by
  rw [cubePairing_apply, lie_self, map_zero]

theorem cubePairing_separating (K : Type) [Field K] (u : cubeSpan K)
    (hu : ∀ v, cubePairing K u v = 0) : u = 0 := by
  let lc : (Cube → K) →ₗ[K] Mat K := Fintype.linearCombination K (cubeCoefficient K)
  have hm : u.val ∈ lc.range := by
    change u.val ∈ (Fintype.linearCombination K (cubeCoefficient K)).range
    rw [Fintype.range_linearCombination]
    exact u.property
  obtain ⟨c, hc⟩ := hm
  have hz : ∀ b : Cube, ⁅∑ a, c a • cubeCoefficient K a, cubeCoefficient K b⁆ = 0 := by
    intro b
    have hsum : (∑ a, c a • cubeCoefficient K a) = u.val := hc
    rw [hsum]
    let v : cubeSpan K := ⟨cubeCoefficient K b, Submodule.subset_span (Set.mem_range_self b)⟩
    have he := matrix_bracket_eq_pairing_smul K u v
    rw [hu v, zero_smul] at he
    exact he
  have hcz := coefficients_zero_of_all_brackets_zero K c hz
  apply Subtype.ext
  change u.val = 0
  calc
    u.val = lc c := hc.symm
    _ = 0 := by rw [hcz, map_zero]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleScalarPairing
