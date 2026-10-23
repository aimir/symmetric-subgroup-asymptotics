import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdges
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortComplementUnique
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixBlockProjection
import SymmetricSubgroupAsymptotics.CFSGAlgebraConjugationAction

/-! The actual canonical outer words act on cube first coefficients by
integral unit edge maps. Linearity is literal matrix conjugation; its
compatibility with the group first layer comes from block projection,
not an assumed linear structure on an abstract root quotient. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLinearEdges
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleRadicalQuotient CFSGTrialityGeckMiddleFirstLayer
open CFSGTrialityGeckMiddleCubeCoordinates CFSGTrialityGeckMiddleCubeEdges
open CFSGGradedMatrixSupport CFSGGradedMatrixSubgroups CFSGGradedMatrixGroupFirstLayer
open CFSGGradedMatrixBlockProjection
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

theorem outerWord_preserving (K : Type) [Field K] (j : Fin 3) (t : K) :
    outerWord K j t ∈ preservingUnits middleWeight :=
  CFSGTrialityGeckShortComplementUnique.outerGroup_le_preserving K
    (CFSGTrialityGeckShortComplementFactor.outer_root_mem K j t)

theorem cubeWord_strict (K : Type) [Field K] (a : Cube) (t : K) :
    cubeWord K a t ∈ strictUnits middleWeight :=
  middle_le_strict K (middle_root_mem K (cubeRoot a) (cubeRoot_positive a)
    (by rw [cubeRoot_middle]) t)

theorem cubeWord_firstLayer (K : Type) [Field K] (a : Cube) (t : K) :
    firstLayer middleWeight (cubeWord K a t) = t • cubeCoefficient K a :=
  root_firstLayer K (cubeRoot a) (cubeRoot_middle a) t

def outerLinear (K : Type) [Field K] (j : Fin 3) (t : K) : Mat K ≃ₗ[K] Mat K :=
  CFSGAlgebraConjugationAction.action K (Mat K) (outerWord K j t)

theorem zero_bit_linear_sign (a : Cube) (j : Fin 3) (hbit : a j = 0) :
    ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧ ∀ (K : Type) [Field K] (t : K),
      outerLinear K j t (cubeCoefficient K a) =
        cubeCoefficient K a + ((ε:K)*t) • cubeCoefficient K (Function.update a j 1) := by
  obtain ⟨ε, hε, hedge⟩ := zero_bit_conjugation_sign a j hbit
  refine ⟨ε, hε, ?_⟩
  intro K _ t
  have hp := outerWord_preserving K j t
  have hpinv := (preservingUnits (K := K) middleWeight).inv_mem hp
  have h := congrArg (fun z : UnitsD4 K => firstLayer middleWeight z) (hedge K t 1)
  dsimp only at h
  rw [firstLayer_conjugate K middleWeight _ _ hp hpinv,
    firstLayer_mul middleWeight _ _
      (cubeWord_strict K (Function.update a j 1) ((ε:K)*(1*t))) (cubeWord_strict K a 1)] at h
  simp only [cubeWord_firstLayer, one_smul, one_mul] at h
  change outerLinear K j t (cubeCoefficient K a) =
    ((ε:K)*t) • cubeCoefficient K (Function.update a j 1) + cubeCoefficient K a at h
  exact h.trans (add_comm _ _)

theorem one_bit_linear_fixed (K : Type) [Field K] (a : Cube) (j : Fin 3)
    (hbit : a j = 1) (t : K) :
    outerLinear K j t (cubeCoefficient K a) = cubeCoefficient K a := by
  have hp := outerWord_preserving K j t
  have hpinv := (preservingUnits (K := K) middleWeight).inv_mem hp
  have hcomm := one_bit_commutes K a j hbit t 1
  have he : outerWord K j t * cubeWord K a 1 * (outerWord K j t)⁻¹ = cubeWord K a 1 := by
    rw [hcomm.eq]
    group
  have h := congrArg (fun z : UnitsD4 K => firstLayer middleWeight z) he
  dsimp only at h
  rw [firstLayer_conjugate K middleWeight _ _ hp hpinv] at h
  simp only [cubeWord_firstLayer, one_smul] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeLinearEdges
