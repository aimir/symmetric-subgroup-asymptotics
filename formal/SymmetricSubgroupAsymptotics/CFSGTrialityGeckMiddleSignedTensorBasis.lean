import SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleCubeEdgeOperators
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! The ordered tensor words in the ACTUAL outer edge operators form a
basis of the eight middle-root coefficient lines. Each is an integral
unit multiple of its distinct original root coefficient. In particular
no tensor vertex vanishes in characteristic two or three. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleSignedTensorBasis
open CFSGTrialityGeckDiagramCovariance CFSGTrialityD4MiddleCube
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityGeckMiddleCubeCoordinates
open CFSGTrialityGeckMiddleCubeEdgeOperators
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _
local instance : DecidableEq GeckIndex := inferInstance

abbrev zeroCube : Cube := 0

def cubePrefix (a : Cube) (n : ℕ) : Cube := fun j => if j.val < n then a j else 0

private theorem cubePrefix_zero (a : Cube) : cubePrefix a 0 = zeroCube := by
  funext j
  simp [cubePrefix]

private theorem cubePrefix_three (a : Cube) : cubePrefix a 3 = a := by
  funext j
  exact if_pos j.isLt

private theorem cubePrefix_succ : ∀ (a : Cube) (j : Fin 3),
    cubePrefix a (j.val+1) = Function.update (cubePrefix a j.val) j (a j) := by
  decide

def edgePowerSign (a : Cube) (j : Fin 3) (b : Fin 2) : ℤ :=
  if b = 0 then 1 else edgeSign a j

private theorem edgePowerSign_unit (a : Cube) (j : Fin 3) (b : Fin 2) (hbit : a j = 0) :
    edgePowerSign a j b = 1 ∨ edgePowerSign a j b = -1 := by
  by_cases hb : b = 0
  · exact Or.inl (if_pos hb)
  · simpa only [edgePowerSign, if_neg hb] using edgeSign_unit a j hbit

private theorem edgePower_cube (K : Type) [Field K] (a : Cube) (j : Fin 3)
    (b : Fin 2) (hbit : a j = 0) :
    (edgeShift K j ^ b.val) (cubeCoefficient K a) =
      (edgePowerSign a j b : K) • cubeCoefficient K (Function.update a j b) := by
  fin_cases b
  · simp only [pow_zero, Module.End.one_apply]
    change cubeCoefficient K a =
      (edgePowerSign a j (0 : Fin 2) : K) •
        cubeCoefficient K (Function.update a j (0 : Fin 2))
    rw [edgePowerSign, if_pos rfl, Int.cast_one,
      Function.update_eq_self_iff.mpr hbit.symm, one_smul]
  · change edgeShift K j (cubeCoefficient K a) =
      (edgeSign a j : K) • cubeCoefficient K (Function.update a j 1)
    exact edgeShift_cube K a j

def tensorStage (K : Type) [Field K] (a : Cube) : ℕ → Mat K
  | 0 => cubeCoefficient K zeroCube
  | n+1 => if h : n < 3 then
      (edgeShift K ⟨n,h⟩ ^ (a ⟨n,h⟩).val) (tensorStage K a n) else tensorStage K a n

private theorem mul_sign {a b : ℤ} (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1) :
    a*b=1 ∨ a*b= -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

theorem tensorStage_unit_sign (a : Cube) (n : ℕ) : n ≤ 3 →
    ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧ ∀ (K : Type) [Field K],
      tensorStage K a n = (ε:K) • cubeCoefficient K (cubePrefix a n) := by
  induction n with
  | zero =>
    intro hn
    refine ⟨1, Or.inl rfl, ?_⟩
    intro K _
    simp only [tensorStage, Int.cast_one, cubePrefix_zero, one_smul]
  | succ n ih =>
    intro hn
    have hn3 : n < 3 := by omega
    obtain ⟨ε, hε, hvalue⟩ := ih (by omega)
    let j : Fin 3 := ⟨n, hn3⟩
    have hbit : cubePrefix a n j = 0 := by simp [cubePrefix, j]
    let η := edgePowerSign (cubePrefix a n) j (a j)
    have hη : η=1 ∨ η= -1 := edgePowerSign_unit (cubePrefix a n) j (a j) hbit
    have hprefix : cubePrefix a (n+1) = Function.update (cubePrefix a n) j (a j) :=
      cubePrefix_succ a j
    refine ⟨ε*η, mul_sign hε hη, ?_⟩
    intro K _
    rw [tensorStage, dif_pos hn3]
    change (edgeShift K j ^ (a j).val) (tensorStage K a n) = _
    calc
      _ = (ε:K) • (edgeShift K j ^ (a j).val) (cubeCoefficient K (cubePrefix a n)) := by
        rw [hvalue K, map_smul]
      _ = (ε:K) • (η:K) • cubeCoefficient K (Function.update (cubePrefix a n) j (a j)) :=
        congrArg (fun M : Mat K => (ε:K) • M) (edgePower_cube K (cubePrefix a n) j (a j) hbit)
      _ = ((ε*η:ℤ):K) • cubeCoefficient K (cubePrefix a (n+1)) := by
        rw [smul_smul, Int.cast_mul, hprefix]

def tensorBasis (K : Type) [Field K] (a : Cube) : Mat K := tensorStage K a 3

theorem tensorBasis_unit_sign (a : Cube) :
    ∃ ε : ℤ, (ε=1 ∨ ε= -1) ∧ ∀ (K : Type) [Field K],
      tensorBasis K a = (ε:K) • cubeCoefficient K a := by
  obtain ⟨ε, hε, he⟩ := tensorStage_unit_sign a 3 (by omega)
  exact ⟨ε, hε, fun K _ => by simpa only [tensorBasis, cubePrefix_three] using he K⟩

theorem tensor_coefficients_unique (K : Type) [Field K] (c d : Cube → K)
    (h : (∑ a, c a • tensorBasis K a) = ∑ a, d a • tensorBasis K a) : c = d := by
  let ε : Cube → ℤ := fun a => Classical.choose (tensorBasis_unit_sign a)
  have hvalue : ∀ a, tensorBasis K a = (ε a : K) • cubeCoefficient K a :=
    fun a => (Classical.choose_spec (tensorBasis_unit_sign a)).2 K
  simp_rw [hvalue, smul_smul] at h
  have hcoeff := cube_coefficients_unique K (fun a => c a * (ε a : K))
    (fun a => d a * (ε a : K)) h
  funext a
  have hunit := (Classical.choose_spec (tensorBasis_unit_sign a)).1
  have hsquare : (ε a : K) * (ε a : K) = 1 := by
    rcases hunit with he | he <;> rw [show ε a = _ from he] <;> norm_num
  have he := congrArg (fun x : K => x * (ε a : K)) (congrFun hcoeff a)
  simpa only [mul_assoc, hsquare, mul_one] using he

theorem tensorBasis_linearIndependent (K : Type) [Field K] :
    LinearIndependent K (tensorBasis K) := by
  apply linearIndependent_iff_injective_fintypeLinearCombination.mpr
  intro c d h
  exact tensor_coefficients_unique K c d h

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckMiddleSignedTensorBasis
