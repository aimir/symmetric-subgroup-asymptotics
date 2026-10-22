import SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! Literal Gaussian elimination of a signed-isotropic vector by one
norm-constrained upper array. This is an all-characteristic computation,
not a transitivity or Bruhat hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices
variable {K : Type} [Field K] (σ : K ≃+* K)

def SignedIsotropic (v : Fin 3 → K) : Prop :=
  σ (v 0) * v 2 - σ (v 1) * v 1 + σ (v 2) * v 0 = 0

theorem normalized_clear_parameters (hσ : Function.Involutive σ) (x y : K)
    (hxy : x + σ x = y * σ y) : NormCondition σ (-σ y) (σ x) := by
  change σ x + σ (σ x) = (-σ y) * σ (-σ y)
  rw [map_neg, hσ x, hσ y]
  linear_combination hxy

theorem normalized_clear_vector (hσ : Function.Involutive σ) (x y : K)
    (hxy : x + σ x = y * σ y) :
    (upperArray σ (-σ y) (σ x)).mulVec ![x, y, 1] = ![0, 0, 1] := by
  funext i
  fin_cases i <;>
    simp [upperArray, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_neg, hσ y] <;>
    linear_combination hxy

theorem exists_upper_clear_vector (hσ : Function.Involutive σ) (v : Fin 3 → K)
    (hv : SignedIsotropic σ v) (hv2 : v 2 ≠ 0) :
    ∃ a b, NormCondition σ a b ∧
      (upperArray σ a b).mulVec v = v 2 • (![0, 0, 1] : Fin 3 → K) := by
  let x := v 0 / v 2
  let y := v 1 / v 2
  have hσv2 : σ (v 2) ≠ 0 := (map_ne_zero σ).mpr hv2
  have hxy : x + σ x = y * σ y := by
    change v 0 / v 2 + σ (v 0 / v 2) = (v 1 / v 2) * σ (v 1 / v 2)
    simp only [map_div₀]
    field_simp [hv2, hσv2]
    change σ (v 0) * v 2 - σ (v 1) * v 1 + σ (v 2) * v 0 = 0 at hv
    linear_combination hv
  have hvnorm : v = v 2 • (![x, y, 1] : Fin 3 → K) := by
    funext i
    fin_cases i <;>
      simp [x, y, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two,
        Matrix.vecHead, Matrix.vecTail] <;> field_simp [hv2]
  refine ⟨-σ y, σ x, normalized_clear_parameters σ hσ x y hxy, ?_⟩
  calc
    _ = (upperArray σ (-σ y) (σ x)).mulVec (v 2 • (![x, y, 1] : Fin 3 → K)) :=
      congrArg (fun w : Fin 3 → K => (upperArray σ (-σ y) (σ x)).mulVec w) hvnorm
    _ = _ := by rw [Matrix.mulVec_smul, normalized_clear_vector σ hσ x y hxy]

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
