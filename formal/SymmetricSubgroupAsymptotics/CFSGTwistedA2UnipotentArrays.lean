import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Literal three-dimensional unitary-unipotent array algebra. These are
symbolic field identities, not a group census or a unitary recognition
assumption. The trace/norm condition is preserved by the actual law. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
open CFSGTwistedANaturalMatrices
variable {K : Type} [Field K] (σ : K ≃+* K)

def upperArray (a b : K) : Mat K 2 := !![1, a, b; 0, 1, σ a; 0, 0, 1]

theorem upperArray_zero : upperArray σ 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upperArray, Matrix.one_apply]

theorem upperArray_mul (a b c d : K) :
    upperArray σ a b * upperArray σ c d =
      upperArray σ (a + c) (b + d + a * σ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperArray, Matrix.mul_apply, Fin.sum_univ_three, map_add] <;> ring

theorem upperArray_inverse_right (a b : K) :
    upperArray σ a b * upperArray σ (-a) (-b + a * σ a) = 1 := by
  rw [upperArray_mul, add_neg_cancel]
  have h : b + (-b + a * σ a) + a * σ (-a) = 0 := by
    rw [map_neg]
    ring
  rw [h, upperArray_zero]

theorem upperArray_inverse_left (a b : K) :
    upperArray σ (-a) (-b + a * σ a) * upperArray σ a b = 1 := by
  rw [upperArray_mul]
  have h : -b + a * σ a + b + -a * σ a = 0 := by ring
  rw [neg_add_cancel, h, upperArray_zero]

def upperUnit (a b : K) : (Mat K 2)ˣ where
  val := upperArray σ a b
  inv := upperArray σ (-a) (-b + a * σ a)
  val_inv := upperArray_inverse_right σ a b
  inv_val := upperArray_inverse_left σ a b

def NormCondition (a b : K) : Prop := b + σ b = a * σ a

theorem normCondition_zero : NormCondition σ 0 0 := by simp [NormCondition]

theorem normCondition_mul (hσ : Function.Involutive σ) (a b c d : K)
    (hab : NormCondition σ a b) (hcd : NormCondition σ c d) :
    NormCondition σ (a + c) (b + d + a * σ c) := by
  change b + σ b = a * σ a at hab
  change d + σ d = c * σ c at hcd
  change b + d + a * σ c + σ (b + d + a * σ c) = (a + c) * σ (a + c)
  rw [map_add, map_add, map_mul, hσ, map_add]
  calc
    _ = (b + σ b) + (d + σ d) + a * σ c + σ a * c := by ring
    _ = _ := by rw [hab, hcd]; ring

theorem normCondition_inverse (hσ : Function.Involutive σ) (a b : K)
    (hab : NormCondition σ a b) : NormCondition σ (-a) (-b + a * σ a) := by
  change b + σ b = a * σ a at hab
  change -b + a * σ a + σ (-b + a * σ a) = (-a) * σ (-a)
  rw [map_add, map_neg, map_mul, hσ, map_neg]
  linear_combination -hab

end SymmetricSubgroupAsymptotics.CFSGTwistedA2UnipotentArrays
