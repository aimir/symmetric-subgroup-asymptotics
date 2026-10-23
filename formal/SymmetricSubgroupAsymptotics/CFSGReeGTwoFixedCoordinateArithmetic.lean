import SymmetricSubgroupAsymptotics.CFSGReeGTwoFieldParameters
import Mathlib.LinearAlgebra.Matrix.Notation

/-! Division-free arithmetic for the six-coordinate Ree fixed-point equations.

This file counts fixed tuples of the displayed signed polynomial map.  It does
not identify that map with an action on a root group: the original signed
collecting and coordinate bridge must supply that identification separately.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCoordinateArithmetic

variable {K : Type*} [CommRing K]

/-- The signed coordinate map after collecting the six positive root factors. -/
def twist (alpha : K ≃+* K) (x : Fin 6 → K) : Fin 6 → K :=
  ![alpha.symm (x 1), alpha (x 0),
    -(alpha.symm (x 1)) * alpha (x 0) - alpha.symm (x 4),
    -(alpha.symm (x 1)) ^ 2 * alpha (x 0) + alpha.symm (x 5),
    -(alpha.symm (x 1)) ^ 3 * alpha (x 0) - alpha (x 2),
    (alpha.symm (x 1)) ^ 3 * (alpha (x 0)) ^ 2 + alpha (x 3)]

/-- The first, third and fourth coordinates are free. -/
def normalForm (alpha : K ≃+* K) (a c d : K) : Fin 6 → K :=
  ![a, alpha a, c, d, -a ^ 3 * alpha a - alpha c,
    a ^ 3 * (alpha a) ^ 2 + alpha d]

private theorem inverse_cube (alpha : K ≃+* K)
    (h : ∀ a : K, alpha (alpha a) = a ^ 3) (a : K) :
    alpha.symm (a ^ 3) = alpha a := by
  rw [← h a, alpha.symm_apply_apply]

theorem twist_normalForm (alpha : K ≃+* K)
    (h : ∀ a : K, alpha (alpha a) = a ^ 3) (a c d : K) :
    twist alpha (normalForm alpha a c d) = normalForm alpha a c d := by
  ext i
  fin_cases i <;>
    simp [twist, normalForm, inverse_cube alpha h, map_sub, map_pow] <;> ring

theorem fixed_iff_normalForm (alpha : K ≃+* K)
    (h : ∀ a : K, alpha (alpha a) = a ^ 3) (x : Fin 6 → K) :
    twist alpha x = x ↔ x = normalForm alpha (x 0) (x 2) (x 3) := by
  constructor
  · intro hx
    have h1 : alpha (x 0) = x 1 := congrFun hx 1
    have h4 : -(x 0) ^ 3 * alpha (x 0) - alpha (x 2) = x 4 := by
      have he := congrFun hx 4
      change -(alpha.symm (x 1)) ^ 3 * alpha (x 0) - alpha (x 2) = x 4 at he
      simpa only [← h1, alpha.symm_apply_apply] using he
    have h5 : (x 0) ^ 3 * (alpha (x 0)) ^ 2 + alpha (x 3) = x 5 := by
      have he := congrFun hx 5
      change (alpha.symm (x 1)) ^ 3 * (alpha (x 0)) ^ 2 + alpha (x 3) = x 5 at he
      simpa only [← h1, alpha.symm_apply_apply] using he
    ext i
    fin_cases i
    · rfl
    · exact h1.symm
    · rfl
    · rfl
    · exact h4.symm
    · exact h5.symm
  · intro hx
    conv_lhs => rw [hx]
    rw [twist_normalForm alpha h, ← hx]

/-- An explicit three-parameter chart for the fixed tuples; no division by
two or by three, and no trace-surjectivity assertion, occurs in this chart. -/
def fixedEquiv (alpha : K ≃+* K)
    (h : ∀ a : K, alpha (alpha a) = a ^ 3) :
    (Fin 3 → K) ≃ {x : Fin 6 → K // twist alpha x = x} where
  toFun y := ⟨normalForm alpha (y 0) (y 1) (y 2),
    twist_normalForm alpha h (y 0) (y 1) (y 2)⟩
  invFun x := ![x.val 0, x.val 2, x.val 3]
  left_inv y := by
    ext i
    fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    exact ((fixed_iff_normalForm alpha h x.val).mp x.property).symm

theorem fixed_card [Finite K] (alpha : K ≃+* K)
    (h : ∀ a : K, alpha (alpha a) = a ^ 3) :
    Nat.card {x : Fin 6 → K // twist alpha x = x} = (Nat.card K) ^ 3 := by
  rw [← Nat.card_congr (fixedEquiv alpha h)]
  simp only [Nat.card_fun, Nat.card_fin]

theorem original_field_fixed_card (m : ℕ) :
    Nat.card {x : Fin 6 → CFSGReeGTwoFieldParameters.Field m //
      twist (CFSGReeGTwoFieldParameters.alphaEquiv m) x = x} =
      (3 ^ (2 * m + 1)) ^ 3 := by
  rw [fixed_card _ (CFSGReeGTwoFieldParameters.alpha_twice m),
    CFSGReeGTwoFieldParameters.field_card]

end SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedCoordinateArithmetic
