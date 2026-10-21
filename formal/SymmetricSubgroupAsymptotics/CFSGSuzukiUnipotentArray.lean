import SymmetricSubgroupAsymptotics.External.CFSG.Models.Suzuki
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! The actual Suzuki unipotent array, over an arbitrary characteristic-two
commutative ring with an endomorphism whose square is Frobenius. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open Matrix
variable {K : Type*} [CommRing K] [CharP K 2]

def twistedArray (t : K →+* K) (a b : K) : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0;
     a, 1, 0, 0;
     b, t a, 1, 0;
     a ^ 2 * t a + a * b + t b, a * t a + b, a, 1]

@[simp] theorem twistedArray_zero (t : K →+* K) : twistedArray t 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [twistedArray, Matrix.one_apply]

theorem twistedArray_mul (t : K →+* K) (ht : ∀ a, t (t a) = a ^ 2)
    (a b c d : K) :
    twistedArray t a b * twistedArray t c d =
      twistedArray t (a + c) (b + d + t a * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twistedArray, Matrix.mul_apply, Fin.sum_univ_succ, map_add, map_mul, map_pow, ht] <;>
    ring_nf <;> simp

@[simp] theorem twistedArray_square (t : K →+* K) (ht : ∀ a, t (t a) = a ^ 2)
    (a b : K) : twistedArray t a b * twistedArray t a b = twistedArray t 0 (t a * a) := by
  rw [twistedArray_mul t ht]
  congr 1 <;> simp

theorem twistedArray_four (t : K →+* K) (ht : ∀ a, t (t a) = a ^ 2)
    (a b : K) : twistedArray t a b ^ 4 = 1 := by
  calc
    twistedArray t a b ^ 4 =
        (twistedArray t a b * twistedArray t a b) *
          (twistedArray t a b * twistedArray t a b) := by
      change twistedArray t a b ^ (2 + 2) = _
      simp only [pow_add, pow_two]
    _ = twistedArray t 0 (t a * a) * twistedArray t 0 (t a * a) := by
      rw [twistedArray_square t ht]
    _ = twistedArray t 0 0 := by rw [twistedArray_square t ht]; simp
    _ = 1 := twistedArray_zero t

theorem twistedArray_mul_inverse (t : K →+* K) (ht : ∀ a, t (t a) = a ^ 2)
    (a b : K) :
    twistedArray t a b * twistedArray t a (b + t a * a) = 1 := by
  rw [twistedArray_mul t ht]
  have ha : a + a = 0 := CharTwo.add_self_eq_zero a
  have hb : b + (b + t a * a) + t a * a = 0 := by
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]
  rw [ha, hb, twistedArray_zero]

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
