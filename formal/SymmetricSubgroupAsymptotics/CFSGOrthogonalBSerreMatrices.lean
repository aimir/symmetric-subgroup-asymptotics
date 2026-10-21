import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Literal natural matrices for the pinned B_r-transpose convention.
The terminal short-root matrices have cube zero, with a nonzero integral
quadratic exponential coefficient. No square-zero assertion is made. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

abbrev Index := (Fin r ⊕ Fin r) ⊕ Unit
abbrev Mat := Matrix (Index r) (Index r) R
abbrev pos (i : Fin r) : Index r := Sum.inl (Sum.inl i)
abbrev neg (i : Fin r) : Index r := Sum.inl (Sum.inr i)
abbrev middle : Index r := Sum.inr ()

def positive (i : Fin r) : Mat R r :=
  if h : i.val + 1 < r then
    Matrix.single (pos r i) (pos r (⟨i.val+1,h⟩ : Fin r)) 1 -
      Matrix.single (neg r (⟨i.val+1,h⟩ : Fin r)) (neg r i) 1
  else Matrix.single (pos r i) (middle r) 1 - Matrix.single (middle r) (neg r i) 2

def negative (i : Fin r) : Mat R r :=
  if h : i.val + 1 < r then
    Matrix.single (pos r (⟨i.val+1,h⟩ : Fin r)) (pos r i) 1 -
      Matrix.single (neg r i) (neg r (⟨i.val+1,h⟩ : Fin r)) 1
  else Matrix.single (middle r) (pos r i) 2 - Matrix.single (neg r i) (middle r) 1

def positiveSecond (i : Fin r) : Mat R r :=
  if i.val + 1 < r then 0 else Matrix.single (pos r i) (neg r i) (-1)

def negativeSecond (i : Fin r) : Mat R r :=
  if i.val + 1 < r then 0 else Matrix.single (neg r i) (pos r i) (-1)

def cartan (i : Fin r) : Mat R r := ⁅positive R r i,negative R r i⁆

private theorem next_ne (i : Fin r) (h : i.val + 1 < r) :
    (⟨i.val+1,h⟩ : Fin r) ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  change i.val+1=i.val at hv
  omega

theorem positive_square (i : Fin r) :
    positive R r i * positive R r i = positiveSecond R r i + positiveSecond R r i := by
  by_cases h : i.val + 1 < r
  · simp [positive,positiveSecond,h,sub_mul,mul_sub,next_ne r i h,(next_ne r i h).symm]
  · simp only [positive,positiveSecond,dif_neg h,if_neg h,sub_mul,mul_sub]
    simp [pos,neg,middle] <;>
      (ext a b; simp [Matrix.single]; split_ifs <;> ring)

theorem negative_square (i : Fin r) :
    negative R r i * negative R r i = negativeSecond R r i + negativeSecond R r i := by
  by_cases h : i.val + 1 < r
  · simp [negative,negativeSecond,h,sub_mul,mul_sub,next_ne r i h,(next_ne r i h).symm]
  · simp only [negative,negativeSecond,dif_neg h,if_neg h,sub_mul,mul_sub]
    simp [pos,neg,middle] <;>
      (ext a b; simp [Matrix.single]; split_ifs <;> ring)

theorem positive_mul_second (i : Fin r) : positive R r i * positiveSecond R r i = 0 := by
  by_cases h : i.val + 1 < r <;> simp [positive,positiveSecond,h,sub_mul]

theorem second_mul_positive (i : Fin r) : positiveSecond R r i * positive R r i = 0 := by
  by_cases h : i.val + 1 < r <;> simp [positive,positiveSecond,h,mul_sub]

theorem negative_mul_second (i : Fin r) : negative R r i * negativeSecond R r i = 0 := by
  by_cases h : i.val + 1 < r <;> simp [negative,negativeSecond,h,sub_mul]

theorem second_mul_negative (i : Fin r) : negativeSecond R r i * negative R r i = 0 := by
  by_cases h : i.val + 1 < r <;> simp [negative,negativeSecond,h,mul_sub]

theorem positiveSecond_sq_zero (i : Fin r) : positiveSecond R r i * positiveSecond R r i = 0 := by
  by_cases h : i.val + 1 < r <;> simp [positiveSecond,h]

theorem negativeSecond_sq_zero (i : Fin r) : negativeSecond R r i * negativeSecond R r i = 0 := by
  by_cases h : i.val + 1 < r <;> simp [negativeSecond,h]

theorem positive_cube (i : Fin r) : positive R r i ^ 3 = 0 := by
  rw [pow_succ,pow_two,positive_square,add_mul,second_mul_positive,zero_add]

theorem negative_cube (i : Fin r) : negative R r i ^ 3 = 0 := by
  rw [pow_succ,pow_two,negative_square,add_mul,second_mul_negative,zero_add]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
