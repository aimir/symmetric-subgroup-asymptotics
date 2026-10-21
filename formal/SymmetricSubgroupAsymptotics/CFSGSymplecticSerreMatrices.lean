import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Linarith

/-! Literal symplectic simple-root matrices over any commutative ring.
The intended Cartan convention is the pinned C_r transpose (equivalently
the displayed B_r table). No Serre-quotient identification is asserted here. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

abbrev Index := Fin r ⊕ Fin r
abbrev Mat := Matrix (Index r) (Index r) R

def positive (i : Fin r) : Mat R r :=
  if h : i.val + 1 < r then
    Matrix.single (Sum.inl i) (Sum.inl (⟨i.val + 1, h⟩ : Fin r)) 1 -
      Matrix.single (Sum.inr (⟨i.val + 1, h⟩ : Fin r)) (Sum.inr i) 1
  else Matrix.single (Sum.inl i) (Sum.inr i) 1

def negative (i : Fin r) : Mat R r := (positive R r i).transpose

def cartan (i : Fin r) : Mat R r := ⁅positive R r i, negative R r i⁆

theorem positive_sq_zero (i : Fin r) : positive R r i ^ 2 = 0 := by
  unfold positive
  split_ifs with h
  · have hne : (⟨i.val + 1, h⟩ : Fin r) ≠ i := by
      intro he
      have hv := congrArg Fin.val he
      change i.val + 1 = i.val at hv
      omega
    simp [pow_two, sub_mul, mul_sub, hne, hne.symm]
  · simp [pow_two]

theorem negative_sq_zero (i : Fin r) : negative R r i ^ 2 = 0 := by
  rw [negative, pow_two, ← Matrix.transpose_mul, ← pow_two, positive_sq_zero]
  exact Matrix.transpose_zero

theorem positive_negative (i : Fin r) : ⁅positive R r i, negative R r i⁆ = cartan R r i := rfl

theorem cartan_transpose (i : Fin r) : (cartan R r i).transpose = cartan R r i := by
  simp only [cartan, Ring.lie_def, negative, Matrix.transpose_sub, Matrix.transpose_mul,
    Matrix.transpose_transpose]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
