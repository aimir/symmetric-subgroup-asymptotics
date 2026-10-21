import SymmetricSubgroupAsymptotics.CFSGSymplecticPositiveSupport
import Mathlib.Tactic.NoncommRing

/-! Actual matrix products controlling the remaining symplectic Serre
relations: nonadjacent roots have zero products, and the length-three
sandwich can be nonzero only at the double Cartan edge. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem positive_mul_of_not_adjacent (i j : Fin r)
    (hf : i.val + 1 ≠ j.val) (hr : j.val + 1 ≠ i.val) :
    positive R r i * positive R r j = 0 := by
  have hn : ∀ h : i.val + 1 < r, (⟨i.val + 1, h⟩ : Fin r) ≠ j := by
    intro h he
    have hv := congrArg Fin.val he
    exact hf hv
  have hnr : ∀ h : j.val + 1 < r, i ≠ (⟨j.val + 1, h⟩ : Fin r) := by
    intro h he
    have hv := congrArg Fin.val he
    exact hr hv.symm
  by_cases hi : i.val + 1 < r <;> by_cases hj : j.val + 1 < r <;>
    simp [positive, hi, hj, sub_mul, mul_sub, hn, hnr]

theorem positive_lie_of_cartan_zero (i j : Fin r) (hzero : CartanMatrix.B r i j = 0) :
    ⁅positive R r i, positive R r j⁆ = 0 := by
  have hf : i.val + 1 ≠ j.val := by
    intro hs
    have hne : i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      omega
    simp only [CartanMatrix.B, Matrix.of_apply, if_neg hne, if_pos hs] at hzero
    split_ifs at hzero <;> omega
  have hr : j.val + 1 ≠ i.val := by
    intro hs
    have hne : i ≠ j := by
      intro he
      have hv := congrArg Fin.val he
      omega
    have hforward : ¬i.val + 1 = j.val := by omega
    simp only [CartanMatrix.B, Matrix.of_apply, if_neg hne, if_neg hforward,
      if_pos hs] at hzero
    omega
  simp only [Ring.lie_def, positive_mul_of_not_adjacent R r i j hf hr,
    positive_mul_of_not_adjacent R r j i hr hf, sub_self]

theorem positive_sandwich_of_not_neg_two (i j : Fin r)
    (hij : CartanMatrix.B r i j ≠ -2) :
    positive R r i * positive R r j * positive R r i = 0 := by
  by_cases hi : i.val + 1 < r
  · let a : Fin r := ⟨i.val + 1, hi⟩
    let M : Mat R r := Matrix.single (Sum.inl i) (Sum.inl a) 1
    let N : Mat R r := Matrix.single (Sum.inr a) (Sum.inr i) 1
    have hei : positive R r i = M - N := by simp only [positive, dif_pos hi]; rfl
    have hl : positive R r j (Sum.inl a) (Sum.inl i) = 0 :=
      positive_left_below R r j a i (by change i.val ≤ i.val + 1; omega)
    have hr : positive R r j (Sum.inr i) (Sum.inr a) = 0 :=
      positive_right_above R r j i a (by change i.val ≤ i.val + 1; omega)
    have hc : positive R r j (Sum.inl a) (Sum.inr a) = 0 := by
      rw [positive_cross_diagonal]
      apply if_neg
      rintro ⟨hj, hja⟩
      apply not_neg_two_forbids_terminal_successor r i j hij
      have hv := congrArg Fin.val hja
      have hjLt := j.isLt
      change j.val = i.val + 1 at hv
      exact ⟨hv.symm, by omega⟩
    rw [hei]
    calc
      (M - N) * positive R r j * (M - N) =
          M * positive R r j * M - M * positive R r j * N -
            (N * positive R r j * M - N * positive R r j * N) := by noncomm_ring
      _ = 0 := by
        simp only [M, N, Matrix.single_mul_mul_single, one_mul, mul_one, hl, hr, hc,
          positive_lower_left, Matrix.single_zero, sub_self, sub_zero]
  · have hei : positive R r i = Matrix.single (Sum.inl i) (Sum.inr i) 1 := by
      simp only [positive, dif_neg hi]
    rw [hei, Matrix.single_mul_mul_single]
    simp only [positive_lower_left, mul_zero, zero_mul, Matrix.single_zero]

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
