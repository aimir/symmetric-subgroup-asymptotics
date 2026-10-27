import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBCartanMatrices
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Actual rational Cartan tails in the original B Serre quotient.
Only the terminal coroot receives coefficient one half. Their literal
images are primitive D_i. This is expressly NOT an integral source
basis or a characteristic-two base-change argument. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRationalCartanTail
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
variable (r : ℕ)

def Hhalf (j : ℕ) : RationalLie (CartanMatrix.B r).transpose :=
  if h : j < r then
    (if j + 1 < r then (1 : ℚ) else 1 / 2) •
      generator (CartanMatrix.B r).transpose (.H ⟨j, h⟩) else 0

def diagonal (j : ℕ) : Mat ℚ r :=
  if h : j < r then Matrix.single (pos r ⟨j, h⟩) (pos r ⟨j, h⟩) 1 -
    Matrix.single (neg r ⟨j, h⟩) (neg r ⟨j, h⟩) 1 else 0

def tail (j : ℕ) : RationalLie (CartanMatrix.B r).transpose :=
  ∑ a ∈ Finset.range (r - j), Hhalf r (j + a)

private theorem telescoping {M : Type*} [AddCommGroup M] (f : ℕ → M) (k n : ℕ) :
    (∑ a ∈ Finset.range n, (f (k + a) - f (k + a + 1))) = f k - f (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [Nat.succ_eq_add_one, Nat.add_assoc]
    abel

theorem Hhalf_image (j : ℕ) :
    rationalOrthogonalRepresentation r (Hhalf r j) = diagonal r j - diagonal r (j + 1) := by
  by_cases hj : j < r
  · rw [Hhalf, dif_pos hj, map_smul, rationalOrthogonalRepresentation_H, cartan_eq]
    by_cases hn : j + 1 < r
    · simp only [Fin.val_mk, hn, if_pos, dif_pos, diagonal, hj, one_smul]
      abel
    · simp only [Fin.val_mk, hn, if_neg, dif_neg, diagonal, hj, dif_pos, sub_zero]
      ext a b
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      simp [Matrix.single_apply]
      split_ifs <;> ring
  · have hn : ¬ j + 1 < r := by omega
    simp only [Hhalf, dif_neg hj, map_zero, diagonal, dif_neg hn, sub_self]

theorem tail_image (j : ℕ) :
    rationalOrthogonalRepresentation r (tail r j) = diagonal r j := by
  unfold tail
  rw [map_sum]
  simp_rw [Hhalf_image]
  rw [telescoping]
  have he : diagonal r (j + (r - j)) = 0 := by
    apply dif_neg
    omega
  rw [he, sub_zero]

theorem tail_step (j : ℕ) (hj : j < r) :
    tail r j = Hhalf r j + tail r (j + 1) := by
  have hr : r - j = (r - (j + 1)) + 1 := by omega
  unfold tail
  rw [hr, Finset.sum_range_succ']
  simp only [Nat.add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  omega

theorem tail_eq_zero_of_le (j : ℕ) (hj : r ≤ j) : tail r j = 0 := by
  simp only [tail, Nat.sub_eq_zero_of_le hj, Finset.range_zero, Finset.sum_empty]

theorem nonterminal_generator_H (i : Fin r) (hi : i.val + 1 < r) :
    generator (CartanMatrix.B r).transpose (.H i) = tail r i.val - tail r (i.val + 1) := by
  have h := tail_step r i.val i.isLt
  simp only [Hhalf, dif_pos i.isLt, if_pos hi, one_smul] at h
  exact eq_sub_iff_add_eq.mpr h.symm

theorem terminal_generator_H (i : Fin r) (hi : ¬ i.val + 1 < r) :
    generator (CartanMatrix.B r).transpose (.H i) = (2 : ℚ) • tail r i.val := by
  have h := tail_step r i.val i.isLt
  rw [tail_eq_zero_of_le r (i.val + 1) (by omega)] at h
  simp only [Hhalf, dif_pos i.isLt, if_neg hi, add_zero] at h
  rw [h]
  simp only [smul_smul]
  norm_num

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalRationalCartanTail
