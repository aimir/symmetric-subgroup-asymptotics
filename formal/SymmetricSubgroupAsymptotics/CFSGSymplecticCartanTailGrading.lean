import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalPositiveWeightIdentification

/-! The literal grading matrix is a positive combination of actual
Cartan tails. This is an identity in the natural representation, not
a source-faithfulness assertion. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticCartanTailGrading
open CFSG.Models.Chevalley CFSGSerreDiagram CFSGSymplecticSerreMatrices
open CFSGSymplecticOriginalRootCandidates CFSGSymplecticOriginalCartanTail
open CFSGSymplecticUniformRootCoordinates CFSGSymplecticUniformRootGrading
open CFSGSymplecticUniformPositiveTables CFSGSymplecticUniformPositiveProfile
variable (r : ℕ)

def cartanAt (a : ℕ) : Mat ℚ r :=
  if h : a < r then cartan ℚ r ⟨a,h⟩ else 0

theorem Hnat_rational_image (a : ℕ) :
    rationalSymplecticRepresentation r (Hnat r a).val=cartanAt r a := by
  unfold Hnat cartanAt
  split_ifs with h
  · exact rationalSymplecticRepresentation_H r ⟨a,h⟩
  · simp

theorem diagonal_tail (i : Fin r) :
    matrix ℚ r (.inl i)=∑ a ∈ Finset.range (r-i.val),cartanAt r (i.val+a) := by
  have h:=CFSGSymplecticOriginalPositiveWeightIdentification.source_image r (.inl i)
  change rationalSymplecticRepresentation r (tail r i.val).val=matrix ℚ r (.inl i) at h
  simp only [tail,Submodule.coe_sum,map_sum,Hnat_rational_image] at h
  exact h.symm

def coefficient (i : Fin r) : ℚ := (r:ℚ)-i.val-1/2

theorem coefficient_pos (i : Fin r) : 0 < coefficient r i := by
  have hi : (i.val:ℚ)+1 ≤ (r:ℚ) := by exact_mod_cast (Nat.succ_le_of_lt i.isLt)
  unfold coefficient
  linarith

private theorem sum_selected (f : Fin r→ℚ) (x y : Fin r) :
    (∑ i : Fin r,if x=i ∧ y=i then f i else 0)=if x=y then f x else 0 := by
  classical
  by_cases h : x=y
  · subst y
    simp [eq_comm]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hx : x=i
    · subst i
      simp [Ne.symm h]
    · simp [hx]

theorem grading_diagonal_sum :
    gradingMatrix r=∑ i : Fin r,coefficient r i • matrix ℚ r (.inl i) := by
  classical
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [gradingMatrix,Matrix.diagonal_apply,diagonalWeight,coefficient,
      matrix,Matrix.sum_apply,Matrix.smul_apply,Matrix.sub_apply,Matrix.single_apply,mul_ite,Finset.sum_neg_distrib,sum_selected,eq_comm]
  all_goals (try split_ifs) <;> (try simp_all only [sum_selected]) <;> ring

theorem grading_tail_sum :
    gradingMatrix r=∑ i : Fin r,coefficient r i •
      ∑ a ∈ Finset.range (r-i.val),cartanAt r (i.val+a) := by
  rw [grading_diagonal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [diagonal_tail]

end SymmetricSubgroupAsymptotics.CFSGSymplecticCartanTailGrading
