import SymmetricSubgroupAsymptotics.FiniteLabelAllocations
import SymmetricSubgroupAsymptotics.TernaryFullWeightReindex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact allocation weights for repeated original markers

The label type Q is an already selected type of distinct pair characters.
Original marker positions remain labelled until their complete allocation
sum is divided by the original factor 6^g g!. The allocation multiplicity
cancels g!, and replacing the selected pair weights contributes 2^card Q.
There is no extra factorial of the number of selected labels.

These are arithmetic identities derived from the complete allocation
family. They neither assert a physical subgroup classification nor insert
a supplied counting estimate. Exterior normalizers are left untouched.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerAllocationWeights

open FiniteLabelAllocations TernaryFullWeightReindex
open DiagonalFullSubmoduleWeights

variable {Q : Type*} [Fintype Q] (g : ℕ)

private theorem factorial_cast_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- Cast the exact integer allocation count without replacing integer
division by field division until its divisibility has been proved. -/
theorem allocation_count_rat (a : Q → ℕ) (ha : ∑ q, a q=g) :
    (Nat.card (Allocation g a) : ℚ)=
      (g.factorial : ℚ)/(∏ q, ((a q).factorial : ℚ)) := by
  have hp : (∏ q, ((a q).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q _ => factorial_cast_ne_zero (a q))
  apply (eq_div_iff hp).mpr
  exact_mod_cast allocation_card_mul_factorials g a ha

/-- The full sum over labelled surjections to the selected label type. -/
def allocationSum (w : Q → ℕ → ℚ) : ℚ :=
  ∑ f : Surjection (Q := Q) g,
    ∏ q, w q (Fintype.card {x : Fin g // f.val x=q})

/-- Positive multiplicity profiles of the selected labels, retaining each
label's own factor. An ordering of Q is not part of this definition. -/
def profileSum (w : Q → ℕ → ℚ) : ℚ :=
  ∑ a : PositiveProfile (Q := Q) g,
    ∏ q, w q (a.val q).val / (((a.val q).val).factorial : ℚ)

theorem allocation_sum_eq_factorial_mul (w : Q → ℕ → ℚ) :
    allocationSum g w=(g.factorial : ℚ)*profileSum g w := by
  unfold allocationSum profileSum
  rw [weighted_surjection_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [nsmul_eq_mul,← allocation_card g (fun q => (a.val q).val) a.property.2,
    allocation_count_rat g _ a.property.2,Finset.prod_div_distrib]
  ring

/-- The fixed-multiplicity contribution with the actual original marker
denominator and the selected binary pair-weight correction. -/
theorem fixed_profile_weight (a : Q → ℕ) (ha : ∑ q, a q=g)
    (w : Q → ℕ → ℚ) (f : ℕ) :
    ((2 : ℚ)^Fintype.card Q/((6 : ℚ)^g*g.factorial*f.factorial)) *
        (Nat.card (Allocation g a) : ℚ) * (∏ q, w q (a q)) =
      ((2 : ℚ)^Fintype.card Q/((6 : ℚ)^g*f.factorial)) *
        (∏ q, w q (a q)/((a q).factorial : ℚ)) := by
  rw [allocation_count_rat g a ha,Finset.prod_div_distrib]
  have hp : (∏ q, ((a q).factorial : ℚ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun q _ => factorial_cast_ne_zero (a q))
  have h6 : (6 : ℚ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [factorial_cast_ne_zero,hp,h6] <;> ring

/-- The same cancellation after summing every labelled allocation. -/
theorem total_profile_weight (w : Q → ℕ → ℚ) (f : ℕ) :
    ((2 : ℚ)^Fintype.card Q/((6 : ℚ)^g*g.factorial*f.factorial)) *
        allocationSum g w =
      ((2 : ℚ)^Fintype.card Q/((6 : ℚ)^g*f.factorial)) * profileSum g w := by
  rw [allocation_sum_eq_factorial_mul]
  have h6 : (6 : ℚ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [factorial_cast_ne_zero,h6] <;> ring

/-- The manuscript's multiplicity sum on the actual selected label type. -/
def markerProfileSum : ℚ :=
  profileSum (Q := Q) g (fun _ a => (ternaryFullFactor a : ℚ))

/-- Actual coordinate fibres may be used directly; their full-coordinate
ternary factors are replaced by cardinality factors via explicit reindexing. -/
theorem literal_fibre_sum_eq :
    (∑ f : Surjection (Q := Q) g,
      ∏ q, (ternaryFullWeight {x : Fin g // f.val x=q} : ℚ))=
      (g.factorial : ℚ)*markerProfileSum (Q := Q) g := by
  calc
    _ = allocationSum (Q := Q) g (fun _ a => (ternaryFullFactor a : ℚ)) := by
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.prod_congr rfl
      intro q _
      rw [weight_eq_factor]
    _ = _ := allocation_sum_eq_factorial_mul g _

theorem original_marker_weight (f : ℕ) :
    ((2 : ℚ)^Fintype.card Q/((6 : ℚ)^g*g.factorial*f.factorial)) *
        (∑ s : Surjection (Q := Q) g,
          ∏ q, (ternaryFullWeight {x : Fin g // s.val x=q} : ℚ)) =
      ((2 : ℚ)^Fintype.card Q/((6 : ℚ)^g*f.factorial)) *
        markerProfileSum (Q := Q) g := by
  rw [literal_fibre_sum_eq]
  have h6 : (6 : ℚ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [factorial_cast_ne_zero,h6] <;> ring

/-- Pure support-weight factorization. The same arbitrary exterior
denominator E occurs on both sides. Physical reconstruction and the actual
relation between n and m are separate from this exact arithmetic identity. -/
theorem support_weight_factorization (w : Q → ℕ → ℚ) (n m f : ℕ) (E : ℚ) :
    (n.factorial : ℚ)*allocationSum g w /
        ((6 : ℚ)^g*g.factorial*f.factorial*E) =
      ((n.factorial : ℚ)/m.factorial) *
        ((2 : ℚ)^Fintype.card Q*profileSum g w/((6 : ℚ)^g*f.factorial)) *
        ((m.factorial : ℚ)/((2 : ℚ)^Fintype.card Q*E)) := by
  by_cases hE : E=0
  · simp [hE]
  rw [allocation_sum_eq_factorial_mul]
  have h6 : (6 : ℚ)^g ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (2 : ℚ)^Fintype.card Q ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [factorial_cast_ne_zero,h6,h2,hE] <;> ring

end SymmetricSubgroupAsymptotics.RepeatedMarkerAllocationWeights
