import SymmetricSubgroupAsymptotics.TerminalAttachmentBound
import SymmetricSubgroupAsymptotics.BinaryMarkedGoursatPeel

/-! Attach one original terminal family to each complete actual carrier.
The existing attachment theorem supplies the inequality. Exact finite-sum
algebra exposes the two correlated marks on that same carrier, before any
word estimate is applied. No binary or vanishing-inflation premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.BinaryMarkedTerminalAttachment

open BinaryMarkedGoursatPeel

/-- The part of one original terminal summand independent of the carrier.
Both original Euler factors, the Gaussian coefficient and 72^ell remain. -/
def coefficient (r c j ell : ℕ) : ℝ :=
  (eulerProduct⁻¹)^2 * (binaryGaussianCoefficient c ell : ℝ) * (72 : ℝ)^ell *
    (2 : ℝ)^(((j : ℝ)-ell)*((r : ℝ)-j))

theorem coefficient_nonneg (r c j ell : ℕ) (hell : ell ≤ c) :
    0 ≤ coefficient r c j ell := by
  have hg : 0 ≤ (binaryGaussianCoefficient c ell : ℝ) := by
    exact_mod_cast (binaryGaussianCoefficient_pos hell).le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (sq_nonneg _) hg) (pow_nonneg (by norm_num) _))
    (Real.rpow_nonneg (by norm_num) _)

/-- Exact factorization, including j < ell. Subtraction is real throughout;
the actual d and actual H² defect always belong to this same H. -/
theorem doubleSum_eq_markSum (r c : ℕ) (H : Type) [Group H] [Finite H] :
    terminalGaussianDoubleSum r c (binaryCharacterRank H)
      (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H)) =
      ∑ j ∈ Finset.range (r+1), ∑ ell ∈ Finset.range (c+1),
        coefficient r c j ell * mark H ((j : ℝ)-ell) 0 ell := by
  unfold terminalGaussianDoubleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ell _
  unfold coefficient mark exponent
  simp only [zero_mul, add_zero]
  have he :
      (Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) : ℝ)*ell +
        ((j : ℝ)-ell)*((r : ℝ)-j+binaryCharacterRank H) =
      ((j : ℝ)-ell)*((r : ℝ)-j) +
        (((j : ℝ)-ell)*(binaryCharacterRank H : ℝ) +
          (ell : ℝ)*(Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) : ℝ)) := by
    ring
  rw [he, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

variable {ι : Type} [Fintype ι] (a : ℕ) (s : ι → Bool)

/-- The original complete-exterior terminal theorem, with its actual
carrier dependence exposed as the marks needed by a later word estimate. -/
theorem actualSubgroups_card_le_markSum (H : Type) [Group H] [Finite H] :
    (Nat.card (TerminalActualSubgroups a s H) : ℝ) ≤
      ∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            mark H ((j : ℝ)-ell) 0 ell :=
  (terminalActualSubgroups_card_le_doubleSum a s H).trans_eq
    (doubleSum_eq_markSum _ _ H)

/-- An arbitrary further condition still tests the original terminal
subgroup. Dropping that condition is precisely the checked subfamily bound. -/
theorem actualSubfamily_card_le_markSum (H : Type) [Group H] [Finite H]
    (P : Subgroup (CriticalProductGroup a s × H) → Prop) :
    (Nat.card {K : TerminalActualSubgroups a s H // P K.1} : ℝ) ≤
      ∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            mark H ((j : ℝ)-ell) 0 ell :=
  (terminalActualSubfamily_card_le_doubleSum a s H P).trans_eq
    (doubleSum_eq_markSum _ _ H)

/-- A single attachment to each complete carrier, followed by one exact
interchange of the finite sums. Each original nonnegative carrier weight
stays inside the marked family sum. The carrier types can be arbitrary
finite groups, in particular literal subgroups of an actual word product. -/
theorem weighted_subfamilies_le_markSums
    {J : Type} [Fintype J] (H : J → Type)
    [∀ h, Group (H h)] [∀ h, Finite (H h)]
    (P : ∀ h, Subgroup (CriticalProductGroup a s × H h) → Prop)
    (w : J → ℝ) (hw : ∀ h, 0 ≤ w h) :
    (∑ h, w h * (Nat.card {K : TerminalActualSubgroups a s (H h) // P h K.1} : ℝ)) ≤
      ∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            ∑ h, w h * mark (H h) ((j : ℝ)-ell) 0 ell := by
  calc
    _ ≤ ∑ h, w h *
        (∑ j ∈ Finset.range (criticalProductRank a s+1),
          ∑ ell ∈ Finset.range (Fintype.card ι+1),
            coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
              mark (H h) ((j : ℝ)-ell) 0 ell) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
        (actualSubfamily_card_le_markSum a s (H h) (P h)) (hw h)
    _ = ∑ h, ∑ j ∈ Finset.range (criticalProductRank a s+1),
        ∑ ell ∈ Finset.range (Fintype.card ι+1),
          coefficient (criticalProductRank a s) (Fintype.card ι) j ell *
            (w h * mark (H h) ((j : ℝ)-ell) 0 ell) := by
      apply Finset.sum_congr rfl
      intro h _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ell _
      rw [Finset.mul_sum]

/-- The original mark indices lie in the full terminal rectangle. This
does not impose ell ≤ j; all such terms have already been retained above. -/
theorem index_rectangle {j ell : ℕ}
    (hj : j ∈ Finset.range (criticalProductRank a s+1))
    (hell : ell ∈ Finset.range (Fintype.card ι+1)) :
    (0 ≤ (j : ℝ) ∧ (j : ℝ) ≤ criticalProductRank a s) ∧
      (0 ≤ (ell : ℝ) ∧ (ell : ℝ) ≤ (criticalProductRank a s : ℝ)/2) := by
  have hj' : j ≤ criticalProductRank a s := by simpa using hj
  have hell' : ell ≤ Fintype.card ι := by simpa using hell
  have htwo : 2*ell ≤ criticalProductRank a s :=
    (Nat.mul_le_mul_left 2 hell').trans (terminalCritical_two_card_le_rank a s)
  have htwoR : (2 : ℝ)*ell ≤ criticalProductRank a s := by exact_mod_cast htwo
  exact ⟨⟨Nat.cast_nonneg _, Nat.cast_le.mpr hj'⟩, ⟨Nat.cast_nonneg _, by linarith⟩⟩

end SymmetricSubgroupAsymptotics.BinaryMarkedTerminalAttachment
