import SymmetricSubgroupAsymptotics.MarkedC4NilpotentTargetConvolution

/-! Exact ordinary literature interface: Roney-Dougal--Tracey,
"The number of subgroups of the symmetric group", arXiv:2503.05416v1,
Theorem 1, page 1, upper half. The published exponent beta*n^(3/2)
is written beta*n*sqrt(n). Only n>=2 is assumed from the paper; degree
zero and one and enlargement of beta to a nonnegative constant are proved.
This input is an ordinary unmarked symmetric-group subgroup bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.OrdinarySubgroupUpper

/-- LIT-RDT-Theorem1-upper, all integers n>1, with one absolute beta. -/
def PublishedTheoremOneUpper : Prop :=
  ∃ β : ℝ,∀ n : ℕ,2≤n →
    (Nat.card (Subgroup (PermutationGroup n)) : ℝ)≤
      (2 : ℝ)^((n : ℝ)^2/16+β*n*Real.sqrt n)

/-- The exact all-degree ordinary input required by the physical odd
convolution. It is derived from Theorem 1, with no marked hypothesis. -/
theorem exists_nonnegative_coarse (h : PublishedTheoremOneUpper) :
    ∃ β : ℝ,0≤β ∧ ∀ n : ℕ,NilpotentTargetConvolution.oddCount n≤
      (2 : ℝ)^((n : ℝ)^2/16+PhysicalOddConvolution.coarseError β n) := by
  obtain ⟨β,hβ⟩ := h
  refine ⟨max β 0,le_max_right _ _,?_⟩
  intro n
  by_cases hn : 2≤n
  · apply (hβ n hn).trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
    unfold PhysicalOddConvolution.coarseError
    have hh := mul_le_mul_of_nonneg_right (le_max_left β 0)
      (mul_nonneg (Nat.cast_nonneg n) (Real.sqrt_nonneg (n : ℝ)))
    nlinarith
  · have hn1 : n≤1 := by omega
    letI : Subsingleton (Fin n) := ⟨by intro i j; apply Fin.ext; omega⟩
    have hs : Nat.card (Subgroup (PermutationGroup n))≤1 :=
      Finite.card_le_one_iff_subsingleton.mpr inferInstance
    have hsR : NilpotentTargetConvolution.oddCount n≤1 := by
      unfold NilpotentTargetConvolution.oddCount
      exact_mod_cast hs
    apply hsR.trans
    apply Real.one_le_rpow (by norm_num : (1 : ℝ)≤2)
    unfold PhysicalOddConvolution.coarseError
    exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
      (mul_nonneg (mul_nonneg (le_max_right β 0) (Nat.cast_nonneg n)) (Real.sqrt_nonneg _))

end SymmetricSubgroupAsymptotics.MarkedC4.OrdinarySubgroupUpper
