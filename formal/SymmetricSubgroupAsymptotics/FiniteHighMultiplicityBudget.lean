import SymmetricSubgroupAsymptotics.AbelianSectionOmegaArithmetic
import Mathlib.Data.Nat.Sqrt

/-! A single multiplicity split pays all high simple rows from the exact
prime-factor budget, without an independent worst-case count per row. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize

theorem highMultiplicity_weighted_budget {I : Type} [Fintype I]
    (c d : I → ℕ) (t : ℕ) (hc : ∀ i, 2 ≤ c i) :
    (t+1) * (Finset.univ.filter (fun i => t < d i)).card ≤
      ∑ i, d i * omega (c i) := by
  let H := Finset.univ.filter (fun i => t < d i)
  calc
    (t+1)*H.card = ∑ _i ∈ H, (t+1) := by simp [mul_comm]
    _ ≤ ∑ i ∈ H, d i * omega (c i) := by
      apply Finset.sum_le_sum
      intro i hi
      have hd : t+1 ≤ d i := by
        have := (Finset.mem_filter.mp hi).2
        omega
      have ho : 1 ≤ omega (c i) :=
        (omega_pos_iff_one_lt.mpr (by have := hc i; omega))
      nlinarith
    _ ≤ ∑ i, d i * omega (c i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)

/-- At the square-root cutoff, the same total budget bounds the number
of high rows. No independent bound on each multiplicity is used. -/
theorem highMultiplicity_card_le_sqrt {I : Type} [Fintype I]
    (c d : I → ℕ) (M : ℕ) (hc : ∀ i, 2 ≤ c i)
    (hbudget : (∑ i, d i * omega (c i)) ≤ M) :
    (Finset.univ.filter (fun i => M.sqrt < d i)).card ≤ M.sqrt := by
  have hb := (highMultiplicity_weighted_budget c d M.sqrt hc).trans hbudget
  have hsq := Nat.lt_succ_sqrt M
  by_contra hn
  have hc' : M.sqrt+1 ≤ (Finset.univ.filter (fun i => M.sqrt < d i)).card := by omega
  nlinarith

end SymmetricSubgroupAsymptotics.MarkedC4.AbelianSectionSize
