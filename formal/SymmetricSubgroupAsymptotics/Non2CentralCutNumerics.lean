import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Numerical synthesis for the retained nonbinary central cut

The annihilator cut used in section capacity has dimension
`min (t / 2) (t - ell)`.  The two permutation-section budgets control its
trivial quotient row, while the coupled socle estimate controls every
nontrivial row.  This file proves that the same cut satisfies the complete
`47/48` cost; the two rows are never optimized independently.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- Dimension of the retained central cut after row-reducing an
`ell`-dimensional extension annihilator inside a `t`-dimensional fixed
space. -/
def non2CentralCutDimension (t ell : Nat) : Nat :=
  min (t / 2) (t - ell)

theorem non2CentralCutDimension_le_half (t ell : Nat) :
    2 * non2CentralCutDimension t ell ≤ t := by
  unfold non2CentralCutDimension
  omega

theorem non2CentralCutDimension_le (t ell : Nat) :
    non2CentralCutDimension t ell ≤ t := by
  have h := non2CentralCutDimension_le_half t ell
  omega

/-- The retained annihilator makes the trivial quotient cost obey one of
the two actual permutation-section budgets.  This is the integer form of
`4t - 2c ≤ max (3t+1) (2(t+ell))`. -/
theorem non2CentralCut_trivial_cost_le
    (t ell : Nat) :
    2 * non2CentralCutDimension t ell +
        4 * (t - non2CentralCutDimension t ell) ≤
      max (3 * t + 1) (2 * (t + ell)) := by
  unfold non2CentralCutDimension
  by_cases h : t / 2 ≤ t - ell
  · rw [min_eq_left h]
    omega
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    omega

/-- Both retained permutation-section budgets imply the sharp physical
`47/48` bound for the trivial row.  The additive one in `3t+1` is absorbed
exactly by `s ≥ 24`. -/
theorem non2CentralCut_trivial_cost
    (s t ell : Nat)
    (hs : 24 ≤ s)
    (hfixed : 16 * t ≤ 5 * s)
    (hunipotent : 8 * (t + ell) ≤ 3 * s) :
    48 * (2 * non2CentralCutDimension t ell +
        4 * (t - non2CentralCutDimension t ell)) ≤
      47 * s := by
  have hrow := non2CentralCut_trivial_cost_le t ell
  by_cases h : 3 * t + 1 ≤ 2 * (t + ell)
  · rw [max_eq_right h] at hrow
    omega
  · rw [max_eq_left (Nat.le_of_not_ge h)] at hrow
    omega

/-- Full retained-annihilator capacity.  `r` is the worst nontrivial
socle row of the actual quotient by the chosen cut.  The coupled estimate
is stated on that same quotient, whose trivial row has dimension `t-c`.
Taking the maximum only after both rows have been bounded gives the desired
uniform cost. -/
theorem non2CentralCut_full_cost
    (s t ell r : Nat)
    (hs : 24 ≤ s)
    (hfixed : 16 * t ≤ 5 * s)
    (hunipotent : 8 * (t + ell) ≤ 3 * s)
    (hcoupled :
      48 * (2 * (t - non2CentralCutDimension t ell) + 4 * r) ≤
        47 * s) :
    48 * (2 * non2CentralCutDimension t ell +
        4 * max (t - non2CentralCutDimension t ell) r) ≤
      47 * s := by
  let c := non2CentralCutDimension t ell
  have hc2 : 2 * c ≤ t := non2CentralCutDimension_le_half t ell
  have htrivial : 48 * (2 * c + 4 * (t - c)) ≤ 47 * s :=
    non2CentralCut_trivial_cost s t ell hs hfixed hunipotent
  by_cases h : t - c ≤ r
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left (Nat.le_of_not_ge h)]
    exact htrivial

/-- Real-valued form used by Schur capacity.  The nontrivial socle density
need not be integral, so this is the interface consumed by the central-prefix
counting theorem. -/
theorem non2CentralCut_full_cost_real
    (s t ell : Nat) (r : ℝ)
    (hs : 24 ≤ s)
    (hfixed : 16 * t ≤ 5 * s)
    (hunipotent : 8 * (t + ell) ≤ 3 * s)
    (hcoupled :
      2 * (t - non2CentralCutDimension t ell : Nat) + 4 * r ≤
        47 * (s : ℝ) / 48) :
    2 * (non2CentralCutDimension t ell : ℝ) +
        4 * max (((t - non2CentralCutDimension t ell : Nat) : ℝ)) r ≤
      47 * (s : ℝ) / 48 := by
  let c := non2CentralCutDimension t ell
  have hct : c ≤ t := non2CentralCutDimension_le t ell
  have hc2Nat : 2 * c ≤ t := non2CentralCutDimension_le_half t ell
  have hc2 : 2 * (c : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hc2Nat
  have hsub : ((t - c : Nat) : ℝ) = (t : ℝ) - (c : ℝ) := by
    exact Nat.cast_sub hct
  have htrivialNat : 48 * (2 * c + 4 * (t - c)) ≤ 47 * s :=
    non2CentralCut_trivial_cost s t ell hs hfixed hunipotent
  have htrivialCast :
      (48 : ℝ) * (2 * (c : ℝ) + 4 * ((t - c : Nat) : ℝ)) ≤
        47 * (s : ℝ) := by
    exact_mod_cast htrivialNat
  have htrivial :
      2 * (c : ℝ) + 4 * ((t - c : Nat) : ℝ) ≤
        47 * (s : ℝ) / 48 := by
    linarith
  by_cases h : ((t - c : Nat) : ℝ) ≤ r
  · rw [max_eq_right h]
    rw [hsub] at hcoupled
    linarith
  · rw [max_eq_left (le_of_not_ge h)]
    exact htrivial

end SymmetricSubgroupAsymptotics
