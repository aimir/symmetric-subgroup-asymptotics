import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotentDisplacements
import Mathlib.Tactic.LinearCombination

/-! Actual B displacements separate every upper flag coordinate.
The two quadratic tests t=1 and t=-1 replace the nonexistent root 2e_i;
their coefficient two is cancelled only in odd characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices
variable (K : Type) [Field K]

theorem unipotent_displacement_separates (h2 : (2 : K) ≠ 0) (s : ℕ)
    (i j : Index (s + 1)) (hij : flagEquiv (s + 1) i < flagEquiv (s + 1) j)
    (v : Index (s + 1) → K)
    (hz : ∀ u ∈ unipotent K (s + 1), (((u.val : Mat K (s + 1)) *ᵥ v) - v) i = 0) : v j = 0 := by
  rcases i with (i | i) | ⟨⟩
  · rcases j with (j | j) | ⟨⟩
    · have hij' : i < j := hij
      have h := hz (chainInU K (s + 1) i j hij' 1).val
        (chainInU K (s + 1) i j hij' 1).property
      change (((chainElement K (s + 1) i j (ne_of_lt hij') 1).val : Mat K (s + 1)) *ᵥ v - v)
        (pos (s + 1) i) = 0 at h
      simpa only [chain_displacement_pos, one_mul] using h
    · by_cases he : i = j
      · subst j
        have hp := hz (shortInU K s i 1).val (shortInU K s i 1).property
        have hm := hz (shortInU K s i (-1)).val (shortInU K s i (-1)).property
        change (((shortElement K s i 1).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) = 0 at hp
        change (((shortElement K s i (-1)).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) = 0 at hm
        rw [short_displacement_pos] at hp hm
        have hh : (2 : K) * v (neg (s + 1) i) = 0 := by linear_combination -hp - hm
        exact (mul_eq_zero.mp hh).resolve_left h2
      · have h := hz (skewInU K h2 s i j he 1).val (skewInU K h2 s i j he 1).property
        change (((skewElement K s i j 1).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) = 0 at h
        simpa only [skew_displacement_pos K h2 s i j he 1 v, one_mul] using h
    · have hp := hz (shortInU K s i 1).val (shortInU K s i 1).property
      have hm := hz (shortInU K s i (-1)).val (shortInU K s i (-1)).property
      change (((shortElement K s i 1).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) = 0 at hp
      change (((shortElement K s i (-1)).val : Mat K (s + 1)) *ᵥ v - v) (pos (s + 1) i) = 0 at hm
      rw [short_displacement_pos] at hp hm
      have hh : (2 : K) * v (middle (s + 1)) = 0 := by linear_combination hp - hm
      exact (mul_eq_zero.mp hh).resolve_left h2
  · rcases j with (j | j) | ⟨⟩
    · exact False.elim ((not_lt_of_gt (flag_pos_lt_neg (s + 1) j i)) hij)
    · have hji : j < i := (flag_neg_lt_neg (s + 1) i j).mp hij
      have h := hz (chainInU K (s + 1) j i hji (-1)).val
        (chainInU K (s + 1) j i hji (-1)).property
      change (((chainElement K (s + 1) j i (ne_of_lt hji) (-1)).val : Mat K (s + 1)) *ᵥ v - v)
        (neg (s + 1) i) = 0 at h
      simpa only [chain_displacement_neg, neg_neg, one_mul] using h
    · exact False.elim ((not_lt_of_gt (flag_middle_lt_neg (s + 1) i)) hij)
  · rcases j with (j | j) | ⟨⟩
    · exact False.elim ((not_lt_of_gt (flag_pos_lt_middle (s + 1) j)) hij)
    · have h := hz (shortInU K s j 1).val (shortInU K s j 1).property
      change (((shortElement K s j 1).val : Mat K (s + 1)) *ᵥ v - v) (middle (s + 1)) = 0 at h
      rw [short_displacement_middle, mul_one] at h
      exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr h2)
    · exact False.elim (lt_irrefl _ hij)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
