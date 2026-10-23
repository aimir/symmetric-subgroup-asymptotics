import SymmetricSubgroupAsymptotics.GaronziMarotiTransitiveInduction
import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

/-! The exact published real-exponent GM target is equivalent to its
transitive case. The cube-to-real conversion is proved; the induction
does not assume a bound on arbitrary smaller groups in its final input.
This is a reduction, not a proof of the remaining transitive theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GaronziMarotiTransitiveTarget
open GaronziMarotiTransitiveInduction

theorem cube_le_iff_real_bound (a n : ℕ) (hn : 1 ≤ n) :
    a^3 ≤ 5^(n-1) ↔ (a : ℝ) ≤ (5 : ℝ)^(((n : ℝ)-1)/3) := by
  have hpow : ((5 : ℝ)^(((n : ℝ)-1)/3))^3 = (5 : ℝ)^(n-1) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 5)]
    have hexp : (((n : ℝ)-1)/3)*(3 : ℝ) = ((n-1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn, Nat.cast_one]
      exact div_mul_cancel₀ _ (by norm_num)
    simp only [Nat.cast_ofNat]
    rw [hexp, Real.rpow_natCast]
  constructor
  · intro h
    apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) _)
    rw [hpow]
    exact_mod_cast h
  · intro h
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ a by exact_mod_cast Nat.zero_le a) h 3
    rw [hpow] at hp
    exact_mod_cast hp

theorem garonziMaroti_bound_of_transitive
    (hTransitive : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      MulAction.IsPretransitive L (Fin n) →
        (Nat.card (ConjClasses L) : ℝ) ≤ (5 : ℝ)^(((n : ℝ)-1)/3)) :
    GaronziMarotiConjugacyClassBound := by
  have hcube : ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
      Nat.card (ConjClasses L)^3 ≤ 5^(n-1) := by
    apply class_cube_le_of_transitive
    intro n hn L ht
    exact (cube_le_iff_real_bound _ n (by omega)).mpr (hTransitive n hn L ht)
  intro n hn L
  exact (cube_le_iff_real_bound _ n (by omega)).mp (hcube n hn L)

theorem garonziMaroti_bound_iff_transitive :
    GaronziMarotiConjugacyClassBound ↔
      ∀ n : ℕ, 4 ≤ n → ∀ L : Subgroup (Equiv.Perm (Fin n)),
        MulAction.IsPretransitive L (Fin n) →
          (Nat.card (ConjClasses L) : ℝ) ≤ (5 : ℝ)^(((n : ℝ)-1)/3) := by
  constructor
  · intro h n hn L _ht
    exact h n hn L
  · exact garonziMaroti_bound_of_transitive

end SymmetricSubgroupAsymptotics.GaronziMarotiTransitiveTarget
