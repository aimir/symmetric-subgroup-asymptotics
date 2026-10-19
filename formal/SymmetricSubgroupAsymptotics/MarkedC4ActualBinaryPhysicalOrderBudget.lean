import SymmetricSubgroupAsymptotics.MarkedC4ActualBinaryLogDensityBinding
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Perm

/-! Elementary binary permutation-order budget and its actual quotient
consequences. This uses Lagrange and Legendre, not a new literature input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryPhysicalOrderBudget

theorem original_card_le (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : IsPGroup 2 G) : Nat.card G≤2^n := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  have hd := G.card_subgroup_dvd_card
  rw [ha,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hd
  have haLe : a≤padicValNat 2 n.factorial :=
    (padicValNat_dvd_iff_le_of_ne_one (p := 2) (a := n.factorial) (n := a)
      (by decide) (Nat.factorial_ne_zero n)).mp hd
  have hv : padicValNat 2 n.factorial≤n := by
    by_cases hn : n=0
    · subst n
      norm_num
    · have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := 2) hn
      norm_num at h
      exact h.le
  rw [ha]
  exact pow_le_pow_right₀ (by norm_num : 1≤(2 : ℕ)) (haLe.trans hv)

theorem quotient_card_le {n : ℕ} (G : Subgroup (Equiv.Perm (Fin n)))
    (hG : IsPGroup 2 G) {Q : Type} [Group Q] [Finite Q]
    (q : G →* Q) (hq : Function.Surjective q) : Nat.card Q≤2^n :=
  (Nat.card_le_card_of_surjective q hq).trans (original_card_le n G hG)

theorem exponent_of_card_le {G : Type} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (k : ℕ) (hcard : Nat.card G≤2^k) : HasExp2 G k := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a,ha⟩ := hG.exists_card_eq
  have hpow : 2^a≤2^k := ha ▸ hcard
  have hk : a≤k := (Nat.pow_le_pow_iff_right (by norm_num : 1<2)).mp hpow
  have hc : 2^k=Nat.card G*2^(k-a) := by
    rw [ha,← pow_add,show a+(k-a)=k by omega]
  intro g
  rw [hc,pow_mul,pow_card_eq_one',one_pow]

theorem log_card_le {G : Type} [Group G] [Finite G]
    (k : ℕ) (hcard : Nat.card G≤2^k) : Real.logb 2 (Nat.card G)≤(k : ℝ) := by
  apply (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2)
    (show (0 : ℝ)<Nat.card G by exact_mod_cast Nat.card_pos)).mpr
  rw [Real.rpow_natCast]
  exact_mod_cast hcard

end SymmetricSubgroupAsymptotics.MarkedC4.ActualBinaryPhysicalOrderBudget
