import SymmetricSubgroupAsymptotics.FiniteModelPrimitiveOrdinaryBudget
import SymmetricSubgroupAsymptotics.FactorialLogSquaredSubquadraticCount
import SymmetricSubgroupAsymptotics.CFSGSimplePowerFullKernelBudget

/-! SAME-D elementary size bounds for a genuine faithful local action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualPrimitiveSocleLogSizeBounds
open PrimitiveSocleRawStructure
variable {R X : Type} [Group R] [Finite R] [Finite X] [MulAction R X]
    [FaithfulSMul R X] (D : NonaffineData R X)

theorem socle_power_le_factorial :
    Nat.card D.Simple^D.factorCount≤(Nat.card X).factorial := by
  have hR : Nat.card R≤(Nat.card X).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (by
      simpa only [Nat.card_perm] using Subgroup.card_dvd_of_injective
        (MulAction.toPermHom R X) MulAction.toPerm_injective)
  have hN : Nat.card (finiteGroupSocle R)≤Nat.card R :=
    Nat.card_le_card_of_injective (finiteGroupSocle R).subtype (finiteGroupSocle R).subtype_injective
  rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin] at hN
  exact hN.trans hR

theorem factorCount_le_log :
    (D.factorCount : ℝ)≤Real.logb 2 (Nat.card X : ℝ) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (pow_pos (by norm_num : (0 : ℝ)<2) D.factorCount)
    (show (2 : ℝ)^D.factorCount≤Nat.card X by
      exact_mod_cast FiniteModelPrimitiveOrdinaryBudget.two_pow_factorCount_le_degree D)
  simpa only [Real.logb_pow,Real.logb_self_eq_one (by norm_num : (1 : ℝ)<2),mul_one] using hh

theorem socle_log_le (hr : 2≤Nat.card X) :
    (D.factorCount : ℝ)*Real.logb 2 (Nat.card D.Simple : ℝ)≤
      (Nat.card X : ℝ)*Real.logb 2 (Nat.card X : ℝ) := by
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (pow_pos (by exact_mod_cast Nat.card_pos (α := D.Simple) :
      (0 : ℝ)<Nat.card D.Simple) D.factorCount)
    (show (Nat.card D.Simple : ℝ)^D.factorCount≤(Nat.card X).factorial by
      exact_mod_cast socle_power_le_factorial D)
  rw [Real.logb_pow] at hh
  exact hh.trans (FactorialLogSquaredSubquadraticCount.factorial_logb_le (Nat.card X) hr)

theorem simple_card_le_factorial : Nat.card D.Simple≤(Nat.card X).factorial := by
  obtain ⟨ell,hell⟩ := exists_leastProperIndex D.Simple
  exact (CFSGSimplePowerFullKernelBudget.simple_card_le_least_index_factorial D ell hell).trans
    (Nat.factorial_le (PrimitiveSocleLeastIndexDegreeComparison.least_index_le_degree D ell hell))

end SymmetricSubgroupAsymptotics.ActualPrimitiveSocleLogSizeBounds
