import SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryFactorProfile
import SymmetricSubgroupAsymptotics.PGroupTransitiveDegree

/-! Remove chosen prime-power exponents from the original-action profile.
Transitivity produces the prime power of the SAME actual point set. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActualDegreeProfile
open CFSGPrimeOrdinaryFactorProfile

/-- No supplied exponent or replacement permutation model is necessary. -/
theorem normalGen_real_le_div (p : ℕ) [Fact p.Prime]
    {X : Type} [Finite X] [Nonempty X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup p U)
    (N : Subgroup U) [N.Normal] :
    (MarkedC4.normalGen N : ℝ)≤(Nat.card X : ℝ)/p := by
  obtain ⟨k,hk⟩ := pGroup_transitive_degree hU (Classical.arbitrary X)
    (fun y => MulAction.exists_smul_eq U _ y)
  exact normalGen_real_le_degree_div p k U hU hk N

/-- The exceptional ternary indicator refers to the actual point degree. -/
theorem ternary_normalGen_real_le
    {X : Type} [Finite X] [Nonempty X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 3 U)
    (N : Subgroup U) [N.Normal] :
    (MarkedC4.normalGen N : ℝ)≤(2/9 : ℝ)*Nat.card X+
      (if Nat.card X=3 ∧ N≠⊥ then (1/9 : ℝ)*Nat.card X else 0) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k,hk⟩ := pGroup_transitive_degree hU (Classical.arbitrary X)
    (fun y => MulAction.exists_smul_eq U _ y)
  have heq : Nat.card X=3 ↔ k=1 := by
    rw [hk]
    have h3 : (3 : ℕ)=3^1 := by norm_num
    rw [h3]
    exact (Nat.pow_right_injective (by decide : 2≤3)).eq_iff
  simpa only [heq] using CFSGPrimeOrdinaryFactorProfile.ternary_normalGen_real_le k U hU hk N

end SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActualDegreeProfile
