import SymmetricSubgroupAsymptotics.CFSGPrimeTransitiveNormalBound
import SymmetricSubgroupAsymptotics.LargePrimePermutationClassFourthBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Original prime-permutation factor bounds for ordinary tableaux.
The rank and order bounds concern every normal subgroup of the same
faithful transitive action. The exceptional ternary row is identified by
its actual degree and nontrivial actual diagonal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryFactorProfile
open CFSGPrimeTransitiveNormalBound

/-- The central-frame recurrence also gives the coarser n/p bound,
including the actual degree-p and singleton factors. -/
theorem normalGen_le_degree_div (p : ℕ) [Fact p.Prime] (k : ℕ)
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup p U)
    (hdegree : Nat.card X=p^k) (N : Subgroup U) [N.Normal] :
    MarkedC4.normalGen N≤Nat.card X/p := by
  have hp : p.Prime := Fact.out
  cases k with
  | zero =>
    have h := normalGen_le_bound p 0 U hU hdegree N
    simpa only [bound] using h.trans (Nat.zero_le _)
  | succ k =>
    cases k with
    | zero =>
      have h := normalGen_le_bound p 1 U hU hdegree N
      have hdiv : p/p=1 := Nat.div_self hp.pos
      simpa only [hdegree,Nat.zero_add,pow_one,hdiv,bound] using h
    | succ k =>
      have h := normalGen_le_twice_power p k U hU hdegree N
      have hm : 2*p^k≤p^(k+1) := by
        rw [pow_succ]
        nlinarith [Nat.mul_le_mul_right (p^k) hp.two_le]
      apply h.trans
      rw [hdegree,show k+1+1=(k+1)+1 by omega,pow_succ,
        Nat.mul_div_cancel _ hp.pos]
      exact hm

/-- Real rank density without a floor or a new uniform-rank premise. -/
theorem normalGen_real_le_degree_div (p : ℕ) [Fact p.Prime] (k : ℕ)
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup p U)
    (hdegree : Nat.card X=p^k) (N : Subgroup U) [N.Normal] :
    (MarkedC4.normalGen N : ℝ)≤(Nat.card X : ℝ)/p := by
  have hp : (0 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply (le_div_iff₀ hp).mpr
  have h := Nat.mul_le_mul_right p (normalGen_le_degree_div p k U hU hdegree N)
  have hh := h.trans (Nat.div_mul_le_self (Nat.card X) p)
  exact_mod_cast hh

/-- The full actual group order pays at most log₂(p)/(p-1) per point. -/
theorem log_order_le (p : ℕ) [Fact p.Prime]
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X)) (hU : IsPGroup p U) :
    Real.logb 2 (Nat.card U)≤(Real.logb 2 p/(p-1))*(Nat.card X : ℝ) := by
  have hcard := LargePrimePermutationClassFourthBound.pGroup_card_le p U X hU
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ)<2)
    (show (0 : ℝ)<Nat.card U by exact_mod_cast Nat.card_pos)
    (show (Nat.card U : ℝ)≤((p : ℝ)^(Nat.card X/(p-1))) by exact_mod_cast hcard)
  rw [Real.logb_pow] at hlog
  have hl : 0≤Real.logb 2 p := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
  have hp : (0 : ℝ)<p-1 := by
    have hp1 : (1 : ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    linarith
  have hfloor : ((Nat.card X/(p-1) : ℕ) : ℝ)*(p-1)≤Nat.card X := by
    have h := Nat.div_mul_le_self (Nat.card X) (p-1)
    have hcast : ((Nat.card X/(p-1) : ℕ) : ℝ)*((p-1 : ℕ) : ℝ)≤Nat.card X := by
      exact_mod_cast h
    simpa only [Nat.cast_sub (Fact.out : p.Prime).one_lt.le,Nat.cast_one] using hcast
  have hdiv : ((Nat.card X/(p-1) : ℕ) : ℝ)≤(Nat.card X : ℝ)/(p-1) :=
    (le_div_iff₀ hp).mpr hfloor
  apply hlog.trans
  have hm := mul_le_mul_of_nonneg_right hdiv hl
  convert hm using 1 <;> ring

/-- The only ternary departure from the 2n/9 bound is an active original
three-point diagonal. Its excess is exactly at most n/9. -/
theorem ternary_normalGen_real_le (k : ℕ)
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X))
    [MulAction.IsPretransitive U X] (hU : IsPGroup 3 U)
    (hdegree : Nat.card X=3^k) (N : Subgroup U) [N.Normal] :
    (MarkedC4.normalGen N : ℝ)≤(2/9 : ℝ)*Nat.card X+
      (if k=1 ∧ N≠⊥ then (1/9 : ℝ)*Nat.card X else 0) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  cases k with
  | zero =>
    have h := normalGen_le_bound 3 0 U hU hdegree N
    have hz : MarkedC4.normalGen N=0 := Nat.eq_zero_of_le_zero h
    simp only [hz,Nat.cast_zero,hdegree,pow_zero,Nat.cast_one]
    norm_num
  | succ k =>
    cases k with
    | zero =>
      by_cases hN : N=⊥
      · subst N
        simp only [MarkedC4.normalGen_bot,Nat.cast_zero,hdegree,pow_one]
        norm_num
      · have h := normalGen_le_bound 3 1 U hU hdegree N
        norm_num [hdegree,hN]
        exact h
    | succ k =>
      have h := normalGen_le_twice_power 3 k U hU hdegree N
      have hr : (MarkedC4.normalGen N : ℝ)≤2*(3 : ℝ)^k := by exact_mod_cast h
      have hn : (Nat.card X : ℝ)=9*(3 : ℝ)^k := by
        rw [hdegree]
        push_cast
        simp only [pow_succ]
        ring
      rw [if_neg (by omega : ¬(k+1+1=1 ∧ N≠⊥)),hn]
      nlinarith

/-- An active three-point diagonal has order exactly three. Therefore its
normalized density is fixed, rather than merely bounded from above. -/
theorem ternary_active_degree_three_card
    {X : Type} [Finite X] (U : Subgroup (Equiv.Perm X)) (hU : IsPGroup 3 U)
    (hdegree : Nat.card X=3) (N : Subgroup U) (hN : N≠⊥) : Nat.card N=3 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder := LargePrimePermutationClassFourthBound.pGroup_card_le 3 U X hU
  rw [hdegree] at horder
  norm_num at horder
  have hcard : Nat.card N≤3 :=
    (Nat.card_le_card_of_injective N.subtype Subtype.val_injective).trans horder
  obtain ⟨a,ha⟩ := (hU.to_subgroup N).exists_card_eq
  have hpos : 0<a := by
    by_contra h
    have ha0 : a=0 := by omega
    apply hN
    exact Subgroup.card_eq_one.mp (by simpa only [ha0,pow_zero] using ha)
  have hlow : 3≤Nat.card N := by
    rw [ha]
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0<3) hpos
  omega

end SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryFactorProfile
