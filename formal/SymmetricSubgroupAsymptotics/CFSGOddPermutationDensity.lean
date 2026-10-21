import SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryFactorProfile

/-! Prime-independent odd-order density bounds. These are elementary
integer exponential comparisons and statements about the SAME faithful
permutation action; no odd-order classification theorem is involved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOddPermutationDensity

private theorem square_le_three_pow {p : ℕ} (hp : 3 ≤ p) : p^2 ≤ 3^(p-1) := by
  have haux : ∀ k : ℕ,(k+3)^2 ≤ 3^(k+2) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc
        (k+1+3)^2 ≤ (k+1+3)^2+(2*k^2+10*k+11) := Nat.le_add_right _ _
        _ = 3*(k+3)^2 := by ring
        _ ≤ 3*3^(k+2) := Nat.mul_le_mul_left 3 ih
        _ = 3^(k+1+2) := by rw [show k+1+2=(k+2)+1 by omega,pow_succ];ring
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hp
  rw [hk]
  simpa only [show 3+k-1=k+2 by omega,show 3+k=k+3 by omega] using haux k

/-- sqrt(3) is an order-per-point ceiling for every odd prime group. -/
theorem prime_order_density_le {p : ℕ} (hp : 3 ≤ p) :
    Real.logb 2 p/(p-1) ≤ Real.logb 2 3/2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpow : (p : ℝ)^2 ≤ (3 : ℝ)^(p-1 : ℕ) := by exact_mod_cast square_le_three_pow hp
  have hh := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos hpR 2) hpow
  rw [Real.logb_pow,Real.logb_pow] at hh
  have hpred : (0 : ℝ) < p-1 := by
    have h : (3 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  apply (div_le_iff₀ hpred).mpr
  have hc : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one]
  rw [hc] at hh
  norm_num only [Nat.cast_ofNat] at hh
  nlinarith

/-- The order bound is transported through the original faithful image. -/
theorem pGroup_log_order_le {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup p G) :
    Real.logb 2 (Nat.card G) ≤ (Real.logb 2 3/2)*(Nat.card X : ℝ) := by
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  let e : G ≃* f.range := MonoidHom.ofInjective
    (show Function.Injective f from MulAction.toPerm_injective)
  have hh := CFSGPrimeOrdinaryFactorProfile.log_order_le p f.range (hG.of_equiv e)
  rw [←Nat.card_congr e.toEquiv] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (prime_order_density_le hp) (Nat.cast_nonneg _))

/-- A nontrivial diagonal in an odd faithful three-point action has order3.
It need not itself be transitive or normal. -/
theorem nontrivial_subgroup_degree_three_card
    {G X : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hodd : ¬2 ∣ Nat.card G)
    (hdegree : Nat.card X=3) (N : Subgroup G) (hN : N≠⊥) : Nat.card N=3 := by
  have hGdvd : Nat.card G ∣ 6 := by
    have h := (MulAction.toPermHom G X).range.card_subgroup_dvd_card
    let e := MonoidHom.ofInjective (show Function.Injective (MulAction.toPermHom G X) from
      MulAction.toPerm_injective)
    rw [←Nat.card_congr e.toEquiv,Nat.card_perm,hdegree] at h
    norm_num at h
    exact h
  have hNdvd : Nat.card N ∣ 6 := N.card_subgroup_dvd_card.trans hGdvd
  have hNodd : ¬2 ∣ Nat.card N := fun h => hodd (h.trans N.card_subgroup_dvd_card)
  have hNlarge : 1 < Nat.card N := N.one_lt_card_iff_ne_bot.mpr hN
  have hNle : Nat.card N ≤ 6 := Nat.le_of_dvd (by norm_num) hNdvd
  have hcases : Nat.card N=3 ∨ Nat.card N=5 := by omega
  rcases hcases with hc | hc
  · exact hc
  · norm_num [hc] at hNdvd

end SymmetricSubgroupAsymptotics.CFSGOddPermutationDensity
