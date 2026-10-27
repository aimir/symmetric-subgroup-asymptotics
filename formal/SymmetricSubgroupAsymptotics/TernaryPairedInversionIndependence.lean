import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Commute.Basic

/-! Paired inversions detect all three ternary coordinates. The maps in
this lemma are actual group homomorphisms, for example inner conjugations
by genuine derived words. No independence or cardinality is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.TernaryPairedInversionIndependence
variable {G : Type*} [Group G]

theorem third_eq_one (f : G →* G) (a b c : G)
    (hab : Commute a b) (ha : f a=a⁻¹) (hb : f b=b⁻¹) (hc : f c=c)
    (hcube : c^3=1) (hrel : a*b*c=1) : c=1 := by
  have hm := congrArg f hrel
  rw [map_mul,map_mul,ha,hb,hc,map_one] at hm
  have hp : a*b=c⁻¹ := mul_eq_one_iff_eq_inv.mp hrel
  have hi : (a*b)⁻¹*c=1 := by
    rw [mul_inv_rev,←hab.inv_inv.eq]
    exact hm
  rw [hp,inv_inv] at hi
  have hs : c^2=1 := by simpa only [pow_two] using hi
  have hlast : c^2*c=1 := by simpa only [pow_succ] using hcube
  rwa [hs,one_mul] at hlast

theorem factors_eq_one (f g : G →* G) (a b c : G)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a^3=1) (hb : b^3=1) (hc : c^3=1)
    (hfa : f a=a⁻¹) (hfb : f b=b⁻¹) (hfc : f c=c)
    (hga : g a=a⁻¹) (hgb : g b=b) (hgc : g c=c⁻¹)
    (hrel : a*b*c=1) : a=1 ∧ b=1 ∧ c=1 := by
  have hc1 := third_eq_one f a b c hab hfa hfb hfc hc hrel
  have hrel' : a*c*b=1 := by
    calc
      a*c*b = a*(c*b) := mul_assoc _ _ _
      _ = a*(b*c) := congrArg (fun z => a*z) hbc.eq.symm
      _ = a*b*c := (mul_assoc _ _ _).symm
      _ = 1 := hrel
  have hb1 := third_eq_one g a c b hac hga hgc hgb hb hrel'
  have ha1 : a=1 := by simpa only [hb1,hc1,mul_one] using hrel
  exact ⟨ha1,hb1,hc1⟩

private theorem power_cube (a : G) (ha : a^3=1) (i : ℕ) : (a^i)^3=1 := by
  calc
    (a^i)^3 = (a^3)^i := by rw [←pow_mul,←pow_mul,Nat.mul_comm i 3]
    _ = 1 := by rw [ha,one_pow]

theorem powers_eq_one (f g : G →* G) (a b c : G)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a^3=1) (hb : b^3=1) (hc : c^3=1)
    (hfa : f a=a⁻¹) (hfb : f b=b⁻¹) (hfc : f c=c)
    (hga : g a=a⁻¹) (hgb : g b=b) (hgc : g c=c⁻¹)
    (i j k : ℕ) (hrel : a^i*b^j*c^k=1) :
    a^i=1 ∧ b^j=1 ∧ c^k=1 := by
  apply factors_eq_one f g (a^i) (b^j) (c^k)
    (hab.pow_pow i j) (hac.pow_pow i k) (hbc.pow_pow j k)
    (power_cube a ha i) (power_cube b hb j) (power_cube c hc k)
  · simp only [map_pow,hfa,inv_pow]
  · simp only [map_pow,hfb,inv_pow]
  · simp only [map_pow,hfc]
  · simp only [map_pow,hga,inv_pow]
  · simp only [map_pow,hgb]
  · simp only [map_pow,hgc,inv_pow]
  · exact hrel

theorem exponents_divisible (f g : G →* G) (a b c : G)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : orderOf a=3) (hb : orderOf b=3) (hc : orderOf c=3)
    (hfa : f a=a⁻¹) (hfb : f b=b⁻¹) (hfc : f c=c)
    (hga : g a=a⁻¹) (hgb : g b=b) (hgc : g c=c⁻¹)
    (i j k : ℕ) (hrel : a^i*b^j*c^k=1) : 3∣i ∧ 3∣j ∧ 3∣k := by
  have ha3 : a^3=1 := by simpa only [ha] using pow_orderOf_eq_one a
  have hb3 : b^3=1 := by simpa only [hb] using pow_orderOf_eq_one b
  have hc3 : c^3=1 := by simpa only [hc] using pow_orderOf_eq_one c
  obtain ⟨hi,hj,hk⟩ := powers_eq_one f g a b c hab hac hbc ha3 hb3 hc3
    hfa hfb hfc hga hgb hgc i j k hrel
  exact ⟨ha ▸ orderOf_dvd_of_pow_eq_one hi,
    hb ▸ orderOf_dvd_of_pow_eq_one hj,hc ▸ orderOf_dvd_of_pow_eq_one hk⟩

end SymmetricSubgroupAsymptotics.TernaryPairedInversionIndependence
